{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Redundant $" #-}

module Chronolog.Unification (
  unifyAtom,
  Ctx (..), runUnificationT,
  Env (..), emptyEnv, normEnv,
  Error
) where

import Control.Monad (when, zipWithM, ap, liftM)
import Control.Monad.Cont (Cont, cont, runCont)
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.State (MonadState, gets, get, put)
import Chronolog.Grammar hiding (normHeadAliasesInExpr)
import Data.Function ((&))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint (hang, (<+>))
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))
import Utility (bullets, fixpointEqM)

--------------------------------------------------------------------------------
-- Unification monad
--------------------------------------------------------------------------------

-- Reads a global Ctx, throws Error exceptions, uses Env as state, and produces Common.T m actions
type UnificationT c v = UniMonad (Ctx c v) (Env c v)

{-# INLINE runUnificationT #-}
runUnificationT :: Env c v -> Ctx c v -> UnificationT c v b -> (Maybe b, Env c v)
runUnificationT env ctx m = runCont (runUniMonad m) (\b _ s -> (Just b, s)) ctx env

-- CPS version of: ReaderT r (ExceptT () (StateT s m))
-- Using CPS gives a ~50% performance improvement
-- See wiki.haskell.org/Performance/Monads#Use_Continuation_Passing_Style for more details
newtype UniMonad r s a = UniMonad {
  runUniMonad :: forall res. Cont (r -> s -> (Maybe res, s)) a
}

instance Functor (UniMonad r s) where
  fmap = liftM

instance Applicative (UniMonad r s) where
  pure x = UniMonad (return x)
  {-# INLINE pure #-}
  (<*>)  = ap

instance Monad (UniMonad r s) where
  return = pure
  (>>=)  = bindUniMonad
  {-# INLINE (>>=) #-}

-- We use the the variable k for the continuation

instance forall r s. MonadReader r (UniMonad r s) where
  ask       = UniMonad (cont $ \k r -> k r r)
  local f m = UniMonad (cont $ \k r -> runCont (runUniMonad m) k (f r))

instance forall r s. MonadState s (UniMonad r s) where
  get    = UniMonad (cont $ \k r s -> k s r s)
  put s' = UniMonad (cont $ \k r _ -> k () r s')

instance forall r s. MonadError () (UniMonad r s) where
  -- Throw away the continuation and return error
  throwError () = UniMonad (cont $ \_ _ s -> (Nothing, s))
  catchError action handler =
    UniMonad (cont $
      \k r s -> do 
                  let (x', s') = runCont (runUniMonad action) (\a _ s'' -> (Just a, s'')) r s
                  case x' of
                    Nothing -> runCont (runUniMonad (handler ())) k r s'
                    Just a -> k a r s'
    )

throwNothing :: UniMonad r s x
throwNothing = throwError ()

{-# INLINE bindUniMonad #-}
bindUniMonad :: UniMonad r s a -> (a -> UniMonad r s b) -> UniMonad r s b
bindUniMonad m f = UniMonad $ runUniMonad m >>= (\a -> runUniMonad (f a))


--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------


newtype Ctx c v = Ctx { exprAliases :: [ExprAlias c v] }

newtype Env c v = Env { sigma :: Subst c v }
  deriving (Show, Eq)

instance (Pretty c, Pretty v) => Pretty (Env c v) where
  pPrint Env {..} =
    hang "Unification.Env" 2 . bullets $
      [ "sigma =" <+> pPrint sigma
      ]

emptyEnv :: Env c v
emptyEnv =
  Env
    { sigma = emptySubst
    }

data Error a c v
  = AtomsError (Atom a c v) (Atom a c v)
  | ExprsError (Expr c v) (Expr c v)
  | OccursError (Var v) (Expr c v)
  deriving (Show, Eq)

instance (Pretty a, Pretty c, Pretty v) => Pretty (Error a c v) where
  pPrint (AtomsError a1 a2) = pPrint a1 <+> "!~" <+> pPrint a2
  pPrint (ExprsError e1 e2) = pPrint e1 <+> "!~" <+> pPrint e2
  pPrint (OccursError x e) = pPrint x <+> "was unified with" <+> pPrint e <+> "recursively"

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

unifyAtom :: (Eq a, Ord v, Eq c, Pretty v, Pretty c) => Atom a c v -> Atom a c v -> UnificationT c v (Atom a c v)
unifyAtom (Atom c1 es1) (Atom c2 es2) = do
  when (c1 /= c2) do throwNothing
  when ((es1 & length) /= (es2 & length)) do throwNothing
  let n = c1
  es <- zipWithM unifyExpr es1 es2
  -- TODO: is this really necessary? seems like it might be...
  es' <- traverse normExpr es
  pure $ Atom n es'

unifyExpr :: (Ord v, Eq c, Pretty v, Pretty c) => Expr c v -> Expr c v -> UnificationT c v (Expr c v)
unifyExpr e1 e2 = do
  e1' <- normExpr e1
  e2' <- normExpr e2
  unifyExpr' e1' e2'

unifyExpr' :: (Ord v, Eq c, Pretty v, Pretty c) => Expr c v -> Expr c v -> UnificationT c v (Expr c v)
unifyExpr' e1 e2 | e1 == e2 = return e2
unifyExpr' (VarExpr x1) e2 = do
  setVarM x1 e2
  return e2
unifyExpr' e1 (VarExpr x2) = do
  setVarM x2 e1
  return e1
unifyExpr' e1@(ConExpr (Con _ _)) e2@(ConExpr (Con _ _)) = do
  ctx <- ask
  let e1' = normHeadAliasesInExpr ctx.exprAliases e1
  let e2' = normHeadAliasesInExpr ctx.exprAliases e2
  case (e1', e2') of
    (VarExpr x1, _) -> do
      setVarM x1 e2'
      return e2'
    (_, VarExpr x2) -> do
      setVarM x2 e1'
      return e1'
    (c1 :% es1, c2 :% es2) | c1 == c2 -> do
      when ((es1 & length) /= (es2 & length)) do throwNothing
      let c = c1 -- = c2
      es <- zipWithM unifyExpr es1 es2
      pure $ c :% es
    _ -> throwNothing

normExpr :: Ord v => Expr c v -> UnificationT c v (Expr c v)
normExpr = liftA2 substExpr (gets sigma) . return

-- Repeatedly applies substitution to itself until it stabilizes
-- When we rely on this, it is a major bottleneck.
normEnv :: (Eq c, Ord v) => UnificationT c v ()
normEnv = do
  sigma' <-
    gets sigma
      >>= fixpointEqM
        ( \s ->
            s
              & unSubst
              & Map.traverseWithKey
                ( \x e ->
                    if x `Set.member` varsExpr e
                      then throwNothing
                      else return $ substExpr s e
                )
              & fmap Subst
        )
  put $ Env sigma'

{-# SCC setVarM #-}
setVarM :: (Ord v, Eq c, Pretty v, Pretty c) => Var v -> Expr c v -> UnificationT c v ()
setVarM x e = do
  -- if 'x' occurs in 'e', then is a cyclic substitution, which is inconsistent
  when (Set.member x (varsExpr e)) do throwNothing
  e' <-
    gets (substVar . sigma) <*> return x >>= \case
      Nothing -> return e
      -- if 'x' is already substituted, then must unify the old substitute 'e'
      -- with the new substitute 'e''
      Just e' -> do
        unifyExpr e e'
  sigma' <- gets sigma
  put $ Env (setVar x e' sigma')


normHeadAliasesInExpr :: (Pretty c, Pretty v) => [ExprAlias c v] -> Expr c v -> Expr c v
normHeadAliasesInExpr exprAliases e = do
  case exprAliases `applyExprAlias` e of
    Nothing -> e
    Just e' -> normHeadAliasesInExpr exprAliases e'

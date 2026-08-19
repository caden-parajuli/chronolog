{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Redundant $" #-}

module Chronolog.Unification (Ctx (..), runUnificationT, emptyEnv, normEnv, unifyAtom, sigma) where

import Control.Lens (makeLenses, (%=), (.=), (^.))
import Control.Monad (when, zipWithM, ap, liftM)
import Control.Monad.Cont (Cont, cont, runCont)
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Monad.Reader (MonadReader, ask, local)
import Control.Monad.State (MonadState, gets, get, put)
import Control.Monad.Writer (MonadWriter, tell, listen, pass)
import qualified Chronolog.Common as Common
import qualified Chronolog.Common.Msg as Msg
import Chronolog.Grammar
import Data.Function ((&))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint (hang, (<+>))
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))
import Utility (bullets, fixpointEqM, (=<<$>))
import Debug.Trace (trace, traceShow)

--------------------------------------------------------------------------------
-- Unification monad
--------------------------------------------------------------------------------

-- Holds a global Ctx, throws Error exceptions, uses Env as state, and produces Common.T m actions
type UnificationT a c v m = UniMonad (Ctx c v) (Error a c v) (Env c v) (Common.T m)

{-# INLINE runUnificationT #-}
runUnificationT :: Monad m => Env c v -> Ctx c v -> UnificationT a c v m b -> Common.T m (Either (Error a c v) b, Env c v)
runUnificationT env ctx m = runCont (runUniMonad m) (\b _ s -> return (Right b, s)) ctx env

-- CPS version of: ReaderT r (ExceptT e (StateT s m))
newtype UniMonad r e s m a = UniMonad {
  runUniMonad :: forall res. Cont (r -> s -> m (Either e res, s)) a
}

instance (Monad m) => Functor (UniMonad r e s m) where
  fmap = liftM

instance (Monad m) => Applicative (UniMonad r e s m) where
  pure x = UniMonad (return x)
  (<*>)  = ap

instance (Monad m) => Monad (UniMonad r e s m) where
  return = pure
  (>>=)  = bindUniMonad

instance forall r e s m. (Monad m) => MonadReader r (UniMonad r e s m) where
  ask = UniMonad (cont $ \k r s -> k r r s)
  local f m = UniMonad (cont $ \k r s -> runCont (runUniMonad m) k (f r) s)

instance forall r e s m. (Monad m) => MonadState s (UniMonad r e s m) where
  get    = UniMonad (cont $ \k r s -> k s r s)
  put s' = UniMonad (cont $ \k r _ -> k () r s')

instance forall r e s m. (Monad m) => MonadError e (UniMonad r e s m) where
  -- Throw away the continuation
  throwError e = UniMonad (cont $ \_ _ s -> return (Left e, s))
  catchError action handler =
    UniMonad (cont $
      \k r s -> do 
                  (x', s') <- runCont (runUniMonad action) (\a _ s'' -> return (Right a, s'')) r s
                  case x' of
                    Left e -> runCont (runUniMonad (handler e)) k r s'
                    Right a -> k a r s'
    )

instance (MonadWriter w m) => MonadWriter w (UniMonad r e s m) where
  tell w = UniMonad (cont $ \k r s -> (tell w) >> k () r s)
  listen m = do
    a <- UniMonad $ runUniMonad m
    UniMonad $ cont \k r s -> do
                                x <- listen $ return a
                                k x r s
  pass m = do
    a <- UniMonad $ runUniMonad m
    UniMonad $ cont \k r s -> do
                                x <- pass $ return a
                                k x r s

{-# INLINE bindUniMonad #-}
bindUniMonad :: UniMonad r e s m a -> (a -> UniMonad r e s m b) -> UniMonad r e s m b
bindUniMonad m f = UniMonad $ runUniMonad m >>= (\a -> runUniMonad (f a))


--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------


data Ctx c v = Ctx
  { exprAliases :: [ExprAlias c v],
    doLogging :: !Bool
  }

data Env c v = Env
  { _sigma :: Subst c v
  }
  deriving (Show, Eq)

instance (Pretty c, Pretty v) => Pretty (Env c v) where
  pPrint Env {..} =
    hang "Unification.Env" 2 . bullets $
      [ "sigma =" <+> pPrint _sigma
      ]

emptyEnv :: Env c v
emptyEnv =
  Env
    { _sigma = emptySubst
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

makeLenses ''Ctx
makeLenses ''Env

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

unifyAtom :: (Monad m, Eq a, Ord v, Eq c, Pretty v, Pretty c) => Atom a c v -> Atom a c v -> UnificationT a c v m (Atom a c v)
unifyAtom a1@(Atom c1 es1) a2@(Atom c2 es2) = do
  when (c1 /= c2) do throwError $ AtomsError a1 a2
  when ((es1 & length) /= (es2 & length)) do throwError $ AtomsError a1 a2
  let n = c1
  es <- zipWithM unifyExpr es1 es2
  -- TODO: is this really necessary? seems like it might be...
  es' <- normExpr =<<$> es
  pure $ Atom n es'

unifyExpr :: (Monad m, Ord v, Eq c, Pretty v, Pretty c) => Expr c v -> Expr c v -> UnificationT a c v m (Expr c v)
unifyExpr e1 e2 = do
  e1' <- normExpr e1
  e2' <- normExpr e2
  ctx <- ask
  when (ctx.doLogging)
    $ tell
       [ (Msg.mk 5 "unifyExpr")
           { Msg.contents =
               [ "e1 =" <+> pPrint e1',
                 "e2 =" <+> pPrint e2'
               ]
           }
       ]
  unifyExpr' e1' e2'

unifyExpr' :: (Monad m, Ord v, Eq c, Pretty v, Pretty c) => Expr c v -> Expr c v -> UnificationT a c v m (Expr c v)
unifyExpr' e1 e2 | e1 == e2 = return e2
unifyExpr' (VarExpr x1) e2 = do
  setVarM x1 e2
  return e2
unifyExpr' e1 (VarExpr x2) = do
  setVarM x2 e1
  return e1
unifyExpr' e1@(ConExpr (Con _ _)) e2@(ConExpr (Con _ _)) = do
  ctx <- ask
  e1' <- normHeadAliasesInExpr ctx.exprAliases ctx.doLogging e1
  e2' <- normHeadAliasesInExpr ctx.exprAliases ctx.doLogging e2
  case (e1', e2') of
    (VarExpr x1, _) -> do
      setVarM x1 e2'
      return e2'
    (_, VarExpr x2) -> do
      setVarM x2 e1'
      return e1'
    (c1 :% es1, c2 :% es2) | c1 == c2 -> do
      when ((es1 & length) /= (es2 & length)) do throwError $ ExprsError e1' e2'
      let c = c1 -- = c2
      es <- zipWithM unifyExpr es1 es2
      pure $ c :% es
    _ -> throwError $ ExprsError e1' e2'

normExpr :: (Monad m, Ord v) => Expr c v -> UnificationT a c v m (Expr c v)
normExpr = liftA2 substExpr (gets (^. sigma)) . return

normEnv :: (Monad m, Eq c, Ord v) => UnificationT a c v m ()
normEnv = do
  sigma' <-
    gets (^. sigma)
      >>= fixpointEqM
        ( \s ->
            s
              & unSubst
              & Map.traverseWithKey
                ( \x e ->
                    if x `Set.member` varsExpr e
                      then throwError $ OccursError x e
                      else return $ substExpr s e
                )
              & fmap Subst
        )
  sigma .= sigma'

setVarM :: (Monad m, Ord v, Eq c, Pretty v, Pretty c) => Var v -> Expr c v -> UnificationT a c v m ()
setVarM x e = do
  ctx <- ask
  when (ctx.doLogging)
    $ tell [Msg.mk 4 $ "setVarM" <+> pPrint x <+> pPrint e]
  -- if 'x' occurs in 'e', then is a cyclic substitution, which is inconsistent
  when (Set.member x (varsExpr e)) do throwError $ ExprsError (VarExpr x) e
  e' <-
    gets (substVar . (^. sigma)) <*> return x >>= \case
      Nothing -> return e
      -- if 'x' is already substituted, then must unify the old substitute 'e'
      -- with the new substitute 'e''
      Just e' -> do
        when (ctx.doLogging)
          $ tell [Msg.mk 4 $ "[setVarM]" <+> pPrint x <+> "was already substituted, so must check: " <+> pPrint e <+> "~" <+> pPrint e']
        unifyExpr e e'
  sigma %= setVar x e'

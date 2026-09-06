module Chronolog.Engine
  ( Config (..), defaultConfig, runConfig,
    Node (..), mkNode, runNode, substNode,
    Gas (..), decrementGas,
    EngineState (..),
    liftFreshening,
  )
where

import qualified Chronolog.Freshening as Freshening
import Chronolog.Grammar
import Chronolog.Indexing (filterPathIndexing)
import qualified Chronolog.Indexing as Indexing
import qualified Chronolog.Unification as Unification
import Control.Monad.State (State, put, get, modify, runState, execState)
import Data.Function ((&))
import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import qualified Data.List as List
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint), hang, text, (<+>))
import Utility
import Prelude hiding (init)
import Data.Either (partitionEithers)

{- We model the engine state as consisting of a set of "nodes" each of which
   constists principally of a substitution and a set of goals. To begin execution,
   each query is turned into a node, and the main engine loop is executed.
   
   The engine executes by selecting one of its nodes `b_0`, and mapping that node
   to a new set of nodes `b_1 ... b_n`, which replace `b_0` in the engine state.
   This new set of nodes can be empty (for solved or failed goals), a single node,
   or multiple different nodes. This process continues until there are no remaining
   nodes.
   
   More concretely:
   1. The engine pops a node off of its node list
   2. It selects the first active goal from that node (if there is none, the node is marked solved).
   3. It finds all rules that unify with that goal.
   4. For each such rule, a new node is created where the selected goal is replaced by the body of the rule.
   5. The node's substitution is the old node's, composed with the unifier from step 3.
   6. These nodes are pushed back into the engine state, in place of the old node.
   7. Repeat from step 1, until there are no more unsolved nodes.
-}


--------------------------------------------------------------------------------
-- types
--------------------------------------------------------------------------------

data Config a c v = Config
  { rules :: [Rule a c v]
  , goals :: [Goal a c v]
  , shouldSuspend :: Goal a c v -> Bool
  , exprAliases :: [ExprAlias c v]
  , initialGas :: !Gas
  -- , strategy :: Strategy
  -- , doLogging :: !Bool
  }

defaultConfig :: Config a c v
defaultConfig =
  Config
    { rules = []
    , goals = []
    , shouldSuspend = const False
    , exprAliases = []
    , initialGas = InfiniteGas
    }

-- Per-node environment
data Node a c v = Node
  { activeGoals :: [Goal a c v]
  , suspendedGoals :: [Goal a c v]
  , failedGoals :: [Goal a c v]
  , sigma :: Subst c v
  , freshCounter_vars :: !Int
  , freshCounter_goals :: !Int
  }
  deriving Show

instance (Pretty a, Pretty c, Pretty v) => Pretty (Node a c v) where
  pPrint node =
    hang (text "engine node:") 2 . bullets $
      [ text "activeGoals =" <+> pPrint node.activeGoals,
        text "suspendedGoals =" <+> pPrint node.suspendedGoals,
        text "failedGoals =" <+> pPrint node.failedGoals,
        text "sigma =" <+> pPrint node.sigma
      ]

mkNode :: Config a c v -> Node a c v
mkNode cfg =
  Node
    { activeGoals = cfg.goals
    , suspendedGoals = mempty
    , failedGoals = mempty
    , freshCounter_vars = 0
    , freshCounter_goals = (cfg.goals & fmap (fromMaybe (-1) . goalIndex) & maximum) + 1
    , sigma = emptySubst
    }


substNode :: (Ord v) => Subst c v -> Node a c v -> Node a c v
substNode sigma' node =
  node
    { activeGoals = substGoal sigma' <$> node.activeGoals
    , suspendedGoals = substGoal sigma' <$> node.suspendedGoals
    , sigma = composeSubst_unsafe sigma' node.sigma
    }

-- Global engine state
data EngineState a c v = EngineState
  { nodes :: [Node a c v]
  , solvedNodes :: [Node a c v]
  , failedNodes :: [Node a c v]
  , gas :: {-# UNPACK #-} !Gas
  -- Read-only portion:
  , rules :: [Rule a c v]
  , pathIndex :: Indexing.Trie a c v
  , exprAliases :: [ExprAlias c v]
  , shouldSuspend :: Goal a c v -> Bool
  }

mkEngineState :: (Ord a, Ord c) => Config a c v -> Node a c v -> EngineState a c v
mkEngineState cfg rootNode =
  EngineState
    { nodes = [rootNode]
    , solvedNodes = []
    , failedNodes = []
    , gas = cfg.initialGas
    , rules = cfg.rules
    , pathIndex = Indexing.buildIndex cfg.exprAliases cfg.rules
    , exprAliases = cfg.exprAliases
    , shouldSuspend = cfg.shouldSuspend
    }

data Gas
  = FiniteGas !Int
  | InfiniteGas
  deriving (Eq, Show)

instance Pretty Gas where
  pPrint (FiniteGas n) = pPrint n
  pPrint InfiniteGas = text "∞"

isDepletedGas :: Gas -> Bool
isDepletedGas (FiniteGas n) = n <= 0
isDepletedGas InfiniteGas = False
{-# INLINE isDepletedGas #-}

decrementGas :: Gas -> Gas
decrementGas (FiniteGas n) = FiniteGas (n - 1)
decrementGas InfiniteGas = InfiniteGas
{-# INLINE decrementGas #-}

--------------------------------------------------------------------------------
-- functions
--------------------------------------------------------------------------------

runConfig :: (Ord a, Ord c, Ord v, Pretty a, Pretty c, Pretty v) => Config a c v -> [Node a c v]
runConfig cfg = runNode cfg (mkNode cfg)

runNode :: (Ord a, Ord c, Ord v, Pretty a, Pretty c, Pretty v) => Config a c v -> Node a c v -> [Node a c v]
runNode cfg rootNode = solvedNodes $ execState loop (mkEngineState cfg rootNode)

-- Returns True if successful. Returns False if it runs out of gas.
loop :: (Ord a, Ord c, Ord v, Pretty a, Pretty c, Pretty v) => State (EngineState a c v) Bool
loop = do
  mNode <- pop
  case mNode of
    Just node -> do
      -- If we wanted BFS we could just do concatMapM instead of pop and prepend
      newNodes <- tryFirstGoal node
      prepend newNodes

      state <- get

      -- Loop if we have gas
      if isDepletedGas state.gas
      then return False
      else do
        put state{ gas = decrementGas state.gas }
        loop
    -- No nodes left. We are done.
    Nothing -> return True

-- Tries all rules on the given Node, returning the new Nodes this produces.
-- Each successful rule produces a new Node where the tried goal is replaced
-- with the rule's hypotheses.
tryFirstGoal :: (Ord a, Ord c, Ord v, Pretty c, Pretty v) => Node a c v -> State (EngineState a c v) [Node a c v]
tryFirstGoal node =
  -- Get first active goal, if any
  case node.activeGoals of
    [] -> do
      -- No active goals. This node is solved.
      state <- get
      put state{ solvedNodes = node : state.solvedNodes }
      return []
    (goal : otherGoals) -> do
      state <- get
      -- Check global suspend predicate
      if state.shouldSuspend $ normAliasesInGoal state.exprAliases goal
      then return [node{ activeGoals = otherGoals, suspendedGoals = goal : node.suspendedGoals }]
      else do
        let applicableRules = getRules node goal state
            -- Try unifying with the rules to obtain new nodes
            newNodes =
              flip mapMaybe applicableRules \(rule, node') ->
                case tryRule state.exprAliases node'.sigma goal rule of
                  Nothing -> Nothing
                  Just (subst, hyps') ->
                    Just $ fromMaybe (node' {
                                        sigma = composeSubst_unsafe subst node'.sigma,
                                        activeGoals = hyps' ++ (substGoal subst <$> otherGoals)
                                     })
                                     (tryRuleSuspend node rule)
        -- If newNodes is empty, the goal failed
        case newNodes of
          [] -> do
                  state' <- get
                  put state'{ failedNodes = node{failedGoals = goal : node.failedGoals} : state'.failedNodes }
                  return []
          [_] -> return $ map processSuspended newNodes
          _ -> return $ map processSuspended newNodes

-- Applies the substitution to suspended goals, and resumes any that were updated.
processSuspended :: (Eq a, Eq c, Ord v) => Node a c v -> Node a c v
processSuspended node =
  let suspendedGoals_old = node.suspendedGoals
      suspendedGoals_substed = substGoal node.sigma <$> suspendedGoals_old
      (toResume, suspendedGoals_new) =
        partitionEithers $
          zipWith
            (\suspendedGoal_old suspendedGoal_substed ->
                -- todo: We should be able to return directly whether a substitution affected a goal
                -- That should be more efficient since then we don't need to keep the old goals in
                -- memory and check equality
                if suspendedGoal_old == suspendedGoal_substed
                then Right suspendedGoal_substed
                else Left suspendedGoal_substed)
            suspendedGoals_old
            suspendedGoals_substed
   in node{ activeGoals = toResume ++ node.activeGoals, suspendedGoals = suspendedGoals_new }


-- Tries to suspend the first goal of the node based on the rule's suspend option
-- Returns Nothing if the suspend predicate does not apply
tryRuleSuspend :: Node a c v -> Rule a c v -> Maybe (Node a c v)
tryRuleSuspend (Node [] _ _ _ _ _) _rule = Nothing
tryRuleSuspend beforeUni@(Node (goal : otherGoals) _ _ _ _ _) rule =
   case rule.ruleOpts.suspendRuleOpt of
     Just f | f goal -> Just $
       beforeUni{ activeGoals = otherGoals
                , suspendedGoals =
                    -- todo: wouldn't it be more efficient to put it at the start? Does that change anything?
                    beforeUni.suspendedGoals
                    ++ [ goal
                           { goalOpts =
                               goal.goalOpts
                                 { constrainedRulesetGoalOpt = Just (Set.fromList [rule.name])
                                 , requiredGoalOpt = True
                                 }
                           }
                       ]
                }
     _ -> Nothing

-- Get and freshen applicable (as determined by path indexing) rules
getRules ::
  (Ord a, Ord c, Ord v) =>
  Node a c v -> Goal a c v -> EngineState a c v -> [(Rule a c v, Node a c v)]
getRules node goal state =
  map
    (goSubst . flip runState node . liftFreshening . Freshening.freshenRule)
    $ filterConstrainedRuleset goal $ filterPathIndexing state.exprAliases goal state.pathIndex

  where goSubst :: Ord v => (Rule a c v, Node a c v) -> (Rule a c v, Node a c v)
        goSubst (rule, node') = (substRule node'.sigma rule, node')

        filterConstrainedRuleset :: Goal a c v -> [Rule a c v] -> [Rule a c v]
        filterConstrainedRuleset goal' =
          case goal'.goalOpts.constrainedRulesetGoalOpt of
            Nothing -> id
            Just ruleNames -> List.filter \rule -> rule.name `Set.member` ruleNames


tryRule ::
  (Eq a, Ord v, Eq c, Pretty v, Pretty c) =>
  [ExprAlias c v] -> Subst c v -> Goal a c v -> Rule a c v -> Maybe (Subst c v, [Goal a c v])
tryRule aliases subst goal rule =
  case unifyAtoms aliases subst goal.atom rule.conc of
    Nothing -> Nothing
    Just (_, subst') -> Just (subst', map (substGoal subst' . unGoalHyp) rule.hyps)

-- Gets a node, if there are any. This is the "nondeterministic choice"
-- although the implementation just takes the first node, resulting in
-- depth-first search
pop :: State (EngineState a c v) (Maybe (Node a c v))
pop = do
  state <- get
  put state{ nodes = drop 1 state.nodes }
  return (listToMaybe state.nodes)

-- Prepend some active nodes to the engine state
-- This (along with pop) enforces depth-first search.
-- For breadth-first we could just append to the end of the list
-- here (or better yet we concatMap over the whole list instead of pop/prepend)
prepend :: [Node a c v] -> State (EngineState a c v) ()
prepend nodes' = do
  state <- get
  put state{ nodes = nodes' ++ state.nodes }
  return ()

liftFreshening :: Freshening.M c v x -> State (Node a c v) x
liftFreshening freshenState = do
  env_freshening <- do
    env <- get
    return
      Freshening.Env
        { sigma = emptySubst,
          freshCounter_vars = env.freshCounter_vars,
          freshCounter_goals = env.freshCounter_goals,
          existentialVars = Set.empty
        }
  let (x, env_freshening') = runState freshenState env_freshening
  modify \state ->
    state { freshCounter_vars = env_freshening'.freshCounter_vars
          , freshCounter_goals = env_freshening'.freshCounter_goals
          }
  return x

unifyAtoms :: (Eq a, Ord v, Eq c, Pretty v, Pretty c) => [ExprAlias c v] -> Subst c v -> Atom a c v -> Atom a c v -> Maybe (Atom a c v, Subst c v)
unifyAtoms aliases subst atom1 atom2 =
    case ran of
      (Nothing, _) -> Nothing
      (Just atom', Unification.Env subst') -> Just (atom', subst')
  where ran = Unification.runUnificationT (Unification.Env subst) (Unification.Ctx aliases) do
                atom' <- Unification.unifyAtom atom1 atom2
                -- See setVar for why this is necessary
                Unification.normEnv
                return atom'

-- todo: define normReduceEnv which not only norms a Subst,
-- but also takes a Node and prunes all of the unnecessary mappings
-- from the Subst that are unreachable from the Node.
--
-- e.g. if the Node only has variables `x` and `y` in its goals, and
-- the Subst is:
--
-- { x |-> z, y |-> t1, z |-> t2, w |-> t3 }
-- 
-- then `w |-> t3` should be removed from the Subst.
--
-- Substitutions can get to over 1000 mappings in DCS, and this is
-- a major bottleneck.
--
-- It should be sufficient to just do the regular normEnv, then only
-- keep mappings from variables directly in the Node. This should work since
-- normEnv ensures that no variables in the body of the mappings
-- are mapped elsewhere in the substitution. So the only variables
-- in the Subst that are reachable from the Node are the ones
-- that are directly in the Node.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Module      : Control.Hspl.Internal.Logic
Description : A backtracking, stateful monad.
Stability   : Internal

This module defines a monad implementing nondeterministic, backtracking control flow. It is heavily
based on the paper /Backtracking, Interleaving, and Terminating Monad Transformers/, by Oleg
Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry
(<http://www.cs.rutgers.edu/~ccshan/logicprog/LogicT-icfp2005.pdf>), as well as the associated
package "Control.Monad.Logic".

Our implementation builds on those works by adding control over backtracking via a Prolog-like 'cut'
operation. It also adds backtracking state (effects performed in one branch of the computation are
not visible in a parallel branch).

We provide several mtl-style classes encapsulating the various behaviors, as well as concrete types
implementing those classes.
-}

module Control.Hspl.Internal.Logic (
    module Control.Monad
  , module Control.Monad.Trans
  , module Control.Monad.Logic.Class
  , module Control.Monad.State.Class
  -- * Finer control over backtracking via 'cut'
  -- ** The cut class
  , MonadLogicCut (..)
  -- ** The cut monad transformer
  , CutT (..)
  , SuccessCont
  , LogicCont
  , runAllCutT
  , execAllCutT
  , observeAllCutT
  , runManyCutT
  , execManyCutT
  , observeManyCutT
  -- * Backtrackable state
  -- ** The state class
  , SplittableState (..)
  , LogicState (..)
  , Global (..)
  , Backtracking (..)
  -- ** The state monad transformer
  , LTBS (..)
  , LTGS (..)
  , LogicT
  , runAllLogicT
  , execAllLogicT
  , observeAllLogicT
  , runManyLogicT
  , execManyLogicT
  , observeManyLogicT
  -- ** The state monad
  , Logic
  , runAllLogic
  , execAllLogic
  , observeAllLogic
  , runManyLogic
  , execManyLogic
  , observeManyLogic
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Logic.Class
import Control.Monad.State
import Control.Monad.State.Class
import Control.Monad.Trans

-- | Class of logic monads which allow control of backtracking via cut. We use a stack-based model
-- for even finer control. The cut stack can be thought of as a sequence of checkpoints. At any
-- time, a computation can be executed in a new cut frame, which pushes a new checkpoint onto the
-- stack. If the computation calls 'cut' or 'commit', all unexplored choice points created since the
-- most recent checkpoint will be discarded. Choice points created /before/ that checkpoint are
-- kept. When the computation finishes, that checkpoint is popped off of the stack.
--
-- The functions defined in this class should relate to each other as follows:
--
-- prop> cut = commit ()
--
-- or, equivalently
--
-- prop> commit a = cut >> return 'a'
--
-- The relationship to the 'MonadLogic' class is defined by the following semantics:
--
-- prop> (m1 >>= commit) <|> m2 = once m1
--
-- prop> cutFrame m1 <|> m2 = m1 <|> m2
class MonadLogic m => MonadLogicCut m where
  -- | Commit to the current branch of backtracking, discarding unexplored choice points created in
  -- the current cut frame.
  cut :: m ()
  cut = commit ()

  -- | Commit to a given result, discarding unexplored choicepoints created in the current cut
  -- frame.
  commit :: a -> m a
  commit a = cut >> return a

  -- | Execute the given 'MonadLogicCut' computation in a new frame on the cut stack.
  cutFrame :: m a -> m a

  -- | Determine whether 'cut' or 'commit' has been called in the current cut frame.
  hasCut :: m Bool

  {-# MINIMAL (cut | commit), cutFrame, hasCut #-}

-- | Types which can be split into two components and recombined. Used by 'LogicT' to split a state
-- into backtracking and global components.
class SplittableState s where
  -- | The type of the backtracking component of the state.
  type BacktrackingState s

  -- | The type of the global component of the state.
  type GlobalState s

  -- | Split a state into its backtracking and global components.
  splitState :: s -> (BacktrackingState s, GlobalState s)

  -- | Reconstruct a state object from backtracking and global components.
  combineState :: BacktrackingState s -> GlobalState s -> s

  -- | Extract the backtracking component of a state. Useful with 'gets'.
  backtracking :: s -> BacktrackingState s
  backtracking = fst . splitState

  -- | Extract the global component of a state. Useful with 'gets'.
  global :: s -> GlobalState s
  global = snd . splitState

instance SplittableState () where
  type BacktrackingState () = ()
  type GlobalState () = ()
  splitState () = ((), ())
  combineState () () = ()

-- | Simple state type with backtracking and global components.
data LogicState bs gs = LogicState bs gs
  deriving (Show, Eq)

instance SplittableState (LogicState bs gs) where
  type BacktrackingState (LogicState bs gs) = bs
  type GlobalState (LogicState bs gs) = gs
  splitState (LogicState bs gs)  = (bs, gs)
  combineState = LogicState

-- | Simple state type containing only a global component, with no backtracking state.
newtype Global s = Global s
  deriving (Show, Eq, Num)

instance SplittableState (Global s) where
  type GlobalState (Global s) = s
  type BacktrackingState (Global s) = ()
  splitState (Global s) = ((), s)
  combineState = const Global

-- | Simple state type containing only a backtracking component, with no global state.
newtype Backtracking s = Backtracking s
  deriving (Show, Eq, Num)

instance SplittableState (Backtracking s) where
  type BacktrackingState (Backtracking s) = s
  type GlobalState (Backtracking s) = ()
  splitState (Backtracking s) = (s, ())
  combineState s () = Backtracking s

putGlobal :: (SplittableState s, MonadState s m) => GlobalState s -> m ()
putGlobal gs = do
  (bs, _) <- gets splitState
  put $ combineState bs gs

-- | A monad transformer for performing backtracking computations layered over another monad 'm',
-- with the ability to 'cut', or discard any unexplored choice points, at any time. 'CutT' also
-- embeds a backtracking state (but no global state) into the computation. Use 'LogicT' for a logic
-- monad with both backtracking and global state.
--
-- The semantics of how cut and state interact with the methods of the 'MonadLogic' class are
-- subtle. First, 'cut' and 'state' do not "bubble" through 'msplit'. In other words, the
-- computation @msplit (put s)@ leaves the state unchanged, and the computation
-- @liftM (fst.fromJust) (msplit $ commit a) <|> return b@ produces two results, @a@ and @b@.
--
-- The reason for this seemingly counterintuitive behavior is to avoid confusing semantics when
-- using 'msplit' to convert a 'MonadLogic' computation into a list of results (as in 'runManyCutT',
-- for example). In general, without this design decision, the behavior would get confusing whenever
-- the suspension returned by 'msplit' was executed in the same branch of computation as 'msplit'
-- itself.
--
-- However, in cases where the suspension is not executed in the same branch as 'msplit' (such as
-- in 'once', when it is never executed, or in 'ifte', where it is executed in a separate branch
-- via 'mplus') we can get away with more intuitive semantics. Thus, we override the definitions of
-- 'once' and 'ifte' so that affects ('state' and 'cut') bubble through.
newtype CutT s m a = CutT {
  -- | Run a 'CutT' computation with the specified initial success and failure computations, state,
  -- and cut stack.
  runCutT :: forall r. LogicCont s m a r
}

-- | Continuation function invoked when a 'CutT' monad produces a result. This function takes the
-- current result and state as well as a monadic continuation which computes the rest of the
-- results, and combines the first result with the rest.
type SuccessCont s m a r =  a     -- ^ Initial result.
                         -> s     -- ^ Backtrackable state.
                         -> Bool  -- ^ Whether 'cut' or 'commit' was called in the top cut frame.
                         -> m r   -- ^ Computation producing the rest of the results.
                         -> [m r] -- ^ Cut stack.
                         -> m r   -- ^ Computation combining the first result with the rest.

-- | Continuation function for 'CutT' monads.
type LogicCont s m a r =
  SuccessCont s m a r -- ^ Initial success continuation.
  -> s      -- ^ Initial backtracking state.
  -> Bool   -- ^ Whether 'cut' or 'commit' has already been called before running this continuation.
  -> m r    -- ^ Initial failure continuation.
  -> [m r]  -- ^ Initial cut stack.
  -> m r

-- | Extract all results from a 'CutT' computation, as well as the final state for each result.
runAllCutT :: Monad m => CutT s m a -> s -> m [(a, s)]
runAllCutT m s = runCutT m (\a s' _ fk _ -> liftM ((a, s'):) fk) s False (return []) [return []]

-- | Extract the final state from each branch of a 'CutT' computation.
execAllCutT :: Monad m => CutT s m a -> s -> m [s]
execAllCutT m s = map snd `liftM` runAllCutT m s

-- | Extract all results from a 'CutT' computation.
observeAllCutT :: Monad m => CutT s m a -> s -> m [a]
observeAllCutT m s = map fst `liftM` runAllCutT m s

-- | Similar to 'runAllCutT', but extracts only up to a maximum number of results.
runManyCutT :: Monad m => Int -> CutT s m a -> s -> m [(a, s)]
runManyCutT n m s = observeManyCutT n (liftM2 (,) m get) s

-- | Similar to 'execAllCutT', but extracts only up to a maximum number of results.
execManyCutT :: Monad m => Int -> CutT s m a -> s -> m [s]
execManyCutT n m s = map snd `liftM` runManyCutT n m s

-- | Similar to 'observeAllCutT', but extracts only up to a maximum number of results.
observeManyCutT :: Monad m => Int -> CutT s m a -> s -> m [a]
observeManyCutT n m s
  | n <= 0 = return []
  | n == 1 = runCutT m (\a _ _ _ _ -> return [a]) s False (return []) [return []]
  | otherwise = runCutT (msplit m) sk s False (return []) [return []]
  where sk Nothing _ _ _ _ = return []
        sk (Just (a, fk)) _ _ _ _ = (a:) `liftM` observeManyCutT (n - 1) fk s

instance Functor (CutT s f) where
  fmap f lt = CutT $ \sk s c fk ck -> runCutT lt (\a s' c' fk' ck' -> sk (f a) s' c' fk' ck') s c fk ck

instance Applicative (CutT s f) where
  pure = return
  (<*>) = ap

instance Alternative (CutT s f) where
  empty = CutT $ \_ _ _ fk _ -> fk
  f1 <|> f2 = CutT $ \sk s c fk ck -> runCutT f1 sk s c (runCutT f2 sk s c fk ck) ck

instance Monad (CutT s m) where
  return a = CutT $ \sk s c fk ck -> sk a s c fk ck
  m >>= f = CutT $ \sk s c fk ck -> runCutT m (\a s' c' fk' ck' -> runCutT (f a) sk s' c' fk' ck') s c fk ck
  fail _ = empty

instance MonadPlus (CutT s m) where
  mzero = empty
  mplus = (<|>)

instance MonadTrans (CutT s) where
  lift m = CutT $ \sk s c fk ck -> m >>= \a -> sk a s c fk ck

instance MonadIO m => MonadIO (CutT s m) where
  liftIO = lift . liftIO

instance Monad m => MonadLogic (CutT s m) where
  msplit m = CutT $ \sk s c fk ck -> do
    split <- runCutT m sk' s c (return Nothing) [return Nothing]
    sk split s c fk ck
    where sk' a _ _ fk _ = return $ Just (a, lift fk >>= reflect)

  once m = do
    split <- msplit $ liftM3 (,,) m get hasCut
    case split of
      Just ((a, s, c), _) -> put s >> if c then commit a else return a
      Nothing -> mzero

  ifte cond t e = do
    split <- msplit $ liftM3 (,,) cond get hasCut
    case split of
      Just (r, fk) ->
        let sk (a, s, c) = put s >> (if c then commit a else return a) >>= t
        in sk r `mplus` (fk >>= sk)
      Nothing -> e

instance MonadState s (CutT s m) where
  get = CutT $ \sk s c fk ck -> sk s s c fk ck
  put s = CutT $ \sk _ c fk ck -> sk () s c fk ck

instance Monad m => MonadLogicCut (CutT s m) where
  commit a = CutT $ \sk s _ _ ck -> sk a s True (fk ck) ck
    where fk (c:_) = c
          fk [] = fail "commit: cut stack underflow"

  cutFrame m = do
    didCut <- hasCut
    pushCutFrame
    putCut False
    r <- m
    putCut didCut
    popCutFrame
    return r
    where putCut c = CutT $ \sk s _ fk ck -> sk () s c fk ck
          pushCutFrame = CutT $ \sk s c fk ck -> sk () s c fk (fk:ck)
          popCutFrame = CutT $ \sk s c fk ck -> sk () s c fk (pop ck)
          pop (_:cuts) = cuts
          pop [] = fail "popCutFrame: cut stack underflow"

  hasCut = CutT $ \sk s c fk ck -> sk c s c fk ck

-- | Wrapper around the backtracking component of an arbitrary 'SplittableState' type. This wrapper
-- is only necessary for GHC 7.10, because the typechecker gets confused by the type family
-- 'BacktrackingState'.
newtype LTBS s = LTBS { unLTBS :: BacktrackingState s }

-- | Wrapper around the global component of an arbitrary 'SplittableState' type. This wrapper is
-- only necessary for GHC 7.10, because the typechecker gets confused by the type family
-- 'GlobalState'.
newtype LTGS s = LTGS { unLTGS :: GlobalState s }

-- | A monad transformer for performing backtracking computations layered over another monad 'm',
-- with the ability to 'cut', or discard any unexplored choice points, at any time. 'LogicT' also
-- embeds both backtracking and global state into the computation, implementing the
-- 'MonadLogicState' interface.
--
-- See the note on 'CutT' for a description of how and why 'msplit' interacts with statefulness and
-- 'cut'. Note that global state is handled in the same way as backtracking state: it is not
-- affected by 'msplit', but is affected by 'once' and 'ifte'.
newtype LogicT s m a = LogicT { unLogicT :: CutT (LTBS s) (StateT (LTGS s) m) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadIO, MonadLogicCut)

instance (Monad m, SplittableState s) => MonadLogic (LogicT s m) where
  msplit m = do
    s <- get
    split <- LogicT $ msplit $ unLogicT m
    nextGlobal <- gets global
    put s
    return $ case split of
      Just (a, fk) -> Just (a, putGlobal nextGlobal >> LogicT fk)
      Nothing -> Nothing

  once = LogicT . once . unLogicT
  ifte c t e = LogicT $ ifte (unLogicT c) (unLogicT.t) (unLogicT e)

instance MonadTrans (LogicT s) where
  lift m = LogicT $ lift $ lift m

instance (Monad m, SplittableState s) => MonadState s (LogicT s m) where
  get = liftM2 combineState (LogicT $ gets unLTBS) (LogicT $ lift $ gets unLTGS)
  put s =
    let (bs, gs) = splitState s
    in LogicT (put $ LTBS bs) >> LogicT (lift $ put $ LTGS gs)

-- | Extract all results from a 'LogicT' computation, along with the final state for each branch.
-- Note that the global component of each resulting state is the global state
-- /at the time that branch was evaluated/. Thus, the final global state can be obtained via
-- @snd $ last $ runAllLogicT m s@.
runAllLogicT :: (Monad m, SplittableState s) => LogicT s m a -> s -> m [(a, s)]
runAllLogicT m s = observeAllLogicT (liftM2 (,) m get) s

-- | Extract the final state from each branch of a 'LogicT' computation. As with 'runAllLogicT', the
-- global component of each state object is the global state at the time that result was obtained.
execAllLogicT :: (Monad m, SplittableState s) => LogicT s m a -> s -> m [s]
execAllLogicT m s = map snd `liftM` runAllLogicT m s

-- | Extract all results from a 'LogicT' computation.
observeAllLogicT :: (Monad m, SplittableState s) => LogicT s m a -> s -> m [a]
observeAllLogicT m s =
  let (bs, gs) = splitState s
      cutT = unLogicT m
      st = observeAllCutT cutT (LTBS bs)
  in evalStateT st (LTGS gs)

-- | Similar to 'runAllLogicT', but extracts only up to a maximum number of results.
runManyLogicT :: (Monad m, SplittableState s) => Int -> LogicT s m a -> s -> m [(a, s)]
runManyLogicT n m s = observeManyLogicT n (liftM2 (,) m get) s

-- | Similar to 'execAllLogicT', but extracts only up to a maximum number of results.
execManyLogicT :: (Monad m, SplittableState s) => Int -> LogicT s m a -> s -> m [s]
execManyLogicT n m s = map snd `liftM` runManyLogicT n m s

-- | Similar to 'observeAllLogicT', but extracts only up to a maximum number of results.
observeManyLogicT :: (Monad m, SplittableState s) => Int -> LogicT s m a -> s -> m [a]
observeManyLogicT n m s =
  let (bs, gs) = splitState s
      cutT = unLogicT m
      st = observeManyCutT n cutT (LTBS bs)
  in evalStateT st (LTGS gs)

-- | Non-transformer version of 'LogicT'.
type Logic s = LogicT s Identity

-- | Analagous to 'runAllLogicT'.
runAllLogic :: SplittableState s => Logic s a -> s -> [(a, s)]
runAllLogic m s = runIdentity $ runAllLogicT m s

-- | Analagous to 'execAllLogicT'.
execAllLogic :: SplittableState s => Logic s a -> s -> [s]
execAllLogic m s = runIdentity $ execAllLogicT m s

-- | Analagous to 'observeAllLogicT'.
observeAllLogic :: SplittableState s => Logic s a -> s -> [a]
observeAllLogic m s = runIdentity $ observeAllLogicT m s

-- | Analagous to 'runManyLogicT'.
runManyLogic :: SplittableState s => Int -> Logic s a -> s -> [(a, s)]
runManyLogic n m s = runIdentity $ runManyLogicT n m s

-- | Analagous to 'execManyLogicT'.
execManyLogic :: SplittableState s => Int -> Logic s a -> s -> [s]
execManyLogic n m s = runIdentity $ execManyLogicT n m s

-- | Analagous to 'observeManyLogicT'.
observeManyLogic :: SplittableState s => Int -> Logic s a -> s -> [a]
observeManyLogic n m s = runIdentity $ observeManyLogicT n m s

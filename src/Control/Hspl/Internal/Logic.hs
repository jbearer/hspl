{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
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
implementing this classes.
-}

module Control.Hspl.Internal.Logic (
    module Control.Monad
  , module Control.Monad.Trans
  , module Control.Monad.Logic.Class
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
  , MonadLogicState (..)
  , modifyGlobal
  , modifyBacktracking
  , getsGlobal
  , getsBacktracking
  -- ** The state monad transformer
  , LogicT
  , runManyLogicT
  , execManyLogicT
  , observeManyLogicT
  , runAllLogicT
  , execAllLogicT
  , observeAllLogicT
  -- ** The state monad
  , Logic
  , runManyLogic
  , execManyLogic
  , observeManyLogic
  , runAllLogic
  , execAllLogic
  , observeAllLogic
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Logic.Class
import Control.Monad.State
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

  {-# MINIMAL (cut | commit), cutFrame #-}

-- | Class of logic monads which provide both backtracking and global state. Effects performed on
-- the global state in one branch are visible in subsequently explored parallel branches. In this
-- way, the global state exposes the order in which nondeterministic results are tried. Effects
-- performed on the backtracking state are not visible in parallel branches.
class MonadLogic m => MonadLogicState bs gs m | m -> bs, m -> gs where
  -- | Return the global state.
  getGlobal :: m gs
  getGlobal = stateGlobal $ \s -> (s, s)

  -- | Replace the global state.
  putGlobal :: gs -> m ()
  putGlobal s = stateGlobal $ const ((), s)

  -- | Embed an action on the global state into the monad.
  stateGlobal :: (gs -> (a, gs)) -> m a
  stateGlobal f = do
    gs <- getGlobal
    let (a, gs') = f gs
    putGlobal gs'
    return a

  -- | Get the backtracking state.
  getBacktracking :: m bs
  getBacktracking = stateBacktracking $ \s -> (s, s)

  -- | Replace the backtracking state.
  putBacktracking :: bs -> m ()
  putBacktracking s = stateBacktracking $ const ((), s)

  -- | Embed an action on the backtracking state into the monad.
  stateBacktracking :: (bs -> (a, bs)) -> m a
  stateBacktracking f = do
    bs <- getBacktracking
    let (a, bs') = f bs
    putBacktracking bs'
    return a

  {-# MINIMAL (stateGlobal | getGlobal, putGlobal), (stateBacktracking | getBacktracking, putBacktracking) #-}

-- | Modify the global state by applying a function.
modifyGlobal :: MonadLogicState bs gs m => (gs -> gs) -> m ()
modifyGlobal f = getGlobal >>= putGlobal . f

-- | Get a specific comonent of the global state using a projection function.
getsGlobal :: MonadLogicState bs gs m => (gs -> a) -> m a
getsGlobal f = liftM f getGlobal

-- | Modify the backtracking state by applying a function.
modifyBacktracking :: MonadLogicState bs gs m => (bs -> bs) -> m ()
modifyBacktracking f = getBacktracking >>= putBacktracking . f

-- | Get a specific component of the backtracking state using a projection function.
getsBacktracking :: MonadLogicState bs gs m => (bs -> a) -> m a
getsBacktracking f = liftM f getBacktracking

-- | A monad transformer for performing backtracking computations layered over another monad 'm',
-- with the ability to 'cut', or discard any unexplored choice points, at any time. 'CutT' also
-- embeds a backtracking state (but no global state) into the computation. Use 'LogicT' for a logic
-- monad with both backtracking and global state.
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
                (r, s', c') <- runCutT m extract s c (return (Nothing, s, c)) [return (Nothing, s ,c)]
                let fk' = if c' then head ck else fk
                sk r s' c' fk' ck
    where extract a s c fk _ = return (Just (a, lift fk >>= reflect'), s, c)
          reflect' (fk, _, _) = reflect fk

instance MonadState s (CutT s m) where
  get = CutT $ \sk s c fk ck -> sk s s c fk ck
  put s = CutT $ \sk _ c fk ck -> sk () s c fk ck

instance Monad m => MonadLogicCut (CutT s m) where
  commit a = CutT $ \sk s _ _ ck -> sk a s True (fk ck) ck
    where fk (c:_) = c
          fk [] = fail "commit: cut stack underflow"

  cutFrame m = do
    didCut <- getCut
    pushCutFrame
    putCut False
    r <- m
    putCut didCut
    popCutFrame
    return r
    where getCut = CutT $ \sk s c fk ck -> sk c s c fk ck
          putCut c = CutT $ \sk s _ fk ck -> sk () s c fk ck
          pushCutFrame = CutT $ \sk s c fk ck -> sk () s c fk (fk:ck)
          popCutFrame = CutT $ \sk s c fk ck -> sk () s c fk (pop ck)
          pop (_:cuts) = cuts
          pop [] = fail "popCutFrame: cut stack underflow"

-- | A monad transformer for performing backtracking computations layered over another monad 'm',
-- with the ability to 'cut', or discard any unexplored choice points, at any time. 'LogicT' also
-- embeds both backtracking and global state into the computation, implementing the
-- 'MonadLogicState' interface.
newtype LogicT bs gs m a = LogicT { unLogicT :: CutT bs (StateT gs m) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadIO, MonadLogic, MonadLogicCut)

instance MonadTrans (LogicT bs gs) where
  lift m = LogicT $ lift $ lift m

instance Monad m => MonadState (bs, gs) (LogicT bs gs m) where
  get = LogicT $ lift get >>= \gs -> get >>= \bs -> return (bs, gs)
  put (bs, gs) = LogicT $ lift (put gs) >> put bs

instance Monad m => MonadLogicState bs gs (LogicT bs gs m) where
  stateGlobal = LogicT . lift . state
  stateBacktracking = LogicT . state

-- | Extract all results from a 'LogicT' computation, along with the final backtracking state for
-- each branch and the final global state.
runAllLogicT :: Monad m => LogicT bs gs m a -> bs -> gs -> m ([(a, bs)], gs)
runAllLogicT m bs gs =
  let cutT = unLogicT m
      st = runAllCutT cutT bs
  in runStateT st gs

-- | Extract the final backtracking state from each branch of a 'LogicT' computation, as well as the
-- final global state.
execAllLogicT :: Monad m => LogicT bs gs m a -> bs -> gs -> m ([bs], gs)
execAllLogicT m bs gs = do
  (results, gs') <- runAllLogicT m bs gs
  return (map snd results, gs')

-- | Extract all results from a 'LogicT' computation.
observeAllLogicT :: Monad m => LogicT bs gs m a -> bs -> gs -> m [a]
observeAllLogicT m bs gs = do
  (results, _) <- runAllLogicT m bs gs
  return $ map fst results

-- | Similar to 'runAllLogicT', but extracts only up to a maximum number of results.
runManyLogicT :: Monad m => Int -> LogicT bs gs m a -> bs -> gs -> m ([(a, bs)], gs)
runManyLogicT n m bs gs =
  let cutT = unLogicT m
      st = runManyCutT n cutT bs
  in runStateT st gs

-- | Similar to 'execAllLogicT', but extracts only up to a maximum number of results.
execManyLogicT :: Monad m => Int -> LogicT bs gs m a -> bs -> gs -> m ([bs], gs)
execManyLogicT n m bs gs = do
  (results, gs') <- runManyLogicT n m bs gs
  return (map snd results, gs')

-- | Similar to 'observeAllLogicT', but extracts only up to a maximum number of results.
observeManyLogicT :: Monad m => Int -> LogicT bs gs m a -> bs -> gs -> m [a]
observeManyLogicT n m bs gs = do
  (results, _) <- runManyLogicT n m bs gs
  return $ map fst results

-- | Non-transformer version of 'LogicT'.
type Logic bs gs = LogicT bs gs Identity

-- | Analagous to 'runAllLogicT'.
runAllLogic :: Logic bs gs a -> bs -> gs -> ([(a, bs)], gs)
runAllLogic m bs gs = runIdentity $ runAllLogicT m bs gs

-- | Analagous to 'execAllLogicT'.
execAllLogic :: Logic bs gs a -> bs -> gs -> ([bs], gs)
execAllLogic m bs gs = runIdentity $ execAllLogicT m bs gs

-- | Analagous to 'observeAllLogicT'.
observeAllLogic :: Logic bs gs a -> bs -> gs -> [a]
observeAllLogic m bs gs = runIdentity $ observeAllLogicT m bs gs

-- | Analagous to 'runManyLogicT'.
runManyLogic :: Int -> Logic bs gs a -> bs -> gs -> ([(a, bs)], gs)
runManyLogic n m bs gs = runIdentity $ runManyLogicT n m bs gs

-- | Analagous to 'execManyLogicT'.
execManyLogic :: Int -> Logic bs gs a -> bs -> gs -> ([bs], gs)
execManyLogic n m bs gs = runIdentity $ execManyLogicT n m bs gs

-- | Analagous to 'observeManyLogicT'.
observeManyLogic :: Int -> Logic bs gs a -> bs -> gs -> [a]
observeManyLogic n m bs gs = runIdentity $ observeManyLogicT n m bs gs

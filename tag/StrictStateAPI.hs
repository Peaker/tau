{-# OPTIONS -Wall #-}
module StrictStateAPI (state', modify', put') where

import Control.Monad.Trans.State.Strict (State, StateT, state, modify)

state' :: (s -> (a, s)) -> State s a
state' f = state (f $!)

modify' :: Monad m => (s -> s) -> StateT s m ()
modify' f = modify (f $!)

put' :: Monad m => s -> StateT s m ()
put' = modify' . const

{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Rewrite where
import Control.Lens hiding (from, to, deep, at)
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative

import Control.Monad.Fail

newtype  Rewrite' b a = R (ReaderT (Env b ()) Maybe a)
  deriving (Applicative, Functor, Monad, Alternative, MonadFail, MonadReader (Env b ()))
type Rewrite a = Rewrite'  a a
   
class (MonadFail m) => MonadRewrite i e m | m -> e, m -> i where
    environment :: m i
    cur :: m e
instance MonadRewrite () i (Rewrite' i) where
    environment  = asks envEnv
    cur = asks envElem
data Env e i
  = Env
  { envEnv :: i
  , envElem :: e
  }

at :: a -> Rewrite a -> Rewrite' s a
at a r = pure $ runRewrite r a

rewriting :: ((a -> Identity  a) -> s -> Identity s) -> Rewrite a -> Rewrite s
rewriting l (R f) = do
    s <- cur
    pure $ runIdentity $ l step s
  where
     step  a = case runReaderT f (Env () a) of
       Just a' -> Identity a'
       Nothing -> Identity a

rewriting1 :: ((a -> State Bool a) -> s -> State Bool s) -> ReaderT a (StateT Bool Maybe) a -> s -> s
rewriting1 l f s = evalState (l step s) False
  where
     step = state . proc
     proc a b
       | b = (a, b)
       | otherwise = case runStateT (runReaderT f a) b of
           Just (a', _b) -> (a', True)
           Nothing -> (a, b)

runRewrite :: Rewrite s -> s -> s
runRewrite (R m) s = maybe s id $ runReaderT m (Env () s)


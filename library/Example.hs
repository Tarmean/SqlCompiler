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
module Example  (main, rewriting1, rewriting, toListM, foo) where
import Control.Lens hiding (from, to, deep)
import Control.Monad.Reader
import Control.Monad.State
import GHC.Generics
import Generics.Kind

import Control.Monad.Fail
import TraverseChild
import Data.Monoid

data BinOp = Add | Mult
  deriving (Eq, Generic, Show)
data Ex = Lit Int | BinOp BinOp Ex Ex
    deriving (Show, Generic)
instance GenericK BinOp 'LoT0 where
    type RepK BinOp = U1 :+: U1
instance GenericK Ex 'LoT0 where
   type RepK Ex = F (Kon Int) :+: (F (Kon BinOp) :*: F (Kon Ex) :*: F (Kon Ex))
makePrisms ''Ex

instance (MonadEnv (Sum Int) f, AllChildren c Ex e f) => TraverseChild c Ex e f where
    type instance TraverseChildConstraint Ex f = MonadEnv (Sum Int) f
    child f a@(Lit _) = defaultChild @c @Ex @e f a
    child f a = modifyEnv ((+1) :: (Sum Int) -> (Sum Int)) (defaultChild @c @Ex @e f a)
instance TraverseChild c BinOp e f where

foo :: Ex -> Ex
foo = topdown . _Lit +~ 1

main :: IO ()
main = do
    print $ bar testVal
  where testVal = BinOp Add (Lit 2) (BinOp Add (Lit 3) (BinOp Add (Lit 0) (Lit 0)))
bar :: Ex -> Ex
bar = rewriting bottomup
  $ do
      i <- cur
      Sum e <- environment
      return (i + e :: Int)
      
  -- $ do
  --   (Lit x, Lit y) <- cur _Add
  --   pure (Lit $ x + y)
  -- <|> do
  --   (Lit x, Lit y) <- cur _Mult
  --   pure (Lit $ x * y)

aBinOp :: BinOp -> Prism' Ex (Ex,Ex)
aBinOp cop = prism' (\(x,y) -> BinOp cop x y) (\s -> case s of
    BinOp cop' x y | cop == cop' -> Just (x,y)
    _ -> Nothing)
_Add, _Mult:: Prism' Ex (Ex,Ex)
_Add = aBinOp Add
_Mult = aBinOp Mult
   
class (MonadFail m) => MonadRewrite i e m | m -> e, m -> i where
    environment :: m i
    cur :: m e
-- instance MonadRewrite e (ReaderT e Maybe) where
--     environment  = asks envEnv
--     cur p = asks envElem
instance MonadRewrite i e (ReaderT (Env e i) Maybe) where
    environment  = asks envEnv
    cur = asks envElem
data Env e i
  = Env
  { envEnv :: i
  , envElem :: e
  }


rewriting :: (Monoid i) => ((a -> Reader i  a) -> s -> Reader i s) -> (ReaderT (Env a i) Maybe a) -> s -> s
rewriting l f s = runReader (l step s) mempty
  where
     step  a = reader $ \i -> case runReaderT f (Env i a) of
       Just a' -> a'
       Nothing -> a

rewriting1 :: ((a -> State Bool a) -> s -> State Bool s) -> (ReaderT a (StateT Bool Maybe) a) -> s -> s
rewriting1 l f s = evalState (l step s) False
  where
     step = state . proc
     proc a b
       | b = (a, b)
       | otherwise = case runStateT (runReaderT f a) b of
           Just (a', _b) -> (a', True)
           Nothing -> (a, b)


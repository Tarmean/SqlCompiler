{-# Language DataKinds #-}
{-# Language UndecidableInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleContexts #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language ExistentialQuantification #-}
{-# Language GADTs #-}
{-# Language DeriveGeneric #-}
{-# Language FlexibleInstances #-}
{-# Language StandaloneDeriving #-}
{-# Language KindSignatures #-}
module Types where
import GHC.Generics (Generic,from, to, Rec0, Rep)
import Generics.Kind
import TraverseChild
import Example
import Control.Monad.Fail

bar :: Expr -> Expr
bar = rewriting topdown fooz
fooz :: (MonadRewrite () (Comprehension 'True) m) => m (Comprehension 'True)
fooz = do
    CCons (Guard (BinOp And l r)) o <- cur
    pure $ CCons (Guard l) (CCons (Guard r) o)

data BinOpT = Add | Sub | Mult | And
  deriving (Show, Eq, Generic)
instance GenericK BinOpT 'LoT0 where
    type RepK BinOpT = (U1 :+: U1) :+: (U1 :+: U1)
data UnOpT = Singleton
  deriving (Show, Eq, Generic)
instance (AllChildren c Expr e f) => TraverseChild c Expr e f where

instance GenericK UnOpT 'LoT0 where
    type RepK UnOpT = U1
newtype Ident = Ident Int
  deriving (Show, Eq, Generic)
instance GenericK Ident 'LoT0 where
    type RepK Ident = F ('Kon Int)
data Expr = BinOp BinOpT Expr Expr | UnOp UnOpT Expr | Comp (Comprehension ('True)) | Lit Lit | UVar Ident
deriving instance Show Expr
instance Split Expr Expr 'LoT0 where
instance Eq Expr where
    (BinOp a b c) == (BinOp x y z) = a == x && b == y && c == z
    (UnOp a b) == (UnOp x y) = a == x && b == y
    (Lit a) == (Lit x) = a == x
    (UVar a) == (UVar x) = a == x
    (Comp a) == (Comp x) = compComp a x
    _ == _ = False
compComp :: Comprehension a -> Comprehension b -> Bool
compComp (CCons a x) (CCons b y) = a == b && compComp x y
compComp (CEnd a) (CEnd b) = a == b
compComp _ _ = False

instance GenericK Expr 'LoT0 where
    type RepK Expr
        = ((F ('Kon BinOpT) :*: F ('Kon Expr) :*: F ('Kon Expr))
            :+: (F ('Kon UnOpT) :*: F ('Kon Expr)))
        :+: (F ('Kon (Comprehension 'True))
            :+: F ('Kon Lit)
            :+: F ('Kon Ident))
    toK (L1 (L1 (F a :*: F b :*: F c)))= BinOp a b c
    toK (L1 (R1 (F a :*:  F b)))= UnOp a b
    toK (R1 (L1 (F a)))= Comp a
    toK (R1 (R1 (L1 (F a))))= Lit a
    toK (R1 (R1 (R1 (F a))))= UVar a
    fromK (BinOp a b c) = L1 (L1 (F a :*: F b :*: F c))
    fromK (UnOp a b) = L1 (R1 (F a :*: F b))
    fromK (Comp a) = R1 (L1 (F a))
    fromK (Lit a) = R1 (R1 (L1 (F a)))
    fromK (UVar a) = R1 (R1 (R1 (F a)))

deriving instance Show (Comprehension b)
data Comprehension b where
    CEnd :: Expr -> Comprehension 'False
    CCons :: CompElem -> Comprehension a -> Comprehension ('True)
instance GenericK (Comprehension 'True) 'LoT0 where
    type RepK (Comprehension 'True) = E (F ('Kon CompElem) :*: F (Comprehension :$: V0))
    toK (E (F a :*: F b))= CCons a b
    fromK (CCons a b) = E (F a :*: F b)
instance GenericK (Comprehension 'False) 'LoT0 where
    type RepK (Comprehension 'False) = F ('Kon Expr)
    toK (F a) = CEnd a
    fromK (CEnd a) = F a
-- deriving instance Show (Comprehension a)
instance (AllChildren c (Comprehension a) e f) => TraverseChild c (Comprehension a) e f where
instance (AllChildren c BinOpT e f) => TraverseChild c (BinOpT) e f where
instance (AllChildren c UnOpT e f) => TraverseChild c (UnOpT) e f where
instance (AllChildren c Lit e f) => TraverseChild c (Lit) e f where
instance (AllChildren c CompElem e f) => TraverseChild c (CompElem) e f where
instance (AllChildren c Ident e f) => TraverseChild c (Ident) e f where
instance Split (Comprehension a) (Comprehension a) 'LoT0 where

data Lit = LitBool Bool  | LitInt Int
  deriving (Show, Eq, Generic)
data CompElem = Guard Expr | Binding Expr Ident
  deriving (Show, Eq, Generic)
instance GenericK Lit 'LoT0 where
    type RepK Lit = F (Kon Bool) :+: F (Kon Int)
instance GenericK CompElem 'LoT0 where
    type RepK CompElem = F (Kon Expr) :+: (F (Kon Expr) :*: F (Kon Ident))

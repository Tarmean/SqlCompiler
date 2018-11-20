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
{-# Language PatternSynonyms #-}
module Types where
import GHC.Generics (Generic,from, to, Rec0, Rep)
import Generics.Kind
import TraverseChild
import Example

fooz :: Expr -> Expr
fooz = rewriting topdown $ do
    Guard (BinOp And l r) :- rest <- cur
    pure $ Guard l :- Guard r :- rest

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
compComp (CCons a (A x)) (CCons b (A y)) = a == b && compComp x y
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

data Comprehension b where
    CEnd :: Expr -> Comprehension 'False
    CCons :: CompElem -> AComprehension -> Comprehension ('True)
instance GenericK (Comprehension 'True) 'LoT0 where
    type RepK (Comprehension 'True) = F ('Kon CompElem) :*: F ('Kon AComprehension)
    toK (F a :*: F b)= CCons a b
    fromK (CCons a b) = F a :*: F b
data AComprehension where
    A :: Comprehension a -> AComprehension
instance Show AComprehension where
    show (A b) = show b
instance Show (Comprehension a) where
    showsPrec i (CCons a b) = showsPrec i a . showString (" :- ") . showsPrec i b
    showsPrec i (CEnd b) = showsPrec i b
infixr 5 :-
pattern (:-) :: () => forall (a :: Bool).  CompElem -> Comprehension a -> Comprehension 'True
pattern (:-) a  b = CCons a (A b)

instance GenericK AComprehension 'LoT0 where
    type RepK AComprehension = F ('Kon (Comprehension 'True)) :+: F ('Kon (Comprehension 'False))
    toK (L1 (F a)) = A a
    toK (R1 (F a)) = A a
    fromK (A w@(CCons _ _)) = L1 (F w)
    fromK (A w@(CEnd _)) = R1 (F w)
instance GenericK (Comprehension 'False) 'LoT0 where
    type RepK (Comprehension 'False) = F ('Kon Expr)
    toK (F a) = CEnd a
    fromK (CEnd a) = F a
instance (AllChildren c (Comprehension a) e f) => TraverseChild c (Comprehension a) e f where
instance (AllChildren c BinOpT e f) => TraverseChild c (BinOpT) e f where
instance (AllChildren c UnOpT e f) => TraverseChild c (UnOpT) e f where
instance (AllChildren c Lit e f) => TraverseChild c (Lit) e f where
instance (AllChildren c CompElem e f) => TraverseChild c (CompElem) e f where
instance (AllChildren c Ident e f) => TraverseChild c (Ident) e f where
instance (AllChildren c AComprehension e f) => TraverseChild c (AComprehension) e f where
instance Split (Comprehension a) (Comprehension a) 'LoT0 where
instance Split AComprehension AComprehension 'LoT0 where
instance Split CompElem CompElem 'LoT0 where

var :: Int -> Expr
var i = UVar (Ident i)

data Lit = LitBool Bool  | LitInt Int
  deriving (Show, Eq, Generic)
data CompElem = Guard Expr | Bind Expr Ident
  deriving (Show, Eq, Generic)
instance GenericK Lit 'LoT0 where
    type RepK Lit = F ('Kon Bool) :+: F ('Kon Int)
instance GenericK CompElem 'LoT0 where
    type RepK CompElem = F ('Kon Expr) :+: (F ('Kon Expr) :*: F ('Kon Ident))

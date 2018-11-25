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
{-# Language PartialTypeSignatures #-}
{-# Language TemplateHaskell #-}
{-# Language GeneralizedNewtypeDeriving #-}
module Types where
import GHC.Generics (Generic)
import Control.Monad (guard)
import Generics.Kind
import TraverseChild
import Control.Lens.TH
import Control.Lens hiding (Empty)
import Data.Monoid (Endo)
import Control.Monad.Writer (WriterT)
import Rewrite

data BinOpT = Add | Sub | Mult | And | Eql
  deriving (Show, Eq, Generic)
instance GenericK BinOpT 'LoT0 where
    type RepK BinOpT = (U1 :+: U1) :+: (U1 :+: U1 :+: U1) 
data UnOpT = Singleton
  deriving (Show, Eq, Generic)
instance (AllChildren c Expr e f) => TraverseChild c Expr e f where

instance GenericK UnOpT 'LoT0 where
    type RepK UnOpT = U1
newtype Ident = Ident Int
  deriving (Num, Show, Eq, Generic)
data Expr = BinOp BinOpT Expr Expr | UnOp UnOpT Expr | Comp (Comprehension 'NonEmpty) | Lit Lit | UVar Ident
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
compComp (a :- x) (b :- y) = a == b && compComp x y
compComp (CEnd a) (CEnd b) = a == b
compComp _ _ = False

data CompKind = Empty | NonEmpty
data Comprehension b where
    CEnd :: Expr -> Comprehension 'Empty
    (:-) :: CompElem -> Comprehension a -> Comprehension ('NonEmpty)

instance Show (Comprehension a) where
    showsPrec i (a :- b) = showsPrec i a . showString (" :- ") . showsPrec i b
    showsPrec i (CEnd b) = showsPrec i b
infixr 5 :-

instance GenericK Expr 'LoT0 where
    type RepK Expr
        = ((F ('Kon BinOpT) :*: F ('Kon Expr) :*: F ('Kon Expr))
            :+: (F ('Kon UnOpT) :*: F ('Kon Expr)))
        :+: (F ('Kon (Comprehension 'NonEmpty))
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
instance GenericK Ident 'LoT0 where
    type RepK Ident = F ('Kon Int)

instance GenericK Comprehension (a ':&&: 'LoT0) where
    type RepK Comprehension
        =  ((V0 :~: 'Kon 'NonEmpty) :=>: (F ('Kon CompElem) :*: 

                (F ('Kon (Comprehension 'NonEmpty)) :+: F ('Kon (Comprehension 'Empty)))))
           :+: ((V0 :~: 'Kon 'Empty) :=>:  F ('Kon Expr))
    fromK (a :- (b :- c)) = L1 (C (F a :*: (L1 (F (b :- c)))))
    fromK (a :- (CEnd b)) = L1 (C (F a :*: (R1 (F (CEnd b)))))
    fromK (CEnd a) = R1 (C (F a))
    toK (L1 (C (F a :*: L1 (F b)))) = a :- b
    toK (L1 (C (F a :*: R1 (F b)))) = a :- b
    toK (R1 (C (F a))) = CEnd a

instance GenericK Lit 'LoT0 where
    type RepK Lit = F ('Kon Bool) :+: F ('Kon Int) :+: F ('Kon String)
instance GenericK CompElem 'LoT0 where
    type RepK CompElem = F ('Kon Expr) :+: (F ('Kon Expr) :*: F ('Kon Ident))


instance (AllChildren c (Comprehension a) e f) => TraverseChild c (Comprehension a) e f where
instance (AllChildren c BinOpT e f) => TraverseChild c (BinOpT) e f where
instance (AllChildren c UnOpT e f) => TraverseChild c (UnOpT) e f where
instance (AllChildren c Lit e f) => TraverseChild c (Lit) e f where
instance (AllChildren c CompElem e f) => TraverseChild c (CompElem) e f where
instance (AllChildren c Ident e f) => TraverseChild c (Ident) e f where
instance Split (Comprehension a) (Comprehension)  (a ':&&: 'LoT0) where
instance Split CompElem CompElem 'LoT0 where
instance Split Lit Lit 'LoT0 where

var :: Int -> Expr
var i = UVar (Ident i)

data Lit = LitBool Bool  | LitInt Int | Table String
  deriving (Show, Eq, Generic)
data CompElem = Guard Expr | Bind Expr Ident
  deriving (Show, Eq, Generic)
makePrisms ''CompElem

compExpr :: Comprehension a -> Expr
compExpr (_ :- b) = compExpr b
compExpr (CEnd b) = b
type family CompOr a b where
    CompOr 'NonEmpty _ = 'NonEmpty
    CompOr _ b = b
compAppend :: Comprehension a -> Comprehension b -> Comprehension (a `CompOr` b)
compAppend (a :- b) c = a :- (compAppend b c)
compAppend (CEnd _r) c = c

freeVars :: (TopDown a Ident (WriterT (Endo [Ident]) Identity)) => a -> [Ident]
freeVars = toListM topdown 
inline :: (TopDown a Expr Identity) => Expr -> Ident -> Rewrite a
inline e i = rewriting topdown $ do
    UVar j <- cur
    guard (i == j)
    pure e

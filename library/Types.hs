{-# Language DataKinds #-}
{-# Language MultiParamTypeClasses #-}
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


data BinOpT = Add | Sub | Mult
  deriving (Show, Eq, Generic)
instance GenericK BinOpT 'LoT0 where
    type RepK BinOpT = U1 :+: U1 :+: U1
data UnOpT = Singleton
  deriving (Show, Eq, Generic)
instance GenericK UnOpT 'LoT0 where
    type RepK UnOpT = U1
newtype Ident = Ident Int
  deriving (Show, Eq, Generic)
instance GenericK Ident 'LoT0 where
    type RepK Ident = F ('Kon Int)
data Expr = BinOp BinOpT Expr Expr | UnOp UnOpT Expr | forall a. Comp (Comprehension ('S a)) | Lit Lit | UVar Ident
deriving instance Show Expr
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
        :+: (E (F (Comprehension :$: ('S :$: V0)))
            :+: F ('Kon Lit)
            :+: F ('Kon Ident))
    toK (L1 (L1 (F a :*: F b :*: F c)))= BinOp a b c
    toK (L1 (R1 (F a :*:  F b)))= UnOp a b
    toK (R1 (L1 (E (F a))))= Comp a
    toK (R1 (R1 (L1 (F a))))= Lit a
    toK (R1 (R1 (R1 (F a))))= UVar a
    fromK (BinOp a b c) = L1 (L1 (F a :*: F b :*: F c))
    fromK (UnOp a b) = L1 (R1 (F a :*: F b))
    fromK (Comp a) = R1 (L1 (E (F a)))
    fromK (Lit a) = R1 (R1 (L1 (F a)))
    fromK (UVar a) = R1 (R1 (R1 (F a)))

deriving instance Show (Comprehension b)
data Comprehension b where
    CEnd :: Expr -> Comprehension 'Z
    CCons :: CompElem -> Comprehension a -> Comprehension ('S a)
instance GenericK (Comprehension ('S a)) 'LoT0 where
    type RepK (Comprehension ('S a)) = F ('Kon CompElem) :*: F ('Kon (Comprehension a))
    toK (F a :*: F b)= CCons a b
    fromK (CCons a b) = F a :*: F b
instance GenericK (Comprehension 'Z) 'LoT0 where
    type RepK (Comprehension 'Z) = F ('Kon Expr)
    toK (F a) = CEnd a
    fromK (CEnd a) = F a
-- deriving instance Show (Comprehension a)


data Lit = LitBool Bool  | LitInt Int
  deriving (Show, Eq, Generic)
data CompElem = Pattern Expr | Binding Expr Ident
  deriving (Show, Eq, Generic)

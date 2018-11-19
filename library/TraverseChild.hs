{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE InstanceSigs #-}
module TraverseChild where
import GHC.Types
-- import GHC.Generics
import Data.Type.Equality
import Control.Lens hiding (from, to, deep)
import Control.Monad.Writer
import Control.Monad.Reader
import Generics.Kind

class TraverseChild c s (t::Type) f where
    type family TraverseChildConstraint s (f :: Type -> Type) :: Constraint
    type instance TraverseChildConstraint s f = ()
    child :: (Applicative f, TraverseChildConstraint s f) => (forall a. (TraverseChildConstraint a f, c a t f)  => a -> f a) -> s -> f s
    default child :: (AllChildren c s t f, Applicative f) => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) ->  s -> f s
    child f a = defaultChild @c @s @t @f f a
instance TraverseChild c Int e f where
instance TraverseChild c Integer e f where
instance TraverseChild c Float e f where
instance TraverseChild c Double e f where
instance TraverseChild c Char e f where
defaultChild :: forall c s t f. (AllChildren c s t f, Applicative f) => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) ->  s -> f s
defaultChild f a = dispatchChild @(Interesting s t) @c @s @t @f f a

class MonadEnv s f where
    modifyEnv :: (s -> s) -> f a -> f a
instance MonadEnv s Identity where
    modifyEnv _ m = m
instance MonadEnv s (Reader s) where
    modifyEnv s m = local s m

toListM :: ((a -> Writer (Endo [a]) a) -> (s -> Writer (Endo [a]) s)) -> s -> [a]
toListM l s = case runWriter $ l step s of
    (_, Endo o) -> o []
  where step a = a <$ tell (Endo (a:))

class GChild (c :: Type -> Type -> (Type->Type) -> Constraint) t (s :: LoT k -> *) f (x :: LoT k) where
    gchild :: Applicative f => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) -> s x -> f (s x)
instance (GChild c t l f k) => GChild c t (M1 p q l) f k where
    {-# INLINE gchild #-}
    gchild f (M1 l) = M1 <$> (gchild @c @t f l)
instance (GChild c t l f k, GChild c t r f k) => GChild c t (l :*: r) f k where
    {-# INLINE gchild #-}
    gchild f (l :*: r) = (:*:) <$> gchild @c @t f l <*> gchild @c @t f r
instance (GChild c t l f k, GChild c t r f k) => GChild c t (l :+: r) f k where
    {-# INLINE gchild #-}
    gchild f (L1 l) = L1 <$> gchild @c @t f l
    gchild f (R1 l) = R1 <$> gchild @c @t f l
instance GChild c t U1 f k where
    {-# INLINE gchild #-}
    gchild _f U1 = pure U1
instance (TraverseChildConstraint (Ty x k) f, c (Ty x k) t f) => GChild c t (F x) f k where
    {-# INLINE gchild #-}
    gchild f (F x) = F <$> f x

class DispatchChild (b :: Bool) (c :: Type -> Type -> (Type->Type) -> Constraint) s t f where
    dispatchChild :: Applicative f => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) -> s -> f s
instance DispatchChild 'False c s t f where
    {-# INLINE dispatchChild #-}
    dispatchChild _f s = pure s
instance (GChild c t (RepK s) f 'LoT0, GenericK s 'LoT0) => DispatchChild 'True c s t f where
    {-# INLINE dispatchChild #-}
    dispatchChild f s = fmap (toN @'Z) $ gchild @c @t f $ fromN @'Z s

    
-- Inlining this alias gives a type error - weird
type AllChildren c s t f= DispatchChild (Interesting s t) c s t f

class  TopDownT (s == a) s a f => TopDown s a f where
instance  TopDownT (s == a) s a f => TopDown s a f where
class TopDownT (b :: Bool) s a f where
    topdown' :: Monad f => (a -> f a) -> s -> f s
instance (TraverseChildConstraint a f, TraverseChild TopDown a a f) => TopDownT 'True a a f where
    -- {-# INLINE topdown' #-}
    topdown' f a = f a >>= child @TopDown @a @a @f (topdown f)
instance (TraverseChildConstraint s f, TraverseChild TopDown s a f) => TopDownT 'False s a f where
    -- {-# INLINE topdown' #-}
    topdown' f a = child @TopDown @s @a @f (topdown f) a
topdown :: forall f s a. (Monad f, TopDown s a f) => (a -> f a) -> s -> f s
topdown f a = topdown' @(s == a) @s @a f a
     
class  BottomUpT (s == a) s a f => BottomUp s a f where
instance  BottomUpT (s == a) s a f => BottomUp s a f where
class BottomUpT (b :: Bool) s a f where
    bottomup' :: Monad f => (a -> f a) -> s -> f s
instance (TraverseChildConstraint a f, TraverseChild BottomUp a a f) => BottomUpT 'True a a f where
    -- {-# INLINE bottomup' #-}
    bottomup' f a = child @BottomUp @a @a @f (bottomup f) a >>= f
instance (TraverseChildConstraint s f, TraverseChild BottomUp s a f) => BottomUpT 'False s a f where
    -- {-# INLINE bottomup' #-}
    bottomup' f a = child @BottomUp @s @a @f (bottomup f) a
bottomup :: forall f s a. (Monad f, BottomUp s a f) => (a -> f a) -> s -> f s
bottomup f a = bottomup' @(s == a) @s @a f a

type Interesting s a = Fst (InterestingStep s '[] a)

type family InterestingStep (s::Type) seen a where
    InterestingStep Char    seen a = '( 'False, seen)
    InterestingStep Double  seen a = '( 'False, seen)
    InterestingStep Float   seen a = '( 'False, seen)
    InterestingStep Int     seen a = '( 'False, seen)
    InterestingStep Integer seen a = '( 'False, seen)
    InterestingStep s       seen a = Interesting' (RepK s) seen a

type family Interesting' m seen a :: (Bool, [Type]) where
    Interesting' (M1 _ m f) seen a = Interesting' f seen a
    Interesting' (l :*: r) seen a = InterestingBranch (Interesting' l seen a) r a
    Interesting' (l :+: r) seen a = InterestingBranch (Interesting' l seen a) r a
    Interesting' (F a) seen b = InterestingB' (Ty a 'LoT0 == b) a seen b
    Interesting' U1 seen _ = '( 'False, seen)
type family InterestingB' v a seen b where
     InterestingB' 'True a seen b = '( 'True, seen)
     InterestingB' 'False a seen b = InterestingRecurse (Elem (Ty a 'LoT0) seen) (Ty a 'LoT0) seen b



type family InterestingBranch b r a where
    InterestingBranch '( 'True, ls) _ _ = '( 'True, ls)
    InterestingBranch '( 'False, ls) r a = Interesting' r ls a
type family InterestingRecurse b r seen a where
    InterestingRecurse 'True r seen a = '( 'False, seen)
    InterestingRecurse 'False r seen a = InterestingStep r (r ': seen) a

type family Elem a as where
    Elem a (a ': _) = 'True
    Elem a (_ ': as) = Elem a as
    Elem a '[] = 'False
type family Snd (k::(a, b)) :: b where
    Snd '(l, r) = r
type family Fst a where Fst '(l, r) = l

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
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
module TraverseChild (topdown, bottomup, AllChildren, TraverseChild, TopDown, BottomUp, toListM) where
import OrphanInstances()
import GHC.Types hiding (Nat)
-- import GHC.TypeLits
-- import GHC.Generics
import Data.Type.Equality
import Control.Monad.Writer hiding (Any)
import Generics.Kind

type AllChildren c s t f= DispatchChild (Interesting s t) c s t f
class TraverseChild c s (t::Type) f where
    type family TraverseChildConstraint s (f :: Type -> Type) :: Constraint
    type instance TraverseChildConstraint s f = ()
    child :: (Applicative f, TraverseChildConstraint s f) => (forall a. (TraverseChildConstraint a f, c a t f)  => a -> f a) -> s -> f s
    default child :: (AllChildren c s t f , Applicative f) => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) ->  s -> f s
    child f a = defaultChild @c @s @t @f f a
instance TraverseChild c Int e f where
    child _ a = pure a
instance TraverseChild c Integer e f where
    child _ a = pure a
instance TraverseChild c Float e f where
    child _ a = pure a
instance TraverseChild c Double e f where
    child _ a = pure a
instance TraverseChild c Char e f where
    child _ a = pure a

defaultChild :: forall c s t f. (AllChildren c s t f, Applicative f) => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) ->  s -> f s
defaultChild f a = dispatchChild @(Interesting s t) @c @s @t @f f a

-- class MonadEnv s f where
--     modifyEnv :: (s -> s) -> f a -> f a
-- instance MonadEnv s Identity where
--     modifyEnv _ m = m
-- instance MonadEnv s (Reader s) where
--     modifyEnv s m = local s m

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
instance (GChild c t x f k) => GChild c t (c1 :=>: x) f k where
    {-# INLINE gchild #-}
    gchild f (C x) = C <$> gchild @c @t f x
instance (forall (e::Type). GChild c t x f (e ':&&: k)) => GChild c t (E x) f k where
    {-# INLINE gchild #-}
    gchild f (E (x :: x (e ':&&: k))) = E <$> gchild @c @t @x @f @(e ':&&: k) f x
instance (TraverseChildConstraint (Ty x k) f, c (Ty x k) t f) => GChild c t (F x) f k where
    {-# INLINE gchild #-}
    gchild f (F x) = F <$> f x

class DispatchChild (b :: Bool) (c :: Type -> Type -> (Type->Type) -> Constraint) s t f where
    dispatchChild :: Applicative f => (forall a. (TraverseChildConstraint a f, c a t f) => a -> f a) -> s -> f s
instance DispatchChild 'False c s t f where
    {-# INLINE dispatchChild #-}
    dispatchChild _f s = pure s
instance (Split s k x, GChild c t (RepK k) f x, GenericK k x) => DispatchChild 'True c s t f where
    {-# INLINE dispatchChild #-}
    dispatchChild f s = fmap (toF @k) $ gchild @c @t f $ fromF @k s

    
type family Bot where Bot = Bot

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

type family CountM (t::v) :: Nat where
  CountM  (t a) = 'S (CountM t)
  CountM   t    = 'Z

-- don't use s here in case it has free type variables
type Interesting (s::Type) (a::Type) =  Fst (Interesting'Dispatch s a '[])
type Interesting'Dispatch s seen a = Interesting'Helper s (SplitN (CountM s) s) a seen
type family Interesting'Helper s (t::TyEnv) a seen  where
    Interesting'Helper s ('TyEnv l r) a seen = InterestingStep s (RepK l) r a seen


type family InterestingStep (s::Type) (f :: LoT k -> Type) (x :: LoT k) (seen::[Type]) (a::Type) where
    InterestingStep Char    _ _ seen a = '( 'False, seen)
    InterestingStep Double  _ _ seen a = '( 'False, seen)
    InterestingStep Float   _ _ seen a = '( 'False, seen)
    InterestingStep Int     _ _ seen a = '( 'False, seen)
    InterestingStep Integer _ _ seen a = '( 'False, seen)
    InterestingStep Bool _ _ seen a = '( 'False, seen)
    InterestingStep s f x seen a = Interesting' 'False f x seen a


type family Interesting' (b :: Bool) (m :: LoT k -> *) (x :: LoT k) (seen::[Type]) (a::Type) :: (Bool, [Type]) where
    Interesting' b (M1 _ m f) x seen a = Interesting' b f x seen a
    Interesting' b (l :*: r) x seen a = InterestingBranch' b (Interesting' b l x seen a) r x a
    Interesting' b (l :+: r) x seen a = InterestingBranch' b (Interesting' b l x seen a) r x a
    Interesting' b (F a) x seen v = InterestingRecurse b (Ty a x == v)  a x seen v
    Interesting' b (_ :=>: a) x seen v = Interesting' b a x seen v
    Interesting' b U1 _ seen _ = '( 'False, seen)

type family InterestingRecurse (v0 :: Bool) (v1::Bool) (a::Atom d Type) (x :: LoT d) (seen :: [Type]) (b::Type)  :: (Bool, [Type]) where
     InterestingRecurse _ 'True a x seen b = '( 'True, seen)
     InterestingRecurse 'True  _ a x seen b = InterestingRecurse' 'False a x (Ty a x ': seen) b
     InterestingRecurse _  _ a x seen b = InterestingRecurse' (Elem (Ty a x) seen) a x seen b
type family InterestingRecurse' (v1::Bool) (a::Atom d Type) (x :: LoT d) (seen :: [Type]) (b::Type)   :: (Bool, [Type])where
     InterestingRecurse' 'True a x seen b = '( 'False, seen)
     InterestingRecurse' 'False r x seen a = Interesting'Dispatch (Ty r x) a (Ty r x ': seen)
type family InterestingBranch' b0 b r x a where
    InterestingBranch' b0 '( 'True, ls) _ _ _ = '( 'True, ls)
    InterestingBranch' b0 '( 'False, ls) r x a = Interesting' b0 r x ls a


type family Elem a as where
    Elem a (a ': _) = 'True
    Elem a (_ ': as) = Elem a as
    Elem a '[] = 'False
type family Snd (k::(a, b)) :: b where
    Snd '(l, r) = r
type family Fst a where Fst '(l, r) = l

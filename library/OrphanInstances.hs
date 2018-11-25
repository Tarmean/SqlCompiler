{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module OrphanInstances where
import Generics.Kind

instance GenericK [] (a ':&&: 'LoT0) where
    type RepK [] = U1 :+: (F V0 :*: F ([] :$: V0))
instance GenericK Maybe (a ':&&: 'LoT0) where
    type RepK Maybe = U1 :+: F V0

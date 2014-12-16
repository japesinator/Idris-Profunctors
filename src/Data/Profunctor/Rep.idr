module Data.Profunctor.Rep

import Data.Morphisms
import Data.Profunctor

||| Profunctors for which an isomorphic (p d c ~~ d -> f c) Functor exists
class Profunctor p => Representable (p : Type -> Type -> Type) where
  ||| The isomorphic Functor
  Rep'       : Type -> Type
  ||| This is dark magic at the moment
  functorRep : Functor Rep'
  tabulate   : (d -> Rep' c) -> p d c
  rep        : p d c         -> (d -> Rep' c)

||| THe isomorphic Functor of a given Representable Profunctor
Rep : (p : Type -> Type -> Type) ->
      {default %instance i : Representable p} -> Type -> Type
Rep p = Rep' {p}

instance Monad m => Representable (Kleislimorphism m) where
  Rep'       = m
  functorRep = %instance
  tabulate   = Kleisli
  rep        = applyKleisli

instance Functor f => Representable (UpStarred f) where
  Rep'       = f
  functorRep = %instance
  tabulate   = UpStar
  rep        = runUpStar

||| Corepresentable is the dual of Representable
class Profunctor p => Corepresentable (p : Type -> Type -> Type) where
  ||| The isomorphic Functor (Functor is its own dual)
  Corep'       : Type -> Type
  ||| Dark magic
  functorCorep : Functor Corep'
  cotabulate   : (Corep' d -> c) -> p d c
  corep        : p d c           -> (Corep' d -> c)

||| The isomorphic Functor of a given Corepresentable Profunctor
Corep : (p : Type -> Type -> Type) ->
        {default %instance i : Corepresentable p} -> Type -> Type
Corep p = Corep' {p}

instance Functor f => Corepresentable (DownStarred f) where
  Corep'       = f
  functorCorep = %instance
  cotabulate   = DownStar
  corep        = runDownStar

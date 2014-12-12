module Data.Profunctor.Rep

import Data.Morphisms
import Data.Profunctor

class Profunctor p => Representable (p : Type -> Type -> Type) where
  Rep'       : Type -> Type
  functorRep : Functor Rep'
  tabulate   : (d -> Rep' c) -> p d c
  rep        : p d c         -> (d -> Rep' c)

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

class Profunctor p => Corepresentable (p : Type -> Type -> Type) where
  Corep'       : Type -> Type
  functorCorep : Functor Corep'
  cotabulate   : (Corep' d -> c) -> p d c
  corep        : p d c           -> (Corep' d -> c)

Corep : (p : Type -> Type -> Type) ->
        {default %instance i : Corepresentable p} -> Type -> Type
Corep p = Corep' {p}

instance Functor f => Corepresentable (DownStarred f) where
  Corep'       = f
  functorCorep = %instance
  cotabulate   = DownStar
  corep        = runDownStar

module Data.Profunctor.Rep

import Data.Morphisms
import Data.Profunctor

class Profunctor p => Representable (p : Type -> Type -> Type) where
  Rep'       : Type -> Type
  functorRep : Functor Rep'

  tabulate : (d -> Rep' c) -> p d c
  rep      : p d c         -> (d -> Rep' c)

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

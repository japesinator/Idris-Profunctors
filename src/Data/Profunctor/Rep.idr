module Data.Profunctor.Rep

import Control.Applicative.Const
import Control.Monad.Identity
import Data.Morphisms

import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Strong

public export
interface (Sieve p q, Strong p) => Representable p q where
  tabulate : (d -> q c) -> p d c

export
implementation Representable Morphism Identity where
  tabulate f = Mor $ runIdentity . f

export
implementation (Monad m, Functor m) => Representable (Kleislimorphism m) m where
  tabulate = Kleisli

export
implementation Functor f => Representable (UpStarred f) f where
  tabulate = UpStar

export
implementation Representable (Forgotten r) (Const r) where
  tabulate = Forget . (runConst .)

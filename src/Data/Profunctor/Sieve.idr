module Data.Profunctor.Sieve

import Control.Applicative.Const
import Control.Monad.Identity
import Data.Morphisms

import Data.Profunctor

public export
interface (Profunctor p, Functor f) => Sieve p f where
  sieve : p a b -> a -> f b

export
implementation Sieve Morphism Identity where
  sieve f = Id . applyMor f

export
implementation (Monad m, Functor m) => Sieve (Kleislimorphism m) m where
  sieve = applyKleisli

export
implementation Functor f => Sieve (UpStarred f) f where
  sieve = runUpStar

export
implementation Sieve (Forgotten r) (Const r) where
  sieve = (MkConst .) . runForget


module Data.Profunctor.Sieve

import Control.Applicative.Const
import Control.Monad.Identity
import Data.Morphisms

import Data.Profunctor
import Data.Profunctor.Comonad
import Data.Proxy

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

public export
interface (Profunctor p, Functor f) => Cosieve p f where
  cosieve : p a b -> f a -> b

export
implementation Cosieve Morphism Identity where
  cosieve m (Id a) = applyMor m a

export
implementation Functor w => Cosieve (Cokleislimorphism w) w where
  cosieve = runCokleisli

export
implementation Cosieve Tagged Proxy where
  cosieve (Tag a) _ = a

export
implementation Functor f => Cosieve (DownStarred f) f where
  cosieve = runDownStar


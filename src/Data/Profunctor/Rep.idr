module Data.Profunctor.Rep

import Control.Applicative.Const
import Control.Monad.Identity
import Data.Morphisms

import Data.Profunctor
import Data.Profunctor.Iso
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

export
tabulated : (Representable p f, Representable q g) => Iso (d -> f c) (d' -> g c') (p d c) (q d' c')
tabulated = iso tabulate sieve

export
firstRep : Representable p (Pair a) => p a b -> p (a, c) (b, c)
firstRep p = tabulate go
  where go : (a, c) -> Pair a (Pair b c)
        go (a, c) = (,c) <$> sieve p a

export
secondRep : Representable p (Pair c) => p a b -> p (c, a) (c, b)
secondRep p = tabulate go
  where go : (c, a) -> Pair c (Pair c b)
        go (c, a) = (c,) <$> sieve p a


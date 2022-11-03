module Data.Proxy

import Data.Contravariant

public export
record Proxy (a : Type) where
  constructor MkProxy

export
implementation Eq (Proxy a) where
  (==) _ _ = True

export
implementation Ord (Proxy a) where
  compare _ _ = EQ

export
implementation Semigroup (Proxy a) where
  (<+>) _ _ = MkProxy

export
implementation Monoid (Proxy a) where
  neutral = MkProxy

export
implementation Functor Proxy where
  map _ _ = MkProxy

export
implementation Applicative Proxy where
  pure _ = MkProxy
  (<*>) _ _ = MkProxy

export
implementation Monad Proxy where
  (>>=) _ _ = MkProxy
  join _ = MkProxy

export
implementation Foldable Proxy where
  foldr _ z _ = z

export
implementation Traversable Proxy where
  traverse _ _ = pure MkProxy

export
implementation Alternative Proxy where
  empty = MkProxy
  (<|>) _ _ = MkProxy

export
implementation Contravariant Proxy where
  contramap _ _ = MkProxy


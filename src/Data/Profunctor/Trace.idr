module Data.Profunctor.Trace

import Data.Profunctor

record Traced : (Type -> Type -> Type) -> Type where
  Trace : f a a -> Traced f

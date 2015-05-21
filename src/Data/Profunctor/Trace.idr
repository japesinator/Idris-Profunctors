module Data.Profunctor.Trace

import Data.Profunctor

||| Coend of Profunctor
record Traced (f : Type -> Type -> Type) where
  constructor Trace
  runTrace : f a a

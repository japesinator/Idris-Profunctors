module Data.Profunctor.Codensity

import Control.Category
import Data.Profunctor
import Data.Profunctor.Composition

||| The right Kan extenstion of a Profunctor
record Codense (p : Type -> Type -> Type) a b where
  constructor Codensity
  runCodensity : p x a -> p x b

instance Profunctor p => Profunctor (Codense p) where
  dimap ca bd f = Codensity $ rmap bd . runCodensity f . rmap ca
  lmap  ca    f = Codensity $           runCodensity f . rmap ca
  rmap     bd f = Codensity $ rmap bd . runCodensity f

instance Profunctor p => Functor (Codense p a) where
  map bd f = Codensity $ rmap bd . runCodensity f

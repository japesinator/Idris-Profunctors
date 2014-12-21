module Data.Profunctor.Ran

import Data.Profunctor
import Data.Profunctor.Composition
import Data.Profunctor.Monad

record Ran : (Type -> Type -> Type) -> (Type -> Type -> Type) ->
             Type -> Type -> Type where
  Run : (runRan : p x a -> q x b) -> Ran p q a b

instance ProfunctorFunctor (Ran p) where
  promap f _ _ (Run g) = Run $ (.) ((<-$->) f) g

instance (Profunctor p, Profunctor q) => Profunctor (Ran p q) where
  dimap ca bd f = Run $ rmap bd . runRan f . rmap ca
  lmap  ca    f = Run $           runRan f . rmap ca
  rmap     bd f = Run $ rmap bd . runRan f

instance Profunctor q => Functor (Ran p q a) where
  map bd f = Run (rmap bd . runRan f)

curryRan : (Procomposed p q -/-> r) -> p -/-> Ran q r
curryRan f a b p = Run $ \q => f a b (Procompose p q)

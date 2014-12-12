module Data.Profunctor.Composition

import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Closed
import Data.Profunctor.Monad
import Data.Profunctor.Rep

data Procomposed : (Type -> Type -> Type) -> (Type -> Type -> Type) ->
                   Type -> Type -> Type where
  Procompose : p x c -> q d x -> Procomposed p q d c

instance ProfunctorFunctor (Procomposed p) where
  promap f _ _ (Procompose p q) = Procompose p (f <-$-> q)

instance Category p => ProfunctorMonad (Procomposed p) where
  proreturn _ _                                 = Procompose id
  projoin   _ _ (Procompose p (Procompose q r)) = Procompose (p . q) r

procomposed : Category p => Procomposed p p a b -> p a b
procomposed (Procompose pxc pdx) = pxc . pdx

instance (Profunctor p, Profunctor q) => Profunctor (Procomposed p q) where
  dimap l r (Procompose f g) = Procompose (rmap r f) (lmap l g)
  lmap  l   (Procompose f g) = Procompose         f  (lmap l g)
  rmap    r (Procompose f g) = Procompose (rmap r f)         g

instance Profunctor p => Functor (Procomposed p q a) where
  map k (Procompose f g) = Procompose (rmap k f) g

record Rifted : (Type -> Type -> Type) -> (Type -> Type -> Type) ->
                Type -> Type -> Type where
  Rift : {x : Type} -> (runRift : p b x -> q a x) -> Rifted p q a b

instance ProfunctorFunctor (Rifted p) where
  promap f _ _ (Rift g) = Rift (((<-$->) f) . g)

instance (Profunctor p, Profunctor q) => Profunctor (Rifted p q) where
  dimap ca bd f = Rift (lmap ca . runRift f . lmap bd)
  lmap  ca    f = Rift (lmap ca . runRift f          )
  rmap     bd f = Rift (          runRift f . lmap bd)

instance Profunctor p => Functor (Rifted p q a) where
  map bd f = Rift (runRift f . lmap bd)

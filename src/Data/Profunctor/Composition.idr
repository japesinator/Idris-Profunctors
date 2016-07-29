module Data.Profunctor.Composition

import Control.Arrow
import Control.Category
import Data.Profunctor
import Data.Profunctor.Closed

%access public export

||| The composition of two Profunctors
data Procomposed : (Type -> Type -> Type) -> (Type -> Type -> Type) ->
                   Type -> Type -> Type where
  ||| Compose two Profunctors
  Procompose : {x,c,d : _} -> p x c -> q d x -> Procomposed p q d c

procomposed : Category p => Procomposed p p a b -> p a b
procomposed (Procompose pxc pdx) = pxc . pdx

implementation (Profunctor p, Profunctor q) => Profunctor (Procomposed p q) where
  dimap l r (Procompose f g) = Procompose (rmap r f) (lmap l g)
  lmap  l   (Procompose f g) = Procompose         f  (lmap l g)
  rmap    r (Procompose f g) = Procompose (rmap r f)         g

implementation Profunctor p => Functor (Procomposed p q a) where
  map k (Procompose f g) = Procompose (rmap k f) g

||| The right Kan lift of one Profunctor along another
record Rifted (p : Type -> Type -> Type) (q : Type -> Type -> Type) a b where
  constructor Rift
  runRift : p b x -> q a x

implementation (Profunctor p, Profunctor q) => Profunctor (Rifted p q) where
  dimap ca bd f = Rift $ lmap ca . runRift f . lmap bd
  lmap  ca    f = Rift $ lmap ca . runRift f
  rmap     bd f = Rift $           runRift f . lmap bd

implementation Profunctor p => Functor (Rifted p q a) where
  map bd f = Rift $ runRift f . lmap bd

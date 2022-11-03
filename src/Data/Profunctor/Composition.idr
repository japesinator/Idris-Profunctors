module Data.Profunctor.Composition

import Control.Arrow
import Control.Category
import Data.Profunctor
import Data.Profunctor.Closed
import Data.Profunctor.Choice
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Strong

||| The composition of two Profunctors
public export
data Procomposed : (Type -> Type -> Type) -> (Type -> Type -> Type) ->
                   Type -> Type -> Type where
  ||| Compose two Profunctors
  Procompose : {0 x,c,d : _} -> p x c -> q d x -> Procomposed p q d c

export
procomposed : Category p => Procomposed p p a b -> p a b
procomposed (Procompose pxc pdx) = pxc . pdx

export
implementation (Profunctor p, Profunctor q) => Profunctor (Procomposed p q) where
  dimap l r (Procompose f g) = Procompose (rmap r f) (lmap l g)
  lmap  l   (Procompose f g) = Procompose         f  (lmap l g)
  rmap    r (Procompose f g) = Procompose (rmap r f)         g

export
implementation Profunctor p => Functor (Procomposed p q a) where
  map k (Procompose f g) = Procompose (rmap k f) g

export
implementation (Strong p, Strong q) => Strong (Procomposed p q) where
  first' (Procompose x y) = Procompose (first' x) (first' y)
  second' (Procompose x y) = Procompose (second' x) (second' y)

export
implementation (Choice p, Choice q) => Choice (Procomposed p q) where
  left' (Procompose x y) = Procompose (left' x) (left' y)
  right' (Procompose x y) = Procompose (right' x) (right' y)

export
implementation (Closed p, Closed q) => Closed (Procomposed p q) where
  closed (Procompose x y) = Procompose (closed x) (closed y)

export
implementation (Sieve p f, Sieve q g) => Sieve (Procomposed p q) (g . f) using Functor.Compose where
  sieve (Procompose g f) d = sieve g <$> sieve f d

export
implementation (Representable p f, Representable q g) => Representable (Procomposed p q) (g . f) using Functor.Compose where
  tabulate f = Procompose (tabulate id) (tabulate f)

export
implementation (Cosieve p f, Cosieve q g) => Cosieve (Procomposed p q) (f . g) using Functor.Compose where
  cosieve (Procompose g f) d = cosieve g $ cosieve f <$> d

||| The right Kan lift of one Profunctor along another
public export
record Rifted (p : Type -> Type -> Type) (q : Type -> Type -> Type) a b where
  constructor Rift
  runRift : p b y -> q a y

export
implementation (Profunctor p, Profunctor q) => Profunctor (Rifted p q) where
  dimap ca bd f = Rift $ lmap ca . runRift f . lmap bd
  lmap  ca    f = Rift $ lmap ca . runRift f
  rmap     bd f = Rift $           runRift f . lmap bd

export
implementation Profunctor p => Functor (Rifted p q a) where
  map bd f = Rift $ runRift f . lmap bd

module Data.Profunctor.Monad

import Control.Category
import Control.Comonad

import Data.Profunctor
import Data.Profunctor.Cayley
import Data.Profunctor.Closed
import Data.Profunctor.Composition
import Data.Profunctor.Ran

public export
interface ProfunctorFunctor (0 t : (Type -> Type -> Type) -> Type -> Type -> Type) where
  promap : (forall a, b. p a b -> q a b) -> t p a b -> t q a b

export
implementation ProfunctorFunctor (Ran p) where
  promap f (Run g) = Run (f . g)

export
implementation ProfunctorFunctor (Rifted p) where
  promap f (Rift g) = Rift (f . g)

export
implementation ProfunctorFunctor Closure where
  promap f (Close p) = Close (f p)

export
implementation ProfunctorFunctor Environment where
  promap f (Environize l m r) = Environize l (f m) r

export
implementation Functor f => ProfunctorFunctor (Cayleyed f) where
  promap f (Cayley p) = Cayley (f <$> p)

export
implementation ProfunctorFunctor (Procomposed p) where
  promap f (Procompose p q) = Procompose p (f q)

public export
interface ProfunctorFunctor t => ProfunctorMonad t where
  propure : Profunctor p => p a b -> t p a b
  projoin : Profunctor p => t (t p) a b -> t p a b

export
implementation Category p => ProfunctorMonad (Procomposed p) where
  propure = Procompose id
  projoin (Procompose p (Procompose q r)) = Procompose (p . q) r

export
implementation (Functor f, Monad f) => ProfunctorMonad (Cayleyed f) where
  propure = Cayley . pure
  projoin (Cayley m) = Cayley $ m >>= runCayley 

public export
interface ProfunctorFunctor t => ProfunctorComonad t where
  proextract : Profunctor p => t p a b -> p a b
  produplicate : Profunctor p => t p a b -> t (t p) a b

export
implementation Comonad f => ProfunctorComonad (Cayleyed f) where
  proextract (Cayley f) = extract f
  produplicate (Cayley p) = Cayley (Cayley <$> duplicate p)


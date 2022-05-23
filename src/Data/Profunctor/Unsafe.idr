module Data.Profunctor.Unsafe

import Data.Morphisms
import Data.Profunctor

infixr 9 #.
infixl 8 .#

public export
interface Profunctor p => UnsafeProfunctor (p : Type -> Type -> Type) where
  ||| Map the second argument of a Profunctor covariantly with a function
  ||| which is assumed to be a cast
  (#.) : (b -> c) -> p a b -> p a c
  (#.) = rmap

  ||| Map the first argument of a Profunctor contravariantly with a function
  ||| which is assumed to be a cast
  (.#) : p b c -> (a -> b) -> p a c
  (.#) = flip lmap

export
implementation UnsafeProfunctor Morphism where
  (#.) = const believe_me
  (.#) = const . believe_me

export
implementation Monad m => UnsafeProfunctor (Kleislimorphism m) where
  (.#) = const . believe_me

export
implementation UnsafeProfunctor Tagged where
  (#.) = const believe_me
  (.#) = const . Tag . runTagged

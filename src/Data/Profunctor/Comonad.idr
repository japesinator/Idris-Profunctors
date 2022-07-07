module Data.Profunctor.Comonad

import Control.Arrow
import Control.Category
import Control.Comonad
import Data.Profunctor

export
implementation Comonad (Tagged a) where
  duplicate = Tag
  extract = runTagged

public export
record Cokleislimorphism (w : Type -> Type) a b where
  constructor Cokleisli
  runCokleisli : w a -> b

export
implementation Functor w => Profunctor (Cokleislimorphism w) where
  dimap f g (Cokleisli h) = Cokleisli $ g . h . map f

export
implementation Comonad w => Category (Cokleislimorphism w) where
  id = Cokleisli extract
  (Cokleisli f) . (Cokleisli g) = Cokleisli $ f =<= g

export
implementation Functor (Cokleislimorphism w a) where
  map f (Cokleisli g) = Cokleisli $ f . g

export
implementation Applicative (Cokleislimorphism w a) where
  pure = Cokleisli . const
  (Cokleisli f) <*> (Cokleisli a) = Cokleisli $ \w => f w $ a w

export
implementation Monad (Cokleislimorphism w a) where
  (Cokleisli k) >>= f = Cokleisli $ \w => runCokleisli (f $ k w) w

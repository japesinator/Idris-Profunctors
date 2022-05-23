module Data.Profunctor.Comonad

import Control.Arrow
import Control.Category
import Data.Profunctor

public export
interface Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a

  duplicate : w a -> w (w a)
  duplicate = extend id

  extend : (w a -> b) -> w a -> w b
  extend f = map f . duplicate

export
implementation Comonad (Tagged a) where
  duplicate = Tag
  extract = runTagged

infixr 1 =>>
export
(=>>) : Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

infixl 1 <<=
export
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

export
wfix : Comonad w => w (w a -> a) -> a
wfix w = extract w $ w =>> wfix

infixr 1 =<=
export
(=<=) : Comonad w => (w b -> c) -> (w a -> b) -> w a -> c
f =<= g = f . extend g

infixr 1 =>=
export
(=>=) : Comonad w => (w a -> b) -> (w b -> c) -> w a -> c
f =>= g = g . extend f

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

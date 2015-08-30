import Data.Profunctor

class Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a

  duplicate : w a -> w (w a)
  duplicate = extend id

  extend : (w a -> b) -> w a -> w b
  extend f = map f . duplicate

instance Comonad (Tagged a) where
  duplicate = Tag
  extract = runTagged

infixr 1 =>>
(=>>) : Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

infixl 1 <<=
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

wfix : Comonad w => w (w a -> a) -> a
wfix w = extract w $ w =>> wfix

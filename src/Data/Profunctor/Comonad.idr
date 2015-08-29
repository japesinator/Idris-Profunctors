import Data.Profunctor

class Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a

  duplicate : w a -> w (w a)
  duplicate = extend id

  extend : (w a -> b) -> w a -> w b
  extend f = map f . duplicate

instance Functor (Tagged a) where
  map f = Tag . f . runTagged

instance Comonad (Tagged a) where
  duplicate = Tag
  extract = runTagged

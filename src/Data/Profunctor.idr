module Data.Profunctor

import Control.Monad.Identity
import Control.Arrow
import Control.Category
import Data.Morphisms

%default total

||| Profunctors
||| @p The action of the Profunctor on pairs of objects
public export
interface Profunctor (0 p : Type -> Type -> Type) | p where
  ||| Map over both arguments
  |||
  ||| ````idris example
  ||| dimap reverse length (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  ||| Map over the first argument contravariantly
  |||
  ||| ````idris example
  ||| lmap reverse (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  lmap : (a -> b) -> p b c -> p a c
  lmap = flip dimap id

  ||| Map over the second argument covariantly
  |||
  ||| ````idris example
  ||| rmap length (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap id

export
implementation Monad m => Profunctor (Kleislimorphism m) where
  dimap f g (Kleisli h) = Kleisli $ map g . h . f

export
implementation Profunctor Morphism where
  dimap f g (Mor h) = Mor $ g . h . f

||| A method of attaching a phantom type as a "tag"
public export
record Tagged a b where
  constructor Tag
  runTagged : b

export
implementation Profunctor Tagged where
  lmap   = const $ Tag . runTagged
  rmap f = Tag . f . runTagged

export
implementation Functor (Tagged a) where
  map = rmap

-- UpStar
-- {{{

||| Lift a Functor into a Profunctor going forwards
|||
||| ````idris example
||| UpStar $ \x => Just $ isDigit x
||| ````
|||
public export
record UpStarred (f : Type -> Type) d c where
  constructor UpStar
  runUpStar : d -> f c

export
implementation Functor f => Profunctor (UpStarred f) where
  dimap ab cd (UpStar bfc) = UpStar $ \a => map cd $ bfc $ ab a

export
implementation Functor f => Functor (UpStarred f a) where
  map = rmap

export
implementation Applicative f => Applicative (UpStarred f a) where
  pure                        = UpStar . const . pure
  (UpStar ff) <*> (UpStar fx) = UpStar $ \a => ff a <*> fx a

export
implementation Alternative f => Alternative (UpStarred f a) where
  empty = UpStar $ const empty
  (UpStar fa) <|> (UpStar fb) = UpStar $ \x => (fa x) <|> (fb x)

export
implementation Monad f => Monad (UpStarred f a) where
  (UpStar m) >>= f = UpStar $ \e => m e >>= flip runUpStar e . f

-- }}}
-- DownStar
-- {{{

||| Lift a Functor into a Profunctor going backwards
|||
||| ````idris example
||| DownStar $ show
||| ````
|||
public export
record DownStarred (f : Type -> Type) d c where
  constructor DownStar
  runDownStar : f d -> c

export
implementation Functor f => Profunctor (DownStarred f) where
  dimap ab cd (DownStar fbc) = DownStar $ cd . fbc . map ab

export
implementation Functor (DownStarred f a) where
  map = (DownStar .) . (. runDownStar) . (.)

export
implementation Applicative (DownStarred f a) where
  pure                            = DownStar . const
  (DownStar ff) <*> (DownStar fx) = DownStar $ \a => ff a $ fx a

export
implementation Monad (DownStarred f a) where
  (DownStar m) >>= f = DownStar $ \x => runDownStar (f $ m x) x

-- }}}
-- Wrapped Arrows
-- {{{

||| Wrap an Arrow for use as a Profunctor
|||
||| ````idris example
||| WrapArrow $ arrow ((+) 1)
||| ````
|||
public export
record WrappedArrow (p : Type -> Type -> Type) a b where
  constructor WrapArrow
  unwrapArrow : p a b

export
implementation Category p => Category (WrappedArrow p) where
  (WrapArrow f) . (WrapArrow g) = WrapArrow $ f . g
  id                            = WrapArrow id

export
implementation Arrow p => Arrow (WrappedArrow p) where
  arrow                           = WrapArrow . arrow
  first                           = WrapArrow . first  . unwrapArrow
  second                          = WrapArrow . second . unwrapArrow
  (WrapArrow a) *** (WrapArrow b) = WrapArrow $ a *** b
  (WrapArrow a) &&& (WrapArrow b) = WrapArrow $ a &&& b

export
implementation Arrow p => Profunctor (WrappedArrow p) where
  lmap = (>>>) . arrow
  rmap = (.)   . arrow

-- }}}
-- Forget
-- {{{

||| Forget some information about a type
|||
||| ````idris example
||| Forget ((+) 1)
||| ````
|||
public export
record Forgotten r a b where
  constructor Forget
  runForget : a -> r

export
implementation Profunctor (Forgotten r) where
  dimap f _ (Forget k) = Forget $ k . f

export
implementation Functor (Forgotten r a) where
  map = const $ Forget . runForget

export
implementation Foldable (Forgotten r a) where
  foldr = const const

export
implementation Traversable (Forgotten r a) where
  traverse = const $ pure . Forget . runForget

public export
record Zipping a b where
  constructor MkZipping
  runZipping : a -> a -> b

export
implementation Profunctor Zipping where
  dimap f g (MkZipping h) = MkZipping $ \a1, a2 => g $ h (f a1) (f a2)
-- }}}

module Data.Profunctor

import Control.Arrow
import Control.Category
import Data.Morphisms

||| Profunctors
||| @p The action of the Profunctor on pairs of objects
class Profunctor (p : Type -> Type -> Type) where
  ||| Map over both arguments
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  ||| Map over the first argument contravariantly
  lmap : (a -> b) -> p b c -> p a c
  lmap f = dimap f id

  ||| Map over the second argument covariantly
  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap id

instance Monad m => Profunctor (Kleislimorphism m) where
  dimap f g (Kleisli h) = Kleisli (liftA g . h . f)

-- UpStar
-- {{{

||| Lift a Functor into a Profunctor going forwards
record UpStarred : (Type -> Type) -> (Type -> Type -> Type) where
  UpStar : (runUpStar : d -> f c) -> UpStarred f d c

instance Functor f => Profunctor (UpStarred f) where
  dimap ab cd (UpStar bfc) = UpStar (map cd . bfc . ab)

instance Functor f => Functor (UpStarred f a) where
  map = rmap

instance Applicative f => Applicative (UpStarred f a) where
  pure a                      = UpStar $ \_ => pure a
  (UpStar ff) <$> (UpStar fx) = UpStar $ \a => ff a <$> fx a

instance Monad f => Monad (UpStarred f a) where
  (UpStar m) >>= f = UpStar $ \e => do
    a <- m e
    runUpStar (f a) e

-- }}}
-- DownStar
-- {{{

||| Lift a Functor into a Profunctor going backwards
record DownStarred : (Type -> Type) -> (Type -> Type -> Type) where
  DownStar : (runDownStar : f d -> c) -> DownStarred f d c

instance Functor f => Profunctor (DownStarred f) where
  dimap ab cd (DownStar fbc) = DownStar (cd . fbc . map ab)

instance Functor (DownStarred f a) where
  map k (DownStar f) = DownStar (k . f)

instance Applicative (DownStarred f a) where
  pure a                          = DownStar $ \_ => a
  (DownStar ff) <$> (DownStar fx) = DownStar $ \a => ff a (fx a)

instance Monad (DownStarred f a) where
  (DownStar m) >>= f = DownStar $ \x => runDownStar (f (m x)) x

-- }}}
-- Wrapped Arrows
-- {{{

||| Wrap an Arrow for use as a Profunctor
record WrappedArrow : (Type -> Type -> Type) -> Type -> Type -> Type where
  WrapArrow : (unwrapArrow : p a b) -> WrappedArrow p a b

instance Category p => Category (WrappedArrow p) where
  (WrapArrow f) . (WrapArrow g) = WrapArrow (f . g)
  id                            = WrapArrow id

instance Arrow p => Arrow (WrappedArrow p) where
  arrow                           = WrapArrow . arrow
  first                           = WrapArrow . first  . unwrapArrow
  second                          = WrapArrow . second . unwrapArrow
  (WrapArrow a) *** (WrapArrow b) = WrapArrow (a *** b)
  (WrapArrow a) &&& (WrapArrow b) = WrapArrow (a &&& b)

instance Arrow p => Profunctor (WrappedArrow p) where
  lmap f a = arrow f >>> a
  rmap g a = arrow g .   a

-- }}}
-- Forget
-- {{{

||| Forget some information about a type
record Forgotten : Type -> Type -> Type -> Type where
  Forget : (runForget : a -> r) -> Forgotten r a b

instance Profunctor (Forgotten r) where
  dimap f _ (Forget k) = Forget (k . f)

instance Functor (Forgotten r a) where
  map f (Forget k) = Forget k

instance Foldable (Forgotten r a) where
  foldr _ z _ = z

instance Traversable (Forgotten r a) where
  traverse _ (Forget k) = pure (Forget k)

-- }}}
-- Strong
-- {{{

||| Generalized UpStar of a Strong Functor
class Profunctor p => Strong (p : Type -> Type -> Type) where
  first' : p a b -> p (a, c) (b, c)
  first' = dimap (\x => (snd x, fst x)) (\x => (snd x, fst x)) . second'

  second' : p a b -> p (c, a) (c, b)
  second' = dimap (\x => (snd x, fst x)) (\x => (snd x, fst x)) . first'

instance Monad m => Strong (Kleislimorphism m) where
  first'  (Kleisli f) = Kleisli $ \ac => do
    b <- f (fst ac)
    return (b, snd ac)
  second' (Kleisli f) = Kleisli $ \ca => do
    b <- f (snd ca)
    return (fst ca, b)

instance Functor m => Strong (UpStarred m) where
  first'  (UpStar f) = UpStar $ (\ac => map (\b' => (b', snd ac)) (f (fst ac)))
  second' (UpStar f) = UpStar $ (\ca => map (MkPair     (fst ca)) (f (snd ca)))

instance Arrow p => Strong (WrappedArrow p) where
  first'  (WrapArrow k) = WrapArrow (first  k)
  second' (WrapArrow k) = WrapArrow (second k)

instance Strong (Forgotten r) where
  first'  (Forget k) = Forget (k . fst)
  second' (Forget k) = Forget (k . snd)

-- }}}
-- Choice
-- {{{

class Profunctor p => Choice (p : Type -> Type -> Type) where
  left' : p a b -> p (Either a c) (Either b c)
  left' = dimap (either Right Left) (either Right Left) . right'

  right' : p a b -> p (Either c a) (Either c b)
  right' = dimap (either Right Left) (either Right Left) . left'

instance Monad m => Choice (Kleislimorphism m) where
  left'  f = Kleisli $ either (applyKleisli (f        >>> arrow Left))
                              (applyKleisli (arrow id >>> arrow Right))
  right' f = Kleisli $ either (applyKleisli (arrow id >>> arrow Left))
                              (applyKleisli (f        >>> arrow Right))

instance Applicative f => Choice (UpStarred f) where
  left'  (UpStar f) = UpStar $ either (map Left . f   ) (map Right . pure)
  right' (UpStar f) = UpStar $ either (map Left . pure) (map Right . f   )

-- #YOLO
instance Traversable w => Choice (DownStarred w) where
  left' (DownStar wab) = DownStar (either            Right Left
                                  . map wab
                                  . traverse (either Right Left))

instance Monoid r => Choice (Forgotten r) where
  left'  (Forget k) = Forget (either k               (const neutral))
  right' (Forget k) = Forget (either (const neutral) k              )

-- }}}

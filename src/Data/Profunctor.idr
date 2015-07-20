module Data.Profunctor

import Control.Arrow
import Control.Category
import Data.Morphisms

||| Profunctors
||| @p The action of the Profunctor on pairs of objects
class Profunctor (p : Type -> Type -> Type) where
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

instance Monad m => Profunctor (Kleislimorphism m) where
  dimap f g (Kleisli h) = Kleisli $ liftA g . h . f

||| An injective (->)
|||
||| ````idris example
||| believe_me : Arr a b
||| ````
|||
record Arr a b where
  constructor MkArr
  runArr : (a -> b)

instance Profunctor Arr where
  dimap f g (MkArr h) = MkArr $ g . h . f

||| A method of attaching a phantom type as a "tag"
record Tagged a b where
  constructor Tag
  runTagged : b

instance Profunctor Tagged where
  lmap   = const $ Tag . runTagged
  rmap f = Tag . f . runTagged

-- UpStar
-- {{{

||| Lift a Functor into a Profunctor going forwards
|||
||| ````idris example
||| UpStar $ \x => Just $ isDigit x
||| ````
|||
record UpStarred (f : Type -> Type) d c where
  constructor UpStar
  runUpStar : d -> f c

instance Functor f => Profunctor (UpStarred f) where
  dimap ab cd (UpStar bfc) = UpStar $ map cd . bfc . ab

instance Functor f => Functor (UpStarred f a) where
  map = rmap

instance Applicative f => Applicative (UpStarred f a) where
  pure                        = UpStar . const . pure
  (UpStar ff) <*> (UpStar fx) = UpStar $ \a => ff a <*> fx a

instance Monad f => Monad (UpStarred f a) where
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
record DownStarred (f : Type -> Type) d c where
  constructor DownStar
  runDownStar : f d -> c

instance Functor f => Profunctor (DownStarred f) where
  dimap ab cd (DownStar fbc) = DownStar $ cd . fbc . map ab

instance Functor (DownStarred f a) where
  map = (DownStar .) . (. runDownStar) . (.)

instance Applicative (DownStarred f a) where
  pure                            = DownStar . const
  (DownStar ff) <*> (DownStar fx) = DownStar $ \a => ff a $ fx a

instance Monad (DownStarred f a) where
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
record WrappedArrow (p : Type -> Type -> Type) a b where
  constructor WrapArrow
  unwrapArrow : p a b

instance Category p => Category (WrappedArrow p) where
  (WrapArrow f) . (WrapArrow g) = WrapArrow $ f . g
  id                            = WrapArrow id

instance Arrow p => Arrow (WrappedArrow p) where
  arrow                           = WrapArrow . arrow
  first                           = WrapArrow . first  . unwrapArrow
  second                          = WrapArrow . second . unwrapArrow
  (WrapArrow a) *** (WrapArrow b) = WrapArrow $ a *** b
  (WrapArrow a) &&& (WrapArrow b) = WrapArrow $ a &&& b

instance Arrow p => Profunctor (WrappedArrow p) where
  lmap f a = arrow f >>> a
  rmap g a = arrow g .   a

-- }}}
-- Forget
-- {{{

||| Forget some information about a type
|||
||| ````idris example
||| Forget ((+) 1)
||| ````
|||
record Forgotten r a b where
  constructor Forget
  runForget : a -> r

instance Profunctor (Forgotten r) where
  dimap f _ (Forget k) = Forget $ k . f

instance Functor (Forgotten r a) where
  map = const $ Forget . runForget

instance Foldable (Forgotten r a) where
  foldr = const const

instance Traversable (Forgotten r a) where
  traverse = const $ pure . Forget . runForget

-- }}}
-- Strong
-- {{{

||| Generalized UpStar of a Strong Functor
class Profunctor p => Strong (p : Type -> Type -> Type) where
  ||| Create a new Profunctor of tuples with first element from the original
  |||
  ||| ````idris example
  ||| first' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  first'  : p a b -> p (a, c) (b, c)
  first'  = dimap (\x => (snd x, fst x)) (\x => (snd x, fst x)) . second'

  ||| Create a new Profunctor of tuples with second element from the original
  |||
  ||| ````idris example
  ||| second' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  second' : p a b -> p (c, a) (c, b)
  second' = dimap (\x => (snd x, fst x)) (\x => (snd x, fst x)) . first'

instance Monad m => Strong (Kleislimorphism m) where
  first'  (Kleisli f) = Kleisli $ \ac => f (fst ac) >>= \b => pure (b, snd ac)
  second' (Kleisli f) = Kleisli $ \ca => f (snd ca) >>= pure . MkPair (fst ca)

instance Strong Arr where
  first'  (MkArr f) = MkArr $ \(a,c) => (f a, c)
  second' (MkArr f) = MkArr $ \(c,a) => (c, f a)

instance Functor m => Strong (UpStarred m) where
  first'  (UpStar f) = UpStar $ \ac => map (\b' => (b', snd ac)) $ f $ fst ac
  second' (UpStar f) = UpStar $ \ca => map (MkPair $    fst ca)  $ f $ snd ca

instance Arrow p => Strong (WrappedArrow p) where
  first'  = WrapArrow . first  . unwrapArrow
  second' = WrapArrow . second . unwrapArrow

instance Strong (Forgotten r) where
  first'  (Forget k) = Forget $ k . fst
  second' (Forget k) = Forget $ k . snd

-- }}}
-- Choice
-- {{{

||| Generalized DownStar of a Costrong Functor
class Profunctor p => Choice (p : Type -> Type -> Type) where
  ||| Like first' but with sum rather than product types
  |||
  ||| ````idris example
  ||| left' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  left' : p a b -> p (Either a c) (Either b c)
  left' = dimap (either Right Left) (either Right Left) . right'

  ||| Like second' but with sum rather than product types
  |||
  ||| ````idris example
  ||| right' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  right' : p a b -> p (Either c a) (Either c b)
  right' = dimap (either Right Left) (either Right Left) . left'

instance Monad m => Choice (Kleislimorphism m) where
  left'  f = Kleisli $ either (applyKleisli $ f        >>> arrow Left)
                              (applyKleisli $ arrow id >>> arrow Right)
  right' f = Kleisli $ either (applyKleisli $ arrow id >>> arrow Left)
                              (applyKleisli $ f        >>> arrow Right)

instance Choice Arr where
  left'  (MkArr f) = MkArr $ either (Left . f) Right
  right' (MkArr f) = MkArr $ either Left (Right . f)

instance Choice Tagged where
  left'  = Tag . Left  . runTagged
  right' = Tag . Right . runTagged

instance Applicative f => Choice (UpStarred f) where
  left'  (UpStar f) = UpStar $ either (map Left . f   ) (map Right . pure)
  right' (UpStar f) = UpStar $ either (map Left . pure) (map Right . f   )

instance Monoid r => Choice (Forgotten r) where
  left'  (Forget k) = Forget $ either k (const neutral)
  right' (Forget k) = Forget $ either (const neutral) k

-- }}}

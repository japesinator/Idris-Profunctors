module Data.Profunctor

import Control.Monad.Identity
import Control.Arrow
import Control.Category
import Data.Morphisms

%access public export

record Const (a : Type) (b : Type) where
  constructor MkConst
  runConst : a

Functor (Const m) where
  map _ (MkConst v) = MkConst v

Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst a) <*> (MkConst b) = MkConst (a <+> b)

||| Profunctors
||| @p The action of the Profunctor on pairs of objects
interface Profunctor (p : Type -> Type -> Type) where
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

implementation Monad m => Profunctor (Kleislimorphism m) where
  dimap f g (Kleisli h) = Kleisli $ \a => liftA g $ h $ f a

implementation Profunctor Morphism where
  dimap f g (Mor h) = Mor $ g . h . f

||| A method of attaching a phantom type as a "tag"
record Tagged a b where
  constructor Tag
  runTagged : b

implementation Profunctor Tagged where
  lmap   = const $ Tag . runTagged
  rmap f = Tag . f . runTagged

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
record UpStarred (f : Type -> Type) d c where
  constructor UpStar
  runUpStar : d -> f c

implementation Functor f => Profunctor (UpStarred f) where
  dimap ab cd (UpStar bfc) = UpStar $ \a => map cd $ bfc $ ab a

implementation Functor f => Functor (UpStarred f a) where
  map = rmap

implementation Applicative f => Applicative (UpStarred f a) where
  pure                        = UpStar . const . pure
  (UpStar ff) <*> (UpStar fx) = UpStar $ \a => ff a <*> fx a

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
record DownStarred (f : Type -> Type) d c where
  constructor DownStar
  runDownStar : f d -> c

implementation Functor f => Profunctor (DownStarred f) where
  dimap ab cd (DownStar fbc) = DownStar $ cd . fbc . map ab

implementation Functor (DownStarred f a) where
  map = (DownStar .) . (. runDownStar) . (.)

implementation Applicative (DownStarred f a) where
  pure                            = DownStar . const
  (DownStar ff) <*> (DownStar fx) = DownStar $ \a => ff a $ fx a

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
record WrappedArrow (p : Type -> Type -> Type) a b where
  constructor WrapArrow
  unwrapArrow : p a b

implementation Category p => Category (WrappedArrow p) where
  (WrapArrow f) . (WrapArrow g) = WrapArrow $ f . g
  id                            = WrapArrow id

implementation Arrow p => Arrow (WrappedArrow p) where
  arrow                           = WrapArrow . arrow
  first                           = WrapArrow . first  . unwrapArrow
  second                          = WrapArrow . second . unwrapArrow
  (WrapArrow a) *** (WrapArrow b) = WrapArrow $ a *** b
  (WrapArrow a) &&& (WrapArrow b) = WrapArrow $ a &&& b

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
record Forgotten r a b where
  constructor Forget
  runForget : a -> r

implementation Profunctor (Forgotten r) where
  dimap f _ (Forget k) = Forget $ k . f

implementation Functor (Forgotten r a) where
  map = const $ Forget . runForget

implementation Foldable (Forgotten r a) where
  foldr = const const

implementation Traversable (Forgotten r a) where
  traverse = const $ pure . Forget . runForget

-- }}}
-- Strong
-- {{{

||| Generalized UpStar of a Strong Functor
interface Profunctor p => Strong (p : Type -> Type -> Type) where
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

implementation Monad m => Strong (Kleislimorphism m) where
  first'  (Kleisli f) = Kleisli $ \ac => f (fst ac) >>= \b => pure (b, snd ac)
  second' (Kleisli f) = Kleisli $ \ca => f (snd ca) >>= pure . MkPair (fst ca)

implementation Strong Morphism where
  first'  (Mor f) = Mor $ \(a,c) => (f a, c)
  second' (Mor f) = Mor $ \(c,a) => (c, f a)

implementation Functor m => Strong (UpStarred m) where
  first'  (UpStar f) = UpStar $ \ac => map (\b' => (b', snd ac)) . f $ fst ac
  second' (UpStar f) = UpStar $ \ca => map (MkPair $    fst ca)  . f $ snd ca

implementation Arrow p => Strong (WrappedArrow p) where
  first'  = WrapArrow . first  . unwrapArrow
  second' = WrapArrow . second . unwrapArrow

implementation Strong (Forgotten r) where
  first'  (Forget k) = Forget $ k . fst
  second' (Forget k) = Forget $ k . snd

-- }}}
-- Choice
-- {{{

||| Generalized DownStar of a Costrong Functor
interface Profunctor p => Choice (p : Type -> Type -> Type) where
  ||| Like first' but with sum rather than product types
  |||
  ||| ````idris example
  ||| left' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  left' : p a b -> p (Either a c) (Either b c)
  left' = dimap mirror mirror . right'

  ||| Like second' but with sum rather than product types
  |||
  ||| ````idris example
  ||| right' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  right' : p a b -> p (Either c a) (Either c b)
  right' = dimap mirror mirror . left'

implementation Monad m => Choice (Kleislimorphism m) where
  left'  f = Kleisli $ either (applyKleisli       $ f        >>> arrow Left)
                              (applyKleisli       $ arrow id >>> arrow Right)
  right' f = Kleisli $ either (applyKleisli {f=m} $ arrow id >>> arrow Left)
                              (applyKleisli       $ f        >>> arrow Right)

implementation Choice Morphism where
  left'  (Mor f) = Mor $ either (Left . f) Right
  right' (Mor f) = Mor $ either Left (Right . f)

implementation Choice Tagged where
  left'  = Tag . Left  . runTagged
  right' = Tag . Right . runTagged

implementation Applicative f => Choice (UpStarred f) where
  left'  (UpStar f) = UpStar $ either (map Left . f   ) (map Right . pure)
  right' (UpStar f) = UpStar $ either (map Left . pure) (map Right . f   )

implementation Monoid r => Choice (Forgotten r) where
  left'  (Forget k) = Forget .      either k $ const neutral
  right' (Forget k) = Forget . flip either k $ const neutral

||| Profunctors that support polymorphic traversals
interface (Strong p, Choice p) => Wander (p : Type -> Type -> Type) where
  wander : ({f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t

Wander Morphism where
  wander t (Mor f) = Mor $ runIdentity . t (%implementation) (Id . f)

Applicative f => Wander (UpStarred f) where
  wander @{ap} t (UpStar f) = UpStar $ t ap f

Monoid r => Wander (Forgotten r) where
  wander t (Forget r) = Forget $ runConst . t (%implementation) (MkConst . r)

-- }}}

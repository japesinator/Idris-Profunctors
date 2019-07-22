module Data.Profunctor.Closed

import Control.Arrow
import Control.Category
import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Strong
import Data.Profunctor.Unsafe

%access public export

||| A Closed Profunctor that allows the closed structure to pass through
interface Profunctor p => Closed (p : Type -> Type -> Type) where
  ||| Pass the closed structure through the Profunctor
  |||
  ||| ````idris example
  ||| closed $ DownStar $ show
  ||| ````
  |||
  closed : {x : _} -> p a b -> p (x -> a) (x -> b)

implementation Closed Morphism where
  closed = Mor . (.) . applyMor

implementation Functor f => Closed (DownStarred f) where
  closed (DownStar fab) = DownStar $ \fxa,x => fab $ map (\f => f x) fxa

implementation Monoid r => Closed (Forgotten r) where
  closed = const . Forget $ const neutral

Closed Zipping where
  closed (MkZipping f) = MkZipping $ \f1, f2, x => f (f1 x) (f2 x)

||| Closure adjoins a Closed structure to any Profunctor
record Closure (p : Type -> Type -> Type) a b where
  ||| Adjoin a closed-structured Profunctor to a profunctor
  |||
  ||| ````idris example
  ||| Close $ closed $ DownStar $ show
  ||| ````
  |||
  constructor Close
  runClosure : p (x -> a) (x -> b)

hither : (s -> (a,b)) -> (s -> a, s -> b)
hither h = (fst . h, snd . h)

yon : (s -> a, s -> b) -> s -> (a,b)
yon h s = (fst h s, snd h s)

implementation Profunctor p => Profunctor (Closure p) where
  dimap f g (Close p) = Close $ dimap ((.) f) ((.) g) p
  lmap  f   (Close p) = Close $ lmap  ((.) f)         p
  rmap    g (Close p) = Close $ rmap          ((.) g) p

implementation UnsafeProfunctor p => UnsafeProfunctor (Closure p) where
  w         #. (Close p) = Close $ ((.) w) #. p
  (Close p) .# w         = Close $ p       .# ((.) w)

implementation Strong p => Strong (Closure p) where
  first'   (Close p) = Close $ dimap hither yon $ first' p
  second'  (Close p) = Close $ dimap hither yon $ second' p

implementation Profunctor p => Functor (Closure p a) where
  map = rmap

close : Closed p => {a,b : Type} -> ({a',b' : Type} -> p a' b' -> q a' b') ->
                                                       p a b -> (Closure q) a b
close f p = Close {x=believe_me p} . f $ closed p

||| Environment is left adjoint to Closure
data Environment : (Type -> Type -> Type) -> Type -> Type -> Type where
  ||| Convert a Profunctor to an Environment
  |||
  ||| ````idris example
  ||| Environize $ Kleisli $ \x => Just $ reverse x
  ||| ````
  |||
  Environize : ((z -> y) -> b) -> p x y -> (a -> z -> x) -> Environment p a b

implementation Profunctor p => Profunctor (Environment p) where
  dimap f g (Environize l m r) = Environize (g . l) m (r . f)
  lmap  f   (Environize l m r) = Environize l       m (r . f)
  rmap    g (Environize l m r) = Environize (g . l) m r

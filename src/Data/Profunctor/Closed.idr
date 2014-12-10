module Data.Profunctor.Closed

import Data.Profunctor
import Data.Profunctor.Monad

class Profunctor p => Closed (p : Type -> Type -> Type) where
  closed : p a b -> p (x -> a) (x -> b)

instance Functor f => Closed (DownStarred f) where
  closed (DownStar fab) = DownStar $ \fxa,x => fab (map (\f => f x) fxa)

instance Monoid r => Closed (Forgotten r) where
  closed _ = Forget $ \_ => neutral

record Closure : (Type -> Type -> Type) -> Type -> Type -> Type where
  Close : (runClosure : p (x -> a) (x -> b)) -> Closure p a b

hither : (s -> (a,b)) -> (s -> a, s -> b)
hither h = (fst . h, snd . h)

yon : (s -> a, s -> b) -> s -> (a,b)
yon h s = (fst h s, snd h s)

instance Profunctor p => Profunctor (Closure p) where
  dimap f g (Close p) = Close $ dimap ((.) f) ((.) g) p

instance ProfunctorFunctor Closure where
  promap f _ _ (Close p) = Close (f <-$-> p)

instance Strong p => Strong (Closure p) where
  first'  (Close p) = Close $ dimap hither yon $ first' p

instance Profunctor p => Functor (Closure p a) where
  map = rmap

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

data Environment : (Type -> Type -> Type) -> Type -> Type -> Type where
  Environize : ((z -> y) -> b) -> p x y -> (a -> z -> x) -> Environment p a b

instance Profunctor p => Profunctor (Environment p) where
  dimap f g (Environize l m r) = Environize (g . l) m (r . f)
  lmap  f   (Environize l m r) = Environize l       m (r . f)
  rmap    g (Environize l m r) = Environize (g . l) m r

instance ProfunctorFunctor Environment where
  promap f _ _ (Environize l m r) = Environize l (f <-$-> m) r

instance ProfunctorMonad Environment where
  proreturn _ _ p =
    Environize (\x => x ())                  p const
  projoin   _ _ (Environize l (Environize m n o) p) =
    Environize ((\zr => l (m . zr)) . curry) n (\a,(b,c) => o (p a b) c)

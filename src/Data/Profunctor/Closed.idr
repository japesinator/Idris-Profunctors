module Data.Profunctor.Closed

import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad

class Profunctor p => Closed (p : Type -> Type -> Type) where
  closed : p a b -> p (x -> a) (x -> b)

instance Functor f => Closed (DownStarred f) where
  closed (DownStar fab) = DownStar $ \fxa,x => fab (map (\f => f x) fxa)

instance Monoid r => Closed (Forgotten r) where
  closed _ = Forget $ \_ => neutral

module Data.Profunctor.Tambara

import Data.Profunctor
import Data.Profunctor.Monad

data Tambarred : {c : Type} -> (Type -> Type -> Type) ->
                 Type -> Type -> Type where
  Tambara : p (Pair a c) (Pair b c) -> Tambarred {c} p a b

runTambara : Tambarred {c} p a b -> p (Pair a c) (Pair b c)
runTambara (Tambara p) = p

mapFst : (a -> b) -> (a, c) -> (b,   c)
mapFst   f           (a, b) =  (f a, b)

instance Profunctor p => Profunctor (Tambarred {c} p) where
  dimap f g (Tambara p) = Tambara $ dimap (mapFst f) (mapFst g) p

instance Category p => Category (Tambarred {c} p) where
  id                        = Tambara id
  (Tambara p) . (Tambara q) = Tambara (p . q)

swap : (a,b) -> (b,a)
swap   (x,y) =  (y,x)

go : ((a,b),c) -> ((a,c),b)
go   ((x,y),z) =  ((x,z),y)

instance Arrow p => Arrow (Tambarred {c} p) where
  arrow          f  = Tambara $ first $ arrow f
  first (Tambara f) = Tambara (arrow go . first f . arrow go)
  second         f  = arrow swap >>> first f >>> arrow swap
  f      ***     g  = first f >>> second g
  f      &&&     g  = arrow (\b => (b,b)) >>> f *** g

instance ProfunctorFunctor (Tambarred {c}) where
  promap f _ _ (Tambara p) = Tambara $ f <-$-> p

hither : (Either y z, s) -> Either (y, s) (z, s)
hither   (Left   y,   s) =  Left   (y, s)
hither   (Right    z, s) =  Right         (z, s)

yon : Either (y, s) (z, s) -> (Either y z, s)
yon  (Left   (y, s))        = (Left   y,   s)
yon  (Right         (z, s)) = (Right    z, s)

instance Choice p => Choice (Tambarred {c} p) where
  left' (Tambara p) = Tambara $ dimap hither yon $ left' p

instance Profunctor p => Functor (Tambarred {c} p a) where
  map = rmap

instance (Profunctor p, Arrow p) => Applicative (Tambarred {c} p a) where
  pure x  = arrow (const x)
  f <$> g = arrow (uncurry id) . (f &&& g)

module Data.Profunctor.Traversal.Index

import Data.SortedMap
import Data.SortedSet
import Data.Profunctor
import Data.Profunctor.Wander
import Data.Profunctor.Traversal

%default total

public export
interface Wander p => Index (0 p : Type -> Type -> Type) (0 m : Type) (0 a : Type) (0 b : Type) | m where
  ix : a -> Traversal' {p} m b

export
Wander p => Index p (Maybe a) () a where
  ix () = traversed

export
(Wander p, Ord k) => Index p (SortedMap k v) k v where
  ix k = wander $ \coalg, m => maybe (pure m) (map (\v => insert k v m) . coalg) (lookup k m) 

export
(Wander p, Ord a) => Index p (SortedSet a) a () where
  ix x = wander $ \_ => pure . SortedSet.insert x  

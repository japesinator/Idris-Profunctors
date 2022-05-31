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
  -- magical f1 
  ix k = wander $ \coalg, m => maybe (pure {f=f1} m) (map {f=f1} (\v => insert k v m) . coalg) (lookup k m) 

export
(Wander p, Ord a) => Index p (SortedSet a) a () where
  -- magical f1 
  ix x = wander $ \_ => pure {f=f1} . SortedSet.insert x  

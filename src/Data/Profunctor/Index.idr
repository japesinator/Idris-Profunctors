module Data.Profunctor.Index

import Data.SortedMap
import Data.SortedSet
import Data.Profunctor
import Data.Profunctor.Traversal

%default total
%access public export

interface Wander p => Index (p : Type -> Type -> Type) (m : Type) (a : Type) (b : Type) where
  ix : a -> Traversal' {p} m b

(Wander p, Ord k) => Index p (SortedMap k v) k v where
  -- magical f1 
  ix k = wander $ \coalg, m => maybe (pure {f=f1} m) (map {f=f1} (\v => insert k v m) . coalg) (lookup k m) 

(Wander p, Ord a) => Index p (SortedSet a) a () where
  -- magical f1 
  ix x = wander $ \coalg => pure {f=f1} . SortedSet.insert x  
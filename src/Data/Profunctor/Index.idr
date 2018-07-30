module Data.Profunctor.Index

import Data.SortedMap
import Data.Profunctor
import Data.Profunctor.Traversal

%default total
%access public export

interface Wander p => Index (p : Type -> Type -> Type) (m : Type) (a : Type) (b : Type) where
  ix : a -> Traversal' {p} m b

Ord k => Index Arr (SortedMap k v) k v where
  -- magical f1 
  ix k = wander $ \coalg, m => maybe (pure {f=f1} m) (map {f=f1} (\v => insert k v m) . coalg) (lookup k m) 

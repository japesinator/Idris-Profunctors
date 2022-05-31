module Data.Profunctor.Traversal.Index

import Data.SortedMap
import Data.SortedSet
import Data.Profunctor
import Data.Profunctor.Iso
import Data.Profunctor.Traversal
import Data.Profunctor.Wander

%default total

public export
interface Index (0 p : Type -> Type -> Type) (0 m : Type) (0 a : Type) (0 b : Type) | m where
  ix : a -> Traversal' {p} m b

export
Index p (Maybe a) () a where
  ix () = traversed

export
Ord k => Index p (SortedMap k v) k v where
  ix k = wander $ \coalg, m => maybe (pure m) (map (\v => insert k v m) . coalg) (lookup k m)

export
Ord a => Index p (SortedSet a) a () where
  ix x = wander $ \_ => pure . SortedSet.insert x

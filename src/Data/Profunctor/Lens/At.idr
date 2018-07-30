module Data.Profunctor.Lens.At

import Data.SortedMap
import Data.Profunctor
import Data.Profunctor.Lens
import Data.Profunctor.Index

%default total
%access public export

interface (Lensing p, Index p m a b) => At (p : Type -> Type -> Type) (m : Type) (a : Type) (b : Type) where
  at : a -> Lens' {p} m (Maybe b)

Ord k => At Arr (SortedMap k v) k v where
  at k = lens (lookup k) (\m => maybe (delete k m) (\v => insert k v m))

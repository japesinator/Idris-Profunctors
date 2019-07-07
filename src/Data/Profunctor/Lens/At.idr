module Data.Profunctor.Lens.At

import Data.Morphisms
import Data.SortedMap
import Data.SortedSet
import Data.Profunctor
import Data.Profunctor.Lens
import Data.Profunctor.Traversal.Index

%default total
%access public export

||| Allows adding and deleting elements from "container-like" types
interface (Lensing p, Index p m a b) => At (p : Type -> Type -> Type) (m : Type) (a : Type) (b : Type) | m where
  at : a -> Lens' {p} m (Maybe b)

(Wander p, Lensing p) => At p (Maybe a) () a where
  at () = id  

(Wander p, Lensing p, Ord k) => At p (SortedMap k v) k v where
  at k = lens (lookup k) (\m => maybe (delete k m) (\v => insert k v m))

(Wander p, Lensing p, Ord a) => At p (SortedSet a) a () where
  at x = lens get (flip update)
    where
      get xs = if contains x xs then Just () else Nothing
      update Nothing = delete x
      update (Just _) = insert x  

sans : At Morphism m a b => a -> m -> m
sans {m} k = at {p=Morphism} {m} k .~ Nothing 

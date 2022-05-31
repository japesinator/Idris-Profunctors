module Data.Profunctor.Lens.At

import Data.Morphisms
import Data.SortedMap
import Data.SortedSet
import Data.Profunctor
import Data.Profunctor.Wander
import Data.Profunctor.Lens
import Data.Profunctor.Traversal.Index

%default total

||| Allows adding and deleting elements from "container-like" types
public export
interface Index p m a b => At (0 p : Type -> Type -> Type) (0 m : Type) (0 a : Type) (0 b : Type) | m where
  at : a -> Lens' {p} m (Maybe b)

export
At p (Maybe a) () a where
  at () = id

export
Ord k => At p (SortedMap k v) k v where
  at k = lens (lookup k) (\m => maybe (delete k m) (\v => insert k v m))

export
Ord a => At p (SortedSet a) a () where
  at x = lens get (flip update)
    where
      get : SortedSet a -> Maybe ()
      get xs = if contains x xs then Just () else Nothing
      update : Maybe () -> SortedSet a -> SortedSet a
      update Nothing = delete x
      update (Just _) = insert x

export
sans : At Morphism m a b => a -> m -> m
sans {m} k = at {p=Morphism} {m} k .~ Nothing 

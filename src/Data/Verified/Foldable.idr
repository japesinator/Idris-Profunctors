module Data.Verified.Foldable

%default total

public export
interface Foldable t => FoldableV t where
  toListNeutralL : (f : r -> a -> r) -> (z : r) -> (fo : t a) -> foldl f z fo = foldl f z (Prelude.toList fo)
  toListNeutralR : (f : a -> r -> r) -> (z : r) -> (fo : t a) -> foldr f z fo = foldr f z (Prelude.toList fo)


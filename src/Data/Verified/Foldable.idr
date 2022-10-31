module Data.Verified.Foldable

%default total

public export
interface Foldable t => FoldableV t where
  toListNeutralL : (f : r -> a -> r) -> (z : r) -> (fo : t a) -> foldl f z fo = foldl f z (Prelude.toList fo)
  toListNeutralR : (f : a -> r -> r) -> (z : r) -> (fo : t a) -> foldr f z fo = foldr f z (Prelude.toList fo)

export
implementation FoldableV Maybe where
  toListNeutralL f z Nothing  = Refl
  toListNeutralL f z (Just x) = Refl
  toListNeutralR f z Nothing  = Refl
  toListNeutralR f z (Just x) = Refl

export
implementation FoldableV (Either e) where
  toListNeutralL f z (Left x)  = Refl
  toListNeutralL f z (Right x) = Refl
  toListNeutralR f z (Left x)  = Refl
  toListNeutralR f z (Right x) = Refl

export
implementation FoldableV List where
  toListNeutralL f z fo = Refl
  toListNeutralR f z fo = Refl


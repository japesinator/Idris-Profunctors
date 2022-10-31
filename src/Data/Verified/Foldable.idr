module Data.Verified.Foldable

import Control.Applicative.Const
import Data.List1
import Data.Validated
import Text.Bounded

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

export
implementation FoldableV (Const a) where
  toListNeutralL f z xs = Refl
  toListNeutralR f z xs = Refl

export
implementation FoldableV List1 where
  toListNeutralL f z (x ::: xs) = Refl
  toListNeutralR f z (x ::: xs) = Refl

export
implementation FoldableV (Validated e) where
  toListNeutralL f z (Valid x) = Refl
  toListNeutralL f z (Invalid _) = Refl
  toListNeutralR f z (Valid x) = Refl
  toListNeutralR f z (Invalid _) = Refl

export
implementation FoldableV WithBounds where
  toListNeutralL f z xs = Refl
  toListNeutralR f z xs = Refl

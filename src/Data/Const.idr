module Data.Const

%default total
%access public export

record Const a b where
  constructor MkConst
  runConst : a

Functor (Const m) where
  map _ (MkConst v) = MkConst v

Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst a) <*> (MkConst b) = MkConst (a <+> b)

Foldable (Const a) where
  foldr _ x _ = x
  foldl _ x _ = x

Traversable (Const a) where
  traverse _ (MkConst x) = pure $ MkConst x
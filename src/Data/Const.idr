module Data.Const

%default total

public export
record Const a b where
  constructor MkConst
  runConst : a

export
Functor (Const m) where
  map _ (MkConst v) = MkConst v

export
Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst a) <*> (MkConst b) = MkConst (a <+> b)

export
Foldable (Const a) where
  foldr _ x _ = x
  foldl _ x _ = x

export
Traversable (Const a) where
  traverse _ (MkConst x) = pure $ MkConst x

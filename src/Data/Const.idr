module Data.Const

import Control.Applicative.Const

%default total

export
Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst a) <*> (MkConst b) = MkConst (a <+> b)

export
Traversable (Const a) where
  traverse _ (MkConst x) = pure $ MkConst x

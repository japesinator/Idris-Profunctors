module Data.Const

%default total
%access public export

record Const (a : Type) (b : Type) where
  constructor MkConst
  runConst : a

Functor (Const m) where
  map _ (MkConst v) = MkConst v

Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst a) <*> (MkConst b) = MkConst (a <+> b)
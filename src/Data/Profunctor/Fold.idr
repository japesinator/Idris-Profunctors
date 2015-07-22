module Data.Profunctor.Fold

import Data.Profunctor

data SnocList a = Snoc (SnocList a) a | Nil

data L a b = MkL (r -> b) (r -> a -> r) r

unfoldL : (s -> (b, a -> s)) -> s -> L a b
unfoldL f = MkL (fst . f) (snd . f)

runL : Foldable t => L a b -> t a -> b
runL (MkL r i n) = r . foldl i n

instance Profunctor L where
  dimap f g (MkL k h z) = MkL (g . k) ((. f) . h) z
  rmap    g (MkL k h z) = MkL (g . k) h           z
  lmap  f   (MkL k h z) = MkL k       ((. f) . h) z

instance Functor (L a) where
  map f (MkL k h z) = MkL (f . k) h z

instance Applicative (L a) where
  pure b = MkL (const b) (const $ const ()) ()
  (MkL f u y) <*> (MkL a v z) =
    MkL (uncurry $ (. a) . f) (\(x, y), b => (u x b, v y b)) (y, z)

instance Monad (L a) where
  m >>= f = MkL ((. f) . flip runL) ((. pure) . (++)) [] <*> m

data R a b = MkR (r -> b) (a -> r -> r) r

runR : Foldable t => R a b -> t a -> b
runR (MkR r i n) = r . foldr i n

instance Profunctor R where
  dimap f g (MkR k h z) = MkR (g . k) (h . f) z
  rmap    g (MkR k h z) = MkR (g . k) h       z
  lmap  f   (MkR k h z) = MkR k       (h . f) z

instance Functor (R a) where
  map f (MkR k h z) = MkR (f . k) h z

instance Applicative (R a) where
  pure b = MkR (const b) (const $ const ()) ()
  (MkR f u y) <*> (MkR a v z) =
    MkR (uncurry $ (. a) . f) (\b, (x, y) => (u b x, v b y)) (y, z)

instance Monad (R a) where
  m >>= f = MkR ((. f) . flip runR) (::) [] <*> m

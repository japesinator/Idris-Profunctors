module Data.Profunctor.Fold

import Control.Algebra
import Data.Profunctor
import Data.SortedSet

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
  map = rmap

instance Applicative (L a) where
  pure b = MkL (const b) (const $ const ()) ()
  (MkL f u y) <*> (MkL a v z) = MkL (uncurry $ (. a) . f)
                                    (\(x, y), b => (u x b, v y b))
                                    (y, z)

instance Monad (L a) where
  m >>= f = MkL ((. f) . flip runL) ((. pure) . (++)) [] <*> m

instance Semigroup m => Semigroup (L a m) where
  (<+>) = liftA2 (<+>)

instance Monoid m => Monoid (L a m) where
  neutral = pure neutral

instance Group m => Group (L a m) where
  inverse = map inverse

instance AbelianGroup m => AbelianGroup (L a m)

instance Ring m => Ring (L a m) where
  (<.>) = liftA2 (<.>)

instance RingWithUnity m => RingWithUnity (L a m) where
  unity = pure unity

-- The `Field` instance won't type check, but it should exist

instance Num n => Num (L a n) where
  (+)         = liftA2 (+)
  (-)         = liftA2 (-)
  (*)         = liftA2 (*)
  abs         = map abs
  fromInteger = pure . fromInteger

instance Neg n => Neg (L a n) where
  negate = map negate

length : L a Nat
length = MkL id (const . S) Z

null : L a Bool
null = MkL id (const $ const False) True

find : (a -> Bool) -> L a (Maybe a)
find p = MkL id step Nothing where
  step x a = case x of Nothing => if p a then Just a else Nothing
                       _       => x

index : Nat -> L a (Maybe a)
index i = MkL done step (Left 0) where
  step x = case x of Left j => if i == j then Right else const . Left $ S j
                     _      => const x
  done : Either Nat a -> Maybe a
  done = either (const Nothing) Just

nub : Eq a => L a (List a)
nub = MkL (flip snd []) step ([], id) where
  step : (List a, List a -> List a) -> a -> (List a, List a -> List a)
  step (k, r) i = if elem i k then (k, r) else (i :: k, r . (i ::))

fastNub : {a : Type} -> Ord a => L a (List a)
fastNub {a} = MkL (flip snd $ the (List a) [])
                  (\(s, r), a => if contains a s then (s, r)
                                                 else (insert a s, r . (a ::)))
                  (the (SortedSet a) empty, id)

sort : Ord a => L a (List a)
sort = MkL id (flip $ merge . pure) [] where
  merge : Ord a => List a -> List a -> List a
  merge xs [] = xs
  merge [] ys = ys
  merge (x :: xs) (y :: ys) = if x < y then x :: merge xs (y :: ys)
                                       else y :: merge (x :: xs) ys

L1 : (a -> a -> a) -> L a (Lazy (Maybe a))
L1 s = MkL Delay (\m => Just . case m of Just x => s x; _ => id) Nothing

first : L a (Maybe a)
first = map Force $ L1 const

last : L a (Maybe a)
last = map Force . L1 $ flip const

maximum : Ord a => L a (Maybe a)
maximum = map Force $ L1 max

minimum : Ord a => L a (Maybe a)
minimum = map Force $ L1 min

data R a b = MkR (r -> b) (a -> r -> r) r

runR : Foldable t => R a b -> t a -> b
runR (MkR r i n) = r . foldr i n

instance Profunctor R where
  dimap f g (MkR k h z) = MkR (g . k) (h . f) z
  rmap    g (MkR k h z) = MkR (g . k) h       z
  lmap  f   (MkR k h z) = MkR k       (h . f) z

instance Functor (R a) where
  map = rmap

instance Applicative (R a) where
  pure b = MkR (const b) (const $ const ()) ()
  (MkR f u y) <*> (MkR a v z) = MkR (uncurry $ (. a) . f)
                                    (\b, (x, y) => (u b x, v b y))
                                    (y, z)

instance Monad (R a) where
  m >>= f = MkR ((. f) . flip runR) (::) [] <*> m

instance Semigroup m => Semigroup (R a m) where
  (<+>) = liftA2 (<+>)

instance Monoid m => Monoid (R a m) where
  neutral = pure neutral

instance Num n => Num (R a n) where
  (+)         = liftA2 (+)
  (-)         = liftA2 (-)
  (*)         = liftA2 (*)
  abs         = map abs
  fromInteger = pure . fromInteger

instance Neg n => Neg (R a n) where
  negate = map negate

instance Group m => Group (R a m) where
  inverse = map inverse

instance AbelianGroup m => AbelianGroup (R a m)

instance Ring m => Ring (R a m) where
  (<.>) = liftA2 (<.>)

instance RingWithUnity m => RingWithUnity (R a m) where
  unity = pure unity

lr : L a b -> R a b
lr (MkL r i n) = MkR r (flip i) n

rl : R a b -> L a b
rl (MkR r i n) = MkL r (flip i) n

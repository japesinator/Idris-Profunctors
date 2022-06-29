module Data.Profunctor.Fold

import Control.Algebra
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Prism
import Data.SortedSet

liftA2 : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x y = f <$> x <*> y

||| A leftwards fold
public export
data L a b = MkL (r -> b) (r -> a -> r) r

||| Turn a finalization function, an accumulation function, and an initial value
||| into an `L`
export
unfoldL : (s -> (b, a -> s)) -> s -> L a b
unfoldL f = MkL (fst . f) (snd . f)

||| Run an `L` on a `Foldable` container
export
runL : Foldable t => L a b -> t a -> b
runL (MkL k h z) = k . foldl h z

||| Run an `L` on a `Foldable` container, accumulating results
export
scanL : L a b -> List a -> List b
scanL (MkL k _ z) []      = pure $ k z
scanL (MkL k h z) (x::xs) = k (h z x) :: scanL (MkL k h (h z x)) xs

export
implementation Profunctor L where
  dimap f g (MkL k h z) = MkL (g . k) ((. f) . h) z
  rmap    g (MkL k h z) = MkL (g . k) h           z
  lmap  f   (MkL k h z) = MkL k       ((. f) . h) z

export
implementation Choice L where
  left' (MkL {r} k h z) = MkL (\e => case e of Left a  => Left $ k a
                                               Right b => Right b)
                              step
                              (Left z) where
    step : Either r c -> Either a c -> Either r c
    step (Left x)  (Left y)  = Left $ h x y
    step (Right c) _         = Right c
    step _         (Right c) = Right c
  right' (MkL {r} k h z) = MkL (\e => case e of Right a => Right $ k a
                                                Left b  => Left b)
                               step
                               (Right z) where
    step : Either c r -> Either c a -> Either c r
    step (Right x) (Right y) = Right $ h x y
    step (Left c)  _         = Left c
    step _         (Left c)  = Left c

export
implementation Prisming L where
  costrength = rmap (either id id) . right'

export
implementation Functor (L a) where
  map = rmap

export
implementation Applicative (L a) where
  pure b = MkL (const b) (const $ const ()) ()
  (MkL f u y) <*> (MkL a v z) = MkL (uncurry $ (. a) . f)
                                    (\(x, y), b => (u x b, v y b))
                                    (y, z)

export
implementation Monad (L a) where
  m >>= f = MkL ((. f) . flip runL) ((. pure) . (++)) [] <*> m

export
implementation Semigroup m => Semigroup (L a m) where
  x <+> y = (<+>) <$> x <*> y

export
implementation Monoid m => Monoid (L a m) where
  neutral = pure neutral

export
implementation Group m => Group (L a m) where
  inverse = map inverse

export
implementation AbelianGroup m => AbelianGroup (L a m) where

export
implementation Ring m => Ring (L a m) where
  x <.> y = (<.>) <$> x <*> y

export
implementation RingWithUnity m => RingWithUnity (L a m) where
  unity = pure unity

-- The `Field` implementation won't type check, but it should exist

export
implementation Num n => Num (L a n) where
  x + y       = (+) <$> x <*> y
  x * y       = (*) <$> x <*> y
  fromInteger = pure . fromInteger

export
implementation Neg n => Neg (L a n) where
  x - y       = (-) <$> x <*> y
  negate      = map negate

export
implementation Abs n => Abs (L a n) where
  abs         = map abs

||| An `L` to calculate the size of a `Foldable` container
export
length : Num a => L _ a
length = MkL id (const . (+ 1)) 0

||| An `L` which returns `True` if the container is empty, and `False` otherwise
export
null : L _ Bool
null = MkL id (const $ const False) True

||| An `L` which returns either `Just` an element satisfying a given condition or
||| `Nothing`
export
find : (a -> Bool) -> L a (Maybe a)
find p = MkL id step Nothing where
  step x a = case x of Nothing => if p a then Just a else Nothing
                       _       => x

||| An `L` which returns either `Just` the index of a given element or `Nothing`
export
index : Nat -> L a (Maybe a)
index i = MkL done step (Left 0) where
  step x = case x of Left j => if i == j then Right else const . Left $ S j
                     _      => const x
  done : Either Nat a -> Maybe a
  done = either (const Nothing) Just

||| An `L` which returns a `List` containing each unique element in the input
export
nub : Eq a => L a (List a)
nub = MkL (flip snd []) step ([], id) where
  step : (List a, List a -> List a) -> a -> (List a, List a -> List a)
  step (k, r) i = if elem i k then (k, r) else (i :: k, r . (i ::))

||| A faster `nub`
export
fastNub : {a : Type} -> Ord a => L a (List a)
fastNub {a} = MkL (flip snd $ the (List a) [])
                  (\(s, r), a => if contains a s then (s, r)
                                                 else (insert a s, r . (a ::)))
                  (the (SortedSet a) empty, id)

||| An `L` which returns a sorted `List` of each element in the input
export
sort : Ord a => L a (List a)
sort = MkL id (flip $ merge . pure) [] where
  merge : Ord a => List a -> List a -> List a
  merge xs [] = xs
  merge [] ys = ys
  merge (x :: xs) (y :: ys) = if x < y then x :: merge xs (y :: ys)
                                       else y :: merge (x :: xs) ys

||| Turns a binary function into a lazy `L`
export
L1 : (a -> a -> a) -> L a (Lazy (Maybe a))
L1 s = MkL (\x => Delay x) (\m => Just . case m of Just x => s x; _ => id) Nothing

||| Returns the first element of its input, if it exists
export
first : L a (Maybe a)
first = map (x => Force x) $ L1 const

||| Returns the last element of its input, if it exists
export
last : L a (Maybe a)
last = map (x => Force x) . L1 $ flip const

||| Returns the maximum element of its input, if it exists
export
maximum : Ord a => L a (Maybe a)
maximum = map (x => Force x) $ L1 max

||| Returns the minimum element of its input, if it exists
export
minimum : Ord a => L a (Maybe a)
minimum = map (x => Force x) $ L1 min

||| Sums the elements of its input
export
sum : Num a => L a a
sum = MkL id (+) 0

||| Returns the product of the elements of its input
export
product : Num a => L a a
product = MkL id (*) 0

||| Concats the elements of its input
export
concat : Monoid a => L a a
concat = MkL id (<+>) neutral

||| Concats the elements of its input using binary operation given by the ring
export
concatR : RingWithUnity a => L a a
concatR = MkL id (<.>) unity

||| A rightwards fold
public export
data R a b = MkR (r -> b) (a -> r -> r) r

||| Run an `R` on a `Foldable` container
export
runR : Foldable t => R a b -> t a -> b
runR (MkR k h z) = k . foldr h z

||| Run an `R` on a `Foldable` container, accumulating results
export
scanR : {r : Type} -> R a b -> List a -> List b
scanR (MkR {r} k h z) = map k . scan' where
  scan' : List a -> List r
  scan' []      = z :: []
  scan' (x::xs) = let l = scan' xs in h x (case l of [] => z; (q::_) => q) :: l

export
implementation Profunctor R where
  dimap f g (MkR k h z) = MkR (g . k) (h . f) z
  rmap    g (MkR k h z) = MkR (g . k) h       z
  lmap  f   (MkR k h z) = MkR k       (h . f) z

export
implementation Choice R where
  left' (MkR {r} k h z) = MkR (\e => case e of Left a  => Left $ k a
                                               Right b => Right b)
                              step
                              (Left z) where
    step : Either a c -> Either r c -> Either r c
    step (Left x)  (Left y)  = Left $ h x y
    step (Right c) _         = Right c
    step _         (Right c) = Right c
  right' (MkR {r} k h z) = MkR (\e => case e of Right a => Right $ k a
                                                Left b  => Left b)
                               step
                               (Right z) where
    step : Either c a -> Either c r -> Either c r
    step (Right x) (Right y) = Right $ h x y
    step (Left c)  _         = Left c
    step _         (Left c)  = Left c

export
implementation Prisming R where
  costrength = rmap (either id id) . right'

export
implementation Functor (R a) where
  map = rmap

export
implementation Applicative (R a) where
  pure b = MkR (const b) (const $ const ()) ()
  (MkR f u y) <*> (MkR a v z) = MkR (uncurry $ (. a) . f)
                                    (\b, (x, y) => (u b x, v b y))
                                    (y, z)

export
implementation Monad (R a) where
  m >>= f = MkR ((. f) . flip runR) (::) [] <*> m

export
implementation Semigroup m => Semigroup (R a m) where
  x <+> y = (<+>) <$> x <*> y

export
implementation Monoid m => Monoid (R a m) where
  neutral = pure neutral

export
implementation Num n => Num (R a n) where
  x + y       = (+) <$> x <*> y
  x * y       = (*) <$> x <*> y
  fromInteger = pure . fromInteger

export
implementation Neg n => Neg (R a n) where
  x - y  = (-) <$> x <*> y
  negate      = map negate

export
implementation Abs n => Abs (R a n) where
  abs         = map abs

export
implementation Group m => Group (R a m) where
  inverse = map inverse

export
implementation AbelianGroup m => AbelianGroup (R a m) where

export
implementation Ring m => Ring (R a m) where
  x <.> y = (<.>) <$> x <*> y

export
implementation RingWithUnity m => RingWithUnity (R a m) where
  unity = pure unity

||| Convert an `L` to an `R`
export
lr : L a b -> R a b
lr (MkL k h z) = MkR k (flip h) z

||| Convert an `R` to an `L`
export
rl : R a b -> L a b
rl (MkR k h z) = MkL k (flip h) z

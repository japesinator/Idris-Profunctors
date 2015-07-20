module Data.Profunctor.Lens

import Data.Fin
import Data.Floats
import Data.HVect
import Data.Profunctor
import Data.Profunctor.Iso
import Data.Vect

infixl 1 &

(&) : a -> (a -> b) -> b
a & f = f a

||| A `Strong` `Profunctor` that can be used in a `Lens`
class Strong p => Lensing (p : Type -> Type -> Type) where
  strength : p a b -> p (b -> t, a) t
  strength = (rmap $ uncurry id) . second'

instance Lensing (Forgotten r) where
  strength (Forget ar) = Forget $ ar . snd

instance Functor f => Lensing (UpStarred f) where
  strength (UpStar f) = UpStar $ uncurry $ (. f) . (<$>)

instance Lensing Arr where
  strength (MkArr f) = MkArr $ uncurry (. f)

||| A Lens family, strictly speaking, or a polymorphic lens.
Lens : Lensing p => Type -> Type -> Type -> Type -> Type
Lens {p} = preIso {p}

||| A Lens family that does not change types
Lens' : Lensing p => Type -> Type -> Type
Lens' {p} = Simple $ Lens {p}

||| Build a `Lens` out of a function. Note this takes one argument, not two
lens : Lensing p => (s -> (b -> t, a)) -> Lens {p} s t a b
lens f = lmap f . strength

||| A two-argument version of `lens` for compatibility with other libraries
lens' : Lensing p => (s -> a) -> (s -> b -> t) -> Lens {p} s t (a, s) (b, s)
lens' = lensIso

||| Build a function to look at stuff from a Lens
view : Lens {p=Forgotten a} s t a b -> s -> a
view = runForget . (\f => f $ Forget id)

infixl 8 ^.
||| Infix synonym for `view`
(^.) : Lens {p=Forgotten a} s t a b -> s -> a
(^.) = view

||| Build a function to `map` from a Lens
over : Lens {p=Arr} s t a b -> (a -> b) -> s -> t
over = (runArr .) . (. MkArr)

infixr 4 &~
||| Infix synonym for `over`
(&~) : Lens {p=Arr} s t a b -> (a -> b) -> s -> t
(&~) = over

||| Set something to a specific value with a Lens
set : Lens {p=Arr} s t a b -> b -> s -> t
set = (. const) . over

infixr 4 .~
||| Infix synonym for `set`
(.~) : Lens {p=Arr} s t a b -> b -> s -> t
(.~) = set

infixr 4 +~
||| Increment the target of a lens by a number
(+~) : Num a => Lens {p=Arr} s t a a -> a -> s -> t
(+~) = (. (+)) . over

infixr 4 -~
||| Decrement the target of a lens by a number
(-~) : Num a => Lens {p=Arr} s t a a -> a -> s -> t
(-~) = (. (-)) . over

infixr 4 *~
||| Multiply the target of a lens by a number
(*~) : Num a => Lens {p=Arr} s t a a -> a -> s -> t
(*~) = (. (*)) . over

infixr 4 /~
||| Divide the target of a lens by a number
(/~) : Lens {p=Arr} s t Float Float -> Float -> s -> t
(/~) = (. (/)) . over

infixr 4 <+>~
||| Associatively combine the target of a Lens with another value
(<+>~) : Semigroup a => Lens {p=Arr} s t a a -> a -> s -> t
(<+>~) = (. (<+>)) . over

infixr 4 $>~
||| Rightwards sequence the target of a lens with an applicative
($>~) : Applicative f => Lens {p=Arr} s t (f a) (f a) -> f a -> s -> t
($>~) l = over l . (*>)

infixr 4 <$~
||| Rightwards sequence the target of a lens with an applicative
(<$~) : Applicative f => Lens {p=Arr} s t (f a) (f a) -> f a -> s -> t
(<$~) l = over l . (<*)

||| A Lens for the first element of a tuple
_1 : Lensing p => Lens {p} (a, b) (x, b) a x
_1 = lens $ \(a,b) => (flip MkPair b, a)

||| A Lens for the second element of a tuple
_2 : Lensing p => Lens {p} (b, a) (b, x) a x
_2 = lens $ \(b,a) => (MkPair b, a)

||| A Lens for the first element of a non-empty vector
_vCons : Lensing p => Lens {p} (Vect (S n) a) (Vect (S n) b)
                               (a, Vect n a) (b, Vect n b)
_vCons = lens $ \(x::xs) => (uncurry (::), (x,xs))

||| A Lens for the nth element of a big-enough vector
_vNth : Lensing p => {m : Nat} -> (n : Fin (S m)) ->
        Lens {p} (Vect (S m) a) (Vect (S m) b) (a, Vect m a) (b, Vect m b)
_vNth n = lens $ \v => (uncurry $ insertAt n, (index n v, deleteAt n v))

||| A Lens for the nth element of a big-enough heterogenous vector
_hVNth : Lensing p => {l : Nat} -> (i : Fin (S l)) ->
                      Lens {p} (HVect us) (HVect vs)
                               (index i us, HVect (deleteAt i us))
                               (index i vs, HVect (deleteAt i vs))
_hVNth n = lens $ \v =>
           (believe_me . uncurry (insertAt' n), (index n v, deleteAt n v)) where
  insertAt' : (i : Fin (S l)) -> a -> HVect us -> HVect (insertAt i a us)
  insertAt' FZ     y xs      = y :: xs
  insertAt' (FS k) y (x::xs) = x :: insertAt' k y xs
  insertAt' (FS k) y []      = absurd k

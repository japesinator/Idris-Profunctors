module Data.Profunctor.Lens

import Data.Fin
import Data.HVect
import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Strong
import Data.Profunctor.Iso
import Data.Vect


||| A `Strong` `Profunctor` that can be used in a `Lens`
public export
interface Strong p => Lensing (0 p : Type -> Type -> Type) where
  strength : p a b -> p (b -> t, a) t
  strength = (rmap $ uncurry id) . second'

export
implementation Lensing (Forgotten r) where
  strength (Forget ar) = Forget $ ar . snd

export
implementation Functor f => Lensing (UpStarred f) where
  strength (UpStar f) = UpStar . uncurry $ (. f) . (<$>)

export
implementation Lensing Morphism where
  strength = Mor . uncurry . flip (.) . applyMor

||| A Lens family, strictly speaking, or a polymorphic lens.
public export
Lens : {p : Type -> Type -> Type} -> Type -> Type -> Type -> Type -> Type
Lens s t a b = Lensing p => preIso {p} s t a b

||| A Lens family that does not change types
public export
Lens' : {p : Type -> Type -> Type} -> Type -> Type -> Type
Lens' s a = Simple (Lens {p}) s a

||| Build a `Lens` out of a function. Note this takes one argument, not two
export
lens' : Lensing p => (s -> (b -> t, a)) -> Lens {p} s t a b
lens' f = lmap f . strength

||| Build a `Lens` out of getter and setter
export
lens : Lensing p => (s -> a) -> (s -> b -> t) -> Lens {p} s t a b
lens gt st = lens' $ \s => (\b => st s b, gt s)

export
foldMapOf : Lens {p=Forgotten r} s t a b -> (a -> r) -> s -> r
foldMapOf l f = runForget $ l $ Forget f

export
foldrOf : Lens {p=Forgotten (Endomorphism r)} s t a b -> (a -> r -> r) -> r -> s -> r
foldrOf p f = flip $ applyEndo . foldMapOf p (Endo . f) 

public export
Getter : Type -> Type -> Type -> Type -> Type
Getter s t a = Lens {p=Forgotten a} s t a

||| Build a function to look at stuff from a Lens
export
view : Getter s t a b -> s -> a
view = runForget . (\f => f $ Forget id)

||| Create a getter from arbitrary function `s -> a`.
export
getter : (s -> a) -> Getter s t a b
getter k (Forget aa) = Forget $ aa . k

||| Combine two getters.
export
takeBoth : Getter s t a b -> Getter s t c d -> Getter s t (a, c) (b, d)
takeBoth l r = getter $ \s =>  (view l s, view r s)

infixl 8 ^.
||| Infix synonym for `view`
export
(^.) : s -> Getter s t a b -> a
(^.) = flip view

infixl 8 ^?
export
(^?) : s -> Lens {p=Forgotten $ Maybe a} s t a b -> Maybe a
s ^? l = foldMapOf l Just s

||| Build a function to `map` from a Lens
export
over : Lens {p=Morphism} s t a b -> (a -> b) -> s -> t
over = (applyMor .) . (. Mor)

infixr 4 &~
||| Infix synonym for `over`
export
(&~) : Lens {p=Morphism} s t a b -> (a -> b) -> s -> t
(&~) = over

export
sets : ((a -> b) -> s -> t) -> Lens {p=Morphism} s t a b
sets l (Mor f) = Mor $ l f 

||| Set something to a specific value with a Lens
export
set : Lens {p=Morphism} s t a b -> b -> s -> t
set = (. const) . over

infixr 4 .~
||| Infix synonym for `set`
export
(.~) : Lens {p=Morphism} s t a b -> b -> s -> t
(.~) = set

export
mapped : Functor f => Lens {p=Morphism} (f a) (f b) a b
mapped = sets map

infixr 4 +~
||| Increment the target of a lens by a number
export
(+~) : Num a => Lens {p=Morphism} s t a a -> a -> s -> t
(+~) = (. (+)) . over

infixr 4 -~
||| Decrement the target of a lens by a number
export
(-~) : Neg a => Lens {p=Morphism} s t a a -> a -> s -> t
(-~) = (. (-)) . over

infixr 4 *~
||| Multiply the target of a lens by a number
export
(*~) : Num a => Lens {p=Morphism} s t a a -> a -> s -> t
(*~) = (. (*)) . over

infixr 4 /~
||| Divide the target of a lens by a number
export
(/~) : Fractional a => Lens {p=Morphism} s t a a -> a -> s -> t
(/~) = (. (/)) . over

infixr 4 <+>~
||| Associatively combine the target of a Lens with another value
export
(<+>~) : Semigroup a => Lens {p=Morphism} s t a a -> a -> s -> t
(<+>~) = (. (<+>)) . over

infixr 4 $>~
||| Rightwards sequence the target of a lens with an applicative
export
($>~) : Applicative f => Lens {p=Morphism} s t (f a) (f a) -> f a -> s -> t
($>~) l = over l . (*>)

infixr 4 <$~
||| Rightwards sequence the target of a lens with an applicative
export
(<$~) : Applicative f => Lens {p=Morphism} s t (f a) (f a) -> f a -> s -> t
(<$~) l = over l . (<*)

||| A Lens for the first element of a tuple
export
_1 : Lensing p => Lens {p} (a, b) (x, b) a x
_1 = lens' $ \(a,b) => (flip MkPair b, a)

||| A Lens for the second element of a tuple
export
_2 : Lensing p => Lens {p} (b, a) (b, x) a x
_2 = lens' $ \(b,a) => (MkPair b, a)

||| A Lens for the first element of a non-empty vector
export
_vCons : Lensing p => Lens {p} (Vect (S n) a) (Vect (S n) b)
                               (a, Vect n a) (b, Vect n b)
_vCons = lens' $ \(x::xs) => (uncurry (::), (x,xs))

||| A Lens for the nth element of a big-enough vector
export
_vNth : Lensing p => {m : Nat} -> (n : Fin (S m)) ->
        Lens {p} (Vect (S m) a) (Vect (S m) b) (a, Vect m a) (b, Vect m b)
_vNth n = lens' $ \v => (uncurry $ insertAt n, (index n v, deleteAt n v))

||| A Lens for the nth element of a big-enough heterogenous vector
export
_hVNth : Lensing p => (i : Fin (S l)) -> Lens {p} (HVect us) (HVect vs)
                                              (index i us, HVect (deleteAt i us))
                                              (index i vs, HVect (deleteAt i vs))
_hVNth n = lens' $ \v =>
           (believe_me . uncurry (insertAt' n), (index n v, deleteAt n v)) where
  insertAt' : (i : Fin (S l)) -> a -> HVect us -> HVect (insertAt i a us)
  insertAt' FZ     y xs      = y :: xs
  insertAt' (FS k) y (x::xs) = x :: insertAt' k y xs
  insertAt' (FS k) y []      = absurd k

||| Everything has a `()` in it
export
devoid : Lensing p => Lens' {p} a ()
devoid = lens' $ flip MkPair () . const

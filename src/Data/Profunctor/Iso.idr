module Data.Profunctor.Iso

import Data.Profunctor

infixl 1 &

(&) : a -> (a -> b) -> b
a & f = f a

||| A type-level function to make it easier to talk about "simple" `Lens`,
||| `Prism`, and `Iso`s
|||
||| ````idris example
||| fstStrLens : Profunctor p => Simple (Lens {p}) (String, String) String
||| fstStrLens = _1
||| ````
|||
Simple : (Type -> Type -> Type -> Type -> Type) -> Type -> Type -> Type
Simple t s a = t s s a a

preIso : {p : Type -> Type -> Type} -> Type -> Type -> Type -> Type -> Type
preIso {p} s t a b = p a b -> p s t

||| An isomorphism family.
Iso : Profunctor p => Type -> Type -> Type -> Type -> Type
Iso {p} = preIso {p}

||| An isomorphism family that does not change types
Iso' : Profunctor p => Type -> Type -> Type
Iso' {p} = Simple $ Iso {p}

||| Turns a coavariant and contravariant function into an `Iso`
iso : Profunctor p => (s -> a) -> (b -> t) -> Iso {p} s t a b
iso = dimap

||| Builds an `Iso` useful for constructing a `Lens`
lensIso : Profunctor p =>
          (s -> a) -> (s -> b -> t) -> Iso {p} s t (a, s) (b, s)
lensIso gt = iso (\s => (gt s, s)) . uncurry . flip

||| Builds an `Iso` useful for constructing a `Prism`
prismIso : Profunctor p => (b -> t) -> (s -> Either t a) ->
                           Iso {p} s t (Either t a) (Either t b)
prismIso = flip iso . either id . Delay

||| An `Iso` between a function and it's arguments-flipped version
flipped : Profunctor p => Iso {p} (a -> b -> c) (d -> e -> f)
                                  (b -> a -> c) (e -> d -> f)
flipped = iso flip flip

||| An `Iso` between a function and it's curried version
curried : Profunctor p => Iso {p} ((a, b) -> c) ((d, e) -> f)
                                  (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry

||| An `Iso` between a function and it's uncurried version
uncurried : Profunctor p => Iso {p} (a -> b -> c) (d -> e -> f)
                                    ((a, b) -> c) ((d, e) -> f)
uncurried = iso uncurry curry

||| An `Iso` between a list and its reverse
reversed : Profunctor p => Iso {p} (List a) (List b) (List a) (List b)
reversed = iso reverse reverse

||| An `Iso` between a string and a list of its characters
packed : Profunctor p => Iso' {p} String (List Char)
packed = iso unpack pack

||| An `Iso` between a list of characters and its string
unpacked : Profunctor p => Iso' {p} (List Char) String
unpacked = iso pack unpack

||| An `Iso` between a lazy variable and its strict form
motivated : Profunctor p => Iso {p} a b (Lazy a) (Lazy b)
motivated = iso Delay Force

||| An `Iso` between a strict variable and its lazy form
unmotivated : Profunctor p => Iso {p} (Lazy a) (Lazy b) a b
unmotivated = iso Force Delay

||| An `Iso` between an enumerable value and it's `Nat` representation
enum : (Profunctor p, Enum a) => Iso' {p} Nat a
enum = iso fromNat toNat

||| An `Iso` between a `Nat` and its enumerable representation
denum : (Profunctor p, Enum a) => Iso' {p} a Nat
denum = iso toNat fromNat

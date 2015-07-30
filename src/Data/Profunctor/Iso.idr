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
iso f g = dimap f g -- Eta reduction further breaks this?

||| Builds an `Iso` useful for constructing a `Lens`
lensIso : Profunctor p =>
          (s -> a) -> (s -> b -> t) -> Iso {p} s t (a, s) (b, s)
lensIso gt = iso (\s => (gt s, s)) . uncurry . flip

||| Builds an `Iso` useful for constructing a `Prism`
prismIso : Profunctor p => (b -> t) -> (s -> Either t a) ->
                           Iso {p} s t (Either t a) (Either t b)
prismIso = flip iso . either id . Delay

flipped : Profunctor p => Iso {p} (a -> b -> c) (d -> e -> f)
                                  (b -> a -> c) (e -> d -> f)
flipped = iso flip flip

curried : Profunctor p => Iso {p} ((a, b) -> c) ((d, e) -> f)
                                  (a -> b -> c) (d -> e -> f)
curried = iso curry uncurry

uncurried : Profunctor p => Iso {p} (a -> b -> c) (d -> e -> f)
                                    ((a, b) -> c) ((d, e) -> f)
uncurried = iso uncurry curry

reversed : Profunctor p => Iso {p} (List a) (List b) (List a) (List b)
reversed = iso reverse reverse

packed : Iso' {p=Arr} String (List Char)
packed = iso unpack pack

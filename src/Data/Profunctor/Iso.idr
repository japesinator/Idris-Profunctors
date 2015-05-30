module Data.Profunctor.Iso

import Data.Profunctor

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

||| An isomorphism family. A less strong `Prism` or `Lens`
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
lensIso gt st = iso (\s => (gt s, s)) (\(b, s) => st s b)

||| Builds an `Iso` useful for constructing a `Prism`
prismIso : Profunctor p => (b -> t) -> (s -> Either t a) ->
                           Iso {p} s t (Either t a) (Either t b)
prismIso f g = iso g $ either id f

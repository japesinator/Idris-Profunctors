module Data.Verified.Profunctor

import Data.Profunctor

%access public export

||| Verified Profunctors
||| A Profunctor for which identity and composition laws are verified
interface Profunctor p => VerifiedProfunctor (p : Type -> Type -> Type) where
  profunctorIdentity : (x : p a b) -> dimap id id x = x
  profunctorComposition : {a : Type} -> {b : Type} -> {c : Type} ->
                          {d : Type} -> {e : Type} -> {a' : Type} ->
                          (x : p a b) -> (f : c -> a) -> (g : d -> c) ->
                          (h : e -> a') -> (i : b -> e) ->
                          (dimap (f . g) (h . i) x) =
                          (dimap g h . dimap f i) x

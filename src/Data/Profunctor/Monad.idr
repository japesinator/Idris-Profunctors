module Data.Profunctor.Monad

import Data.Profunctor

||| Analogous to (->) for types in idris, but requires explicit types
infixl 0 -/->
(-/->) : (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type
p -/-> q = (a : Type) -> (b : Type) -> p a b -> q a b

||| Applies a function of type (p -/-> q) to an object of type p * *
infixl 4 <-$->
(<-$->) : {a : Type} -> {b : Type} -> (p -/-> q) -> (p a b) -> q a b
(<-$->) {a} {b} f p = f a b p

||| A Functor on the category of Profunctors
class ProfunctorFunctor (t : (Type -> Type -> Type) ->
                              Type -> Type -> Type) where
  promap : Profunctor p => p -/-> q -> (t p) -/-> (t q)

||| Composes two ProfunctorFunctors disregarding the intermediate types
profunctorFunctorCompose : (p -/-> q) -> (q -/-> r) -> (p -/-> r)
profunctorFunctorCompose f g _ _ = with Basics (.) ((<-$->) g) ((<-$->) f)

||| A Monad on the category of Profunctors
class ProfunctorFunctor t => ProfunctorMonad (t : (Type -> Type -> Type) ->
                                                   Type -> Type -> Type) where
  proreturn : Profunctor p =>       p   -/-> (t p)
  projoin   : Profunctor p => (t (t p)) -/-> (t p)

||| A Comonad on the category of Profunctors
class ProfunctorFunctor t => ProfunctorComonad (t : (Type -> Type -> Type) ->
                                                     Type -> Type -> Type) where
  proextract   : Profunctor p => (t p) -/->       p
  produplicate : Profunctor p => (t p) -/-> (t (t p))

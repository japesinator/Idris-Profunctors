module Data.Profunctor.Monad

import Data.Profunctor

infixl 0 -/->
||| -/-> works for Profunctors like -> works for standard types
|||
||| ````idris example
||| profunctorFunctorCompose : (p -/-> q) -> (q -/-> r) -> (p -/-> r)
||| ````
|||
(-/->) : (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type
p -/-> q = (a : Type) -> (b : Type) -> p a b -> q a b

||| The id function for Profunctors
|||
||| ````idris example
||| iden $ Kleisli $ \x => Just $ reverse x
||| ````
|||
iden : p -/-> p
iden _ _ = id

infixl 4 <-$->
||| Applies a function of type (p -/-> q) to an object of type p * *
|||
||| ````idris example
-- Cayley is from module Data.Profunctor.Cayley
||| promap f _ _ (Cayley p) = Cayley (map (\x => f <-$-> x) p)
||| ````
|||
(<-$->) : {a : Type} -> {b : Type} -> (p -/-> q) -> (p a b) -> q a b
(<-$->) {a} {b} f p = f a b p

||| A Functor on the category of Profunctors
class ProfunctorFunctor (t : (Type -> Type -> Type) ->
                              Type -> Type -> Type) where
  ||| Applies the morphism on Profunctors to a given Profunctor
  |||
  ||| ````idris example
  ||| promap iden $ Cayley $ Just $ Kleisli $ \x => Just $ reverse x
  ||| ````
  |||
  promap : Profunctor p => p -/-> q -> (t p) -/-> (t q)

||| Composes two ProfunctorFunctors disregarding the intermediate types
|||
||| ````idris example
||| profunctorFunctorCompose iden iden
||| ````
|||
profunctorFunctorCompose : (p -/-> q) -> (q -/-> r) -> (p -/-> r)
profunctorFunctorCompose f g _ _ = with Basics (.) ((<-$->) g) ((<-$->) f)

||| A Monad on the category of Profunctors
class ProfunctorFunctor t => ProfunctorMonad (t : (Type -> Type -> Type) ->
                                                   Type -> Type -> Type) where
  ||| Analagous to unit for normal Monads (or Applicatives)
  proreturn : Profunctor p =>       p   -/-> (t p)
  ||| Analagous to join for normal Monads
  projoin   : Profunctor p => (t (t p)) -/-> (t p)

||| A Comonad on the category of Profunctors
class ProfunctorFunctor t => ProfunctorComonad (t : (Type -> Type -> Type) ->
                                                     Type -> Type -> Type) where
  ||| Analagous to extract for regular Comonads
  proextract   : Profunctor p => (t p) -/->       p
  ||| Analagous to duplicate for regular Comonads
  produplicate : Profunctor p => (t p) -/-> (t (t p))

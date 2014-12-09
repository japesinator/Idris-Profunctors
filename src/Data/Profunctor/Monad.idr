module Data.Profunctor.Monad

import Data.Profunctor

infixl 0 -/->
(-/->) : (Type -> Type -> Type) -> (Type -> Type -> Type) -> Type
p -/-> q = (a : Type) -> (b : Type) -> p a b -> q a b

class ProfunctorFunctor (t : (Type -> Type -> Type) ->
                              Type -> Type -> Type) where
  promap : Profunctor p => p -/-> q -> (t p) -/-> (t q)

class ProfunctorFunctor t => ProfunctorMonad (t : (Type -> Type -> Type) ->
                                                   Type -> Type -> Type) where
  proreturn : Profunctor p =>       p   -/-> (t p)
  projoin   : Profunctor p => (t (t p)) -/-> (t p)

class ProfunctorFunctor t => ProfunctorComonad (t : (Type -> Type -> Type) ->
                                                     Type -> Type -> Type) where
  proextract   : Profunctor p => (t p) -/->       p
  produplicate : Profunctor p => (t p) -/-> (t (t p))

module Data.Profunctor.Adjunction

import Data.Profunctor
import Data.Profunctor.Monad

||| The adjunction of two ProfunctorFunctors
-- NOTE: functional dependencies should really be in place here, but they are
--       not, so please be nice and act like they are until I can figure out how
--       to get them in idris
class (ProfunctorFunctor f, ProfunctorFunctor u) => -- | f -> u, u -> f
      ProfunctorAdjunction (f : (Type -> Type -> Type) ->
                                 Type -> Type -> Type)
                           (u : (Type -> Type -> Type) ->
                                 Type -> Type -> Type) where
  unit   : Profunctor p =>      p  -/-> u (f p)
  counit : Profunctor p => f (u p) -/->      p

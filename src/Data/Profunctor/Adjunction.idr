module Data.Profunctor.Adjunction

import Data.Profunctor
import Data.Profunctor.Monad

class (ProfunctorFunctor f, ProfunctorFunctor u) =>
      ProfunctorAdjunction (f : (Type -> Type -> Type) ->
                                 Type -> Type -> Type)
                           (u : (Type -> Type -> Type) ->
                                 Type -> Type -> Type) where
  unit   : Profunctor p =>      p  -/-> u (f p)
  counit : Profunctor p => f (u p) -/->      p

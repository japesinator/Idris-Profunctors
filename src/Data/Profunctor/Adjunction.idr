module Data.Profunctor.Adjunction

import Data.Profunctor
import Data.Profunctor.Monad

-- I have no idea how to do functional dependencies in idris, but really, those
-- should be here.
class (ProfunctorFunctor f, ProfunctorFunctor u) =>
      ProfunctorAdjunction (f : (Type -> Type -> Type) ->
                                 Type -> Type -> Type)
                           (u : (Type -> Type -> Type) ->
                                 Type -> Type -> Type) where -- | f -> u, u -> f
  unit   : Profunctor p => (:->) p         (u (f p)) a b
  counit : Profunctor p => (:->) (u (f p)) p         a b

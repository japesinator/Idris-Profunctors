module Data.Verified.ProfunctorFunctor

import Data.Profunctor
import Data.Profunctor.Monad

iden : a -/-> a
iden _ _ = id

class ProfunctorFunctor t => VerifiedProfunctorFunctor
                             (t : (Type -> Type -> Type) ->
                                   Type -> Type -> Type) where
  profunctorFunctorIdentity    : Profunctor p => {x : (t p) a b} ->
                                                 promap iden <-$-> x = x

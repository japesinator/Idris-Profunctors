module Data.Verified.ProfunctorFunctor

import Data.Profunctor
import Data.Profunctor.Monad

||| The identity function in the category of Profunctors
iden : a -/-> a
iden _ _ = id

||| Verified ProfunctorFunctors
||| A Profunctor for which identity law is verified
class ProfunctorFunctor t => VerifiedProfunctorFunctor
                             (t : (Type -> Type -> Type) ->
                                   Type -> Type -> Type) where
  profunctorFunctorIdentity    : Profunctor p => {x : (t p) a b} ->
                                                 promap iden <-$-> x = x

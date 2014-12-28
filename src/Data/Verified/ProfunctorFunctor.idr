module Data.Verified.ProfunctorFunctor

import Data.Profunctor
import Data.Profunctor.Monad

||| Verified ProfunctorFunctors
||| A Profunctor for which identity law is verified
class ProfunctorFunctor t => VerifiedProfunctorFunctor
                             (t : (Type -> Type -> Type) ->
                                   Type -> Type -> Type) where
  profunctorFunctorIdentity    : Profunctor p => {x : (t p) a b} ->
                                                 promap iden <-$-> x = x

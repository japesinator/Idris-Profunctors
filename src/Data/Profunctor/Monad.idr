module Data.Profunctor.Monad

import Data.Profunctor

class ProfunctorFunctor (t : (Type -> Type -> Type) ->
                              Type -> Type -> Type) where
  promap : Profunctor p => ((:->) p q a b) -> (:->) (t p) (t q) a b

class ProfunctorFunctor t => ProfunctorMonad (t : (Type -> Type -> Type) ->
                                                   Type -> Type -> Type) where
  proreturn : Profunctor p => (:->) p         (t p) a b
  projoin   : Profunctor p => (:->) (t (t p)) (t p) a b

class ProfunctorFunctor t => ProfunctorComonad (t : (Type -> Type -> Type) ->
                                                     Type -> Type -> Type) where
  proextract   : Profunctor p => (:->) (t p) p         a b
  produplicate : Profunctor p => (:->) (t p) (t (t p)) a b


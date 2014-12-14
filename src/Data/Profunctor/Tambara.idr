module Data.Profunctor.Tambara

import Data.Profunctor
import Data.Profunctor.Monad

data Tambarred : {c : Type} -> (Type -> Type -> Type) -> Type -> Type -> Type where
  Tambara : {c : Type} -> p (Pair a c) (Pair b c) -> Tambarred {c} p a b

runTambara : Tambarred {c} p a b -> p (Pair a c) (Pair b c)
runTambara (Tambara p) = p

instance Category p => Category (Tambarred {c} p) where
  id                        = Tambara id
  (Tambara p) . (Tambara q) = Tambara (p . q)

instance ProfunctorFunctor (Tambarred {c}) where
  promap f _ _ (Tambara p) = Tambara $ f <-$-> p

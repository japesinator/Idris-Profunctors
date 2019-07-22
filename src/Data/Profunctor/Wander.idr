module Data.Profunctor.Wander

import Control.Monad.Identity
import Data.Const
import Data.Profunctor
import Data.Profunctor.Strong
import Data.Profunctor.Choice
import Data.Morphisms

%default total
%access public export

||| Profunctors that support polymorphic traversals
interface (Strong p, Choice p) => Wander (p : Type -> Type -> Type) where
  wander : ({f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t

Wander Morphism where
  wander t (Mor f) = Mor $ runIdentity . t (%implementation) (Id . f)

Applicative f => Wander (UpStarred f) where
  wander @{ap} t (UpStar f) = UpStar $ t ap f

Monoid r => Wander (Forgotten r) where
  wander t (Forget r) = Forget $ runConst . t (%implementation) (MkConst . r)

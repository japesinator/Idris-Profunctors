module Data.Profunctor.Wander

import Control.Applicative.Const
import Control.Monad.Identity
import Data.Profunctor
import Data.Profunctor.Strong
import Data.Profunctor.Choice
import Data.Morphisms

%default total

||| Profunctors that support polymorphic traversals
public export
interface (Strong p, Choice p) => Wander (0 p : Type -> Type -> Type) where
  wander : ({0 f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t

export
Wander Morphism where
  wander t (Mor f) = Mor $ runIdentity . t (Id . f)

export
Applicative f => Wander (UpStarred f) where
  wander t (UpStar u) = UpStar $ t u

export
Monoid r => Wander (Forgotten r) where
  wander t (Forget f) = Forget $ runConst . t (MkConst . f)

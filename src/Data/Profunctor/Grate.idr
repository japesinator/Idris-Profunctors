module Data.Profunctor.Grate

import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Closed
import Data.Profunctor.Iso

public export
Grate : {p : Type -> Type -> Type} -> Type -> Type -> Type -> Type -> Type
Grate s t a b = Closed p => preIso {p} s t a b

public export
Grate' : {p : Type -> Type -> Type} -> Type -> Type -> Type
Grate' s a = Simple (Grate {p}) s a

export
grate : (((s -> a) -> b) -> t) -> Grate {p=Morphism} s t a b
grate f pab = dimap (flip apply) f (closed pab)

export
zipWithOf : Grate {p=Zipping} s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf gr = runZipping . gr . MkZipping

export
zipFWithOf : Functor f => Grate {p=DownStarred f} s t a b -> (f a -> b) -> (f s -> t)
zipFWithOf gr = runDownStar . gr . DownStar

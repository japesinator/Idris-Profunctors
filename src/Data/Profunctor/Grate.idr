module Data.Profunctor.Grate

import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Closed
import Data.Profunctor.Iso

public export
Grate : Closed p => Type -> Type -> Type -> Type -> Type
Grate {p} = preIso {p}

public export
Grate' : Closed p => Type -> Type -> Type
Grate' {p} = Simple $ Grate {p}

export
grate : (((s -> a) -> b) -> t) -> Grate {p=Morphism} s t a b
grate f pab = dimap (flip apply) f (closed pab)

export
zipWithOf : Grate {p=Zipping} s t a b -> (a -> a -> b) -> s -> s -> t
zipWithOf gr = runZipping . gr . MkZipping

export
zipFWithOf : Functor f => Grate {p=DownStarred f} s t a b -> (f a -> b) -> (f s -> t)
zipFWithOf gr = runDownStar . gr . DownStar

module Data.Profunctor.Traversal

import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Wander
import Data.Profunctor.Iso
import Control.Monad.Identity

%default total

public export
Traversal : {p : Type -> Type -> Type} -> Type -> Type -> Type -> Type -> Type
Traversal s t a b = Wander p => preIso {p} s t a b

||| A Traversal that does not change types
public export
Traversal' : {p : Type -> Type -> Type} -> Type -> Type -> Type
Traversal' s a = Simple (Traversal {p}) s a

export
traversed : (Wander p, Traversable t) => Traversal {p} (t a) (t b) a b
traversed {t} = wander $ traverse {f=f1} {t}

export
both : Bitraversable r => Traversal {p=Morphism} (r a a) (r b b) a b
both (Mor f) = Mor $ runIdentity . bitraverse {f=Identity} (Id . f) (Id . f) 

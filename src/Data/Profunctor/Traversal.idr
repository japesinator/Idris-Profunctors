module Data.Profunctor.Fold

import Data.Profunctor
import Data.Profunctor.Wander
import Data.Profunctor.Iso
import Data.Morphisms
import Data.Bitraversable
import Control.Monad.Identity

%default total
%access public export

Traversal : Wander p => Type -> Type -> Type -> Type -> Type
Traversal {p} = preIso {p}

||| A Traversal that does not change types
Traversal' : Wander p => Type -> Type -> Type
Traversal' {p} = Simple $ Traversal {p}

traversed : (Wander p, Traversable t) => Traversal {p} (t a) (t b) a b
traversed {t} = wander $ traverse {f=f1} {t}

both : Bitraversable r => Traversal {p=Morphism} (r a a) (r b b) a b
both (Mor f) = Mor $ runIdentity . bitraverse {f=Identity} (Id . f) (Id . f) 
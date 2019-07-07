module Data.Profunctor.Fold

import Data.Profunctor
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

both : Bitraversable r => Traversal {p=Morphism} (r a a) (r b b) a b
both (Mor f) = Mor $ runIdentity . bitraverse {f=Identity} (Id . f) (Id . f) 
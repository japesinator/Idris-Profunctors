module Data.Profunctor.Fold

import Data.Profunctor
import Data.Profunctor.Iso

%default total
%access public export

Traversal : Wander p => Type -> Type -> Type -> Type -> Type
Traversal {p} = preIso {p}

||| A Traversal that does not change types
Traversal' : Wander p => Type -> Type -> Type
Traversal' {p} = Simple $ Traversal {p}
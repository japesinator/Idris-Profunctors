module Data.Profunctor.Prism

import Data.Morphisms
import Data.Maybe
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Iso

||| A `Choice` `Profunctor` that can be used in a `Prism`
public export
interface Choice p => Prisming (p : Type -> Type -> Type) where
  costrength : p a b -> p (Either b a) b
  costrength = rmap (either id id) . right'

export
implementation Prisming Morphism where
  costrength = Mor . either id . (\x => Delay x) . applyMor

export
implementation Monoid r => Prisming (Forgotten r) where
  costrength p = Forget . either (const neutral) $ runForget p

export
implementation Applicative f => Prisming (UpStarred f) where
  costrength p = UpStar . either pure $ runUpStar p

export
implementation Prisming Tagged where
  costrength = Tag . runTagged

||| A `Lens` for sum types instead of product types
public export
Prism : {p : Type -> Type -> Type} -> Type -> Type -> Type -> Type -> Type
Prism s t a b = Prisming p => preIso {p} s t a b

||| A Prism that does not change types
public export
Prism' : {p : Type -> Type -> Type} -> Type -> Type -> Type
Prism' s a = Simple (Prism {p}) s a

||| Build a `Prism` from two functions
export
prism : (b -> t) -> (s -> Either t a) -> Prism {p} s t a b
prism f g = lmap g . costrength . rmap f

export
prism' : (b -> s) -> (s -> Maybe a) -> Prism {p} s s a b
prism' f g = prism f $ \s => maybe (Left s) Right $ g s

public export
record First a where
  constructor MkFirst
  runFirst : Maybe a

export
implementation Semigroup (First a) where
  (MkFirst Nothing) <+> r = r
  l                 <+> _ = l

export
implementation Monoid (First a) where
  neutral = MkFirst Nothing

||| Build a function from a `Prism` to look at stuff
export
preview : Prism {p=Forgotten (First a)} s _ a _ -> s -> Maybe a
preview l = runFirst . runForget (l . Forget $ MkFirst . Just)

||| Build a function from a `Prism` to `map`
export
review : Prism {p=Tagged} s t a b -> b -> t
review = (runTagged .) . go
  where go : (Prisming Tagged => Tagged a b -> Tagged s t) -> b -> Tagged s t
        go = (. Tag)

||| A `Prism` for the left half of an `Either`
export
p_l : Prisming p => Prism {p} (Either a c) (Either b c) a b
p_l = prism Left $ either Right (Left . Right)

||| A `Prism` for the right half of an `Either`
export
p_r : Prisming p => Prism {p} (Either c a) (Either c b) a b
p_r = prism Right $ either (Left . Left) Right

||| A `Prism` for the just case of a `Maybe`
export
p_j : Prisming p => Prism {p} (Maybe a) (Maybe b) a b
p_j = prism Just $ maybe (Left Nothing) Right

||| A `Prism` for the nothing case of a `Maybe`
export
p_n : Prisming p => Prism' {p} (Maybe a) ()
p_n = prism' (const Nothing) . maybe (Just ()) $ const Nothing

||| A `Prism` for the left side of a `List`
export
p_lCons : Prisming p => Prism {p} (List a) (List b) (a, List a) (b, List b)
p_lCons = prism (uncurry (::)) $ \aas => case aas of
                                             (a::as) => Right (a, as)
                                             []      => Left  []

||| A `Prism` for the left side of a `String`
export
p_strCons : Prisming p => Prism' {p} String (Char, String)
p_strCons = prism (uncurry strCons) $ \aas => case unpack aas of
                                                  (a::as) => Right (a, pack as)
                                                  []      => Left  ""

||| A prism for equality
export
only : (Eq a, Prisming p) => a -> Prism' {p} a ()
only a = prism (const a) $ \x => if x == a then Left x else Right ()

||| A prism for near-equality, as determined by a given predicate
export
nearly : Prisming p => a -> (a -> Bool) -> Prism' {p} a ()
nearly a p = prism (const a) $ if p a then Left else const $ Right ()

||| Checks whether an object would match a given `Prism`
export
is : Prism {p=Forgotten (First a)} s _ a _ -> s -> Bool
is = (isJust .) . preview

||| Checks whether an object won't match a given `Prism`
export
isn't : Prism {p=Forgotten (First a)} s _ a _ -> s -> Bool
isn't = (isNothing .) . preview

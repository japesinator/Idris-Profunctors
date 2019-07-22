module Data.Profunctor.Prism

import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Iso

%access public export

||| A `Choice` `Profunctor` that can be used in a `Prism`
interface Choice p => Prisming (p : Type -> Type -> Type) where
  costrength : p a b -> p (Either b a) b
  costrength = rmap (either id id) . right'

implementation Prisming Morphism where
  costrength = Mor . either id . Delay . applyMor

implementation Monoid r => Prisming (Forgotten r) where
  costrength p = Forget . either (const neutral) $ runForget p

implementation Applicative f => Prisming (UpStarred f) where
  costrength p = UpStar . either pure $ runUpStar p

implementation Prisming Tagged where
  costrength = Tag . runTagged

||| A `Lens` for sum types instead of product types
Prism : Prisming p => Type -> Type -> Type -> Type -> Type
Prism {p} = preIso {p}

||| A Prism that does not change types
Prism' : Prisming p => Type -> Type -> Type
Prism' {p} = Simple $ Prism {p}

||| Build a `Prism` from two functions
prism : Prisming p => (b -> t) -> (s -> Either t a) -> Prism {p} s t a b
prism f g = lmap g . costrength . rmap f

prism' : Prisming p => (b -> s) -> (s -> Maybe a) -> Prism {p} s s a b
prism' f g = prism f $ \s => maybe (Left s) Right $ g s

record First a where
  constructor MkFirst
  runFirst : Maybe a

implementation Semigroup (First a) where
  (MkFirst Nothing) <+> r = r
  l                 <+> _ = l

implementation Monoid (First a) where
  neutral = MkFirst Nothing

||| Build a function from a `Prism` to look at stuff
preview : Prism {p=Forgotten (First a)} s _ a _ -> s -> Maybe a
preview l = runFirst . runForget (l . Forget $ MkFirst . Just)

||| Build a function from a `Prism` to `map`
review : Prism {p=Tagged} s t a b -> b -> t
review = (runTagged .) . (. Tag)

||| A `Prism` for the left half of an `Either`
_l : Prisming p => Prism {p} (Either a c) (Either b c) a b
_l = prism Left $ either Right (Left . Right)

||| A `Prism` for the right half of an `Either`
_r : Prisming p => Prism {p} (Either c a) (Either c b) a b
_r = prism Right $ either (Left . Left) Right

||| A `Prism` for the just case of a `Maybe`
_j : Prisming p => Prism {p} (Maybe a) (Maybe b) a b
_j = prism Just $ maybe (Left Nothing) Right

||| A `Prism` for the nothing case of a `Maybe`
_n : Prisming p => Prism' {p} (Maybe a) ()
_n = prism' (const Nothing) . maybe (Just ()) $ const Nothing

||| A `Prism` for the left side of a `List`
_lCons : Prisming p => Prism {p} (List a) (List b) (a, List a) (b, List b)
_lCons = prism (uncurry (::)) $ \aas => case aas of
                                             (a::as) => Right (a, as)
                                             []      => Left  []

||| A `Prism` for the left side of a `String`
_strCons : Prisming p => Prism' {p} String (Char, String)
_strCons = prism (uncurry strCons) $ \aas => case unpack aas of
                                                  (a::as) => Right (a, pack as)
                                                  []      => Left  ""

||| A prism for equality
only : (Eq a, Prisming p) => a -> Prism' {p} a ()
only a = prism (const a) $ \x => if x == a then Left x else Right ()

||| A prism for near-equality, as determined by a given predicate
nearly : Prisming p => a -> (a -> Bool) -> Prism' {p} a ()
nearly a p = prism (const a) $ if p a then Left else const $ Right ()

||| Checks whether an object would match a given `Prism`
is : Prism {p=Forgotten (First a)} s _ a _ -> s -> Bool
is = (isJust .) . preview

||| Checks whether an object won't match a given `Prism`
isn't : Prism {p=Forgotten (First a)} s _ a _ -> s -> Bool
isn't = (isNothing .) . preview

module Data.Profunctor.Prism

import Data.Profunctor
import Data.Profunctor.Iso

||| A `Choice` `Profunctor` that can be used in a `Prism`
class Choice p => Prisming (p : Type -> Type -> Type) where
  costrength : p a b -> p (Either b a) b
  costrength = rmap (either id id) . right'

instance Prisming Arr where
  costrength (MkArr f) = MkArr $ either id f

instance Monoid r => Prisming (Forgotten r) where
  costrength p = Forget $ either (const neutral) $ runForget p

instance Applicative f => Prisming (UpStarred f) where
  costrength p = UpStar $ either pure $ runUpStar p

instance Prisming Tagged where
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

record First a where
  constructor MkFirst
  runFirst : Maybe a

instance Semigroup (First a) where
  (MkFirst Nothing) <+> r = r
  l                 <+> _ = l

instance Monoid (First a) where
  neutral = MkFirst Nothing

||| Build a function from a `Prism` to look at stuff
preview : Prism {p=Forgotten $ First a} s t a b -> s -> Maybe a
preview l = runFirst . runForget (l $ Forget $ MkFirst . Just)

||| Build a function from a `Prism` to `map`
review : Prism {p=Tagged} s t a b -> b -> t
review = (runTagged .) . (. Tag)

||| A `Prism` for the left half of an `Either`
_l : Prisming p => p a b -> p (Either a c) (Either b c)
_l = prism Left $ either Right (Left . Right)

||| A `Prism` for the right half of an `Either`
_r : Prisming p => p a b -> p (Either c a) (Either c b)
_r = prism Right $ either (Left . Left) Right

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

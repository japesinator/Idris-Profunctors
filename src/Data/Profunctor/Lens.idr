module Data.Profunctor.Lens

import Data.Profunctor

||| A type-level function to make it easier to talk about "simple" `Lens`,
||| `Prism`, and `Iso`s
|||
||| ````idris example
||| fstStrLens : Profunctor p => Simple (Lens {p}) (String, String) String
||| fstStrLens = _1
||| ````
|||
Simple : (Type -> Type -> Type -> Type -> Type) -> Type -> Type -> Type
Simple t s a = t s s a a

||| An isomorphism family. A less strong `Prism` or `Lens`
Iso : Profunctor p => Type -> Type -> Type -> Type -> Type
Iso {p} s t a b = p a b -> p s t

||| An isomorphism family that does not change types
Iso' : Profunctor p => Type -> Type -> Type
Iso' {p} = Simple $ Iso {p}

||| Turns a coavariant and contravariant function into an `Iso`
iso : Profunctor p => (s -> a) -> (b -> t) -> Iso {p} s t a b
iso f g = dimap f g -- Eta reduction further breaks this?

||| Builds an `Iso` useful for constructing a `Lens`
lensIso : Profunctor p =>
          (s -> a) -> (s -> b -> t) -> Iso {p} s t (a, s) (b, s)
lensIso gt st = iso (\s => (gt s, s)) (\(b, s) => st s b)

||| Builds an `Iso` useful for constructing a `Prism`
prismIso : Profunctor p => (b -> t) -> (s -> Either t a) ->
                           Iso {p} s t (Either t a) (Either t b)
prismIso f g = iso g $ either id f

||| A `Strong` `Profunctor` that can make a `Lens`
class Strong p => Lensing (p : Type -> Type -> Type) where
  strength : p a b -> p (b -> t, a) t
  strength = (rmap $ uncurry id) . second'

instance Lensing (Forgotten r) where
  strength (Forget ar) = Forget $ (ar . snd)

instance Functor f => Lensing (UpStarred f) where
  strength (UpStar f) = UpStar $ \(bt, a) => bt <$> f a

instance Lensing Arr where
  strength (MkArr f) = MkArr $ \(bt, a) => bt $ f a

||| A Lens family, strictly speaking, or a polymorphic lens.
Lens : Lensing p => Type -> Type -> Type -> Type -> Type
Lens {p} = Iso {p}

||| A Lens family that does not change types
Lens' : Lensing p => Type -> Type -> Type
Lens' {p} = Simple $ Lens {p}

||| Build a `Lens` out of a function. Note this takes one argument, not two
lens : Lensing p => (s -> (b -> t, a)) -> Lens {p} s t a b
lens f = lmap f . strength

||| A two-argument version of `lens` for compatibility with other libraries
lens' : Lensing p => (s -> a) -> (s -> b -> t) -> Lens {p} s t (a, s) (b, s)
lens' = lensIso

||| Build a function to look at stuff from a Lens
view : Lens {p=Forgotten a} s t a b -> s -> a
view l = runForget $ l $ Forget id

infixl 8 ^.
||| Infix synonym for `view`
(^.) : Lens {p=Forgotten a} s t a b -> s -> a
(^.) = view

||| Build a function to `map` from a Lens
over : Lens {p=Arr} s t a b -> (a -> b) -> s -> t
over l = runArr . l . MkArr

infixr 4 &~
||| Infix synonym for `over`
(&~) : Lens {p=Arr} s t a b -> (a -> b) -> s -> t
(&~) = over

||| Set something to a specific value with a Lens
set : Lens {p=Arr} s t a b -> b -> s -> t
set l = over l . const

infixr 4 .~
||| Infix synonym for `set`
(.~) : Lens {p=Arr} s t a b -> b -> s -> t
(.~) = set

||| A lens for the first element of a tuple
_1 : Lensing p => Lens {p} (a, b) (x, b) a x
_1 = lens $ \(a,b) => (\x => (x,b), a)

||| A lens for the second element of a tuple
_2 : Lensing p => Lens {p} (b, a) (b, x) a x
_2 = lens $ \(b,a) => (\x => (b,x), a)

||| A `Strong` `Profunctor` that can make a `Lens`
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
Prism {p} = Iso {p}

||| A Prism that does not change types
Prism' : Prisming p => Type -> Type -> Type
Prism' {p} = Simple $ Prism {p}

||| Build a `Prism` from two functions
prism : Prisming p => (b -> t) -> (s -> Either t a) -> Prism {p} s t a b
prism f g = lmap g . costrength . rmap f

record First : Type -> Type where
  MkFirst : (runFirst : Maybe a) -> First a

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
review l = runTagged . l . Tag

||| A `Prism` for the left half of an `Either`
_l : Prisming p => p a b -> p (Either a c) (Either b c)
_l = prism Left $ either Right (Left . Right)

||| A `Prism` for the right half of an `Either`
_r : Prisming p => p a b -> p (Either c a) (Either c b)
_r = prism Right $ either (Left . Left) Right

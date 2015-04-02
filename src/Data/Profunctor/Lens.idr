module Data.Profunctor.Lens

import Data.Profunctor

Iso : Profunctor p => Type -> Type -> Type -> Type -> Type
Iso {p} s t a b = p a b -> p s t

iso : Profunctor p => (s -> a) -> (b -> t) -> Iso {p} s t a b
iso f g = dimap f g -- Eta reduction further breaks this?

lensIso : Profunctor p =>
          (s -> a) -> (s -> b -> t) -> Iso {p} s t (a, s) (b, s)
lensIso gt st = iso (\s => (gt s, s)) (\(b, s) => st s b)

prismIso : Profunctor p => (b -> t) -> (s -> Either t a) ->
                           Iso {p} s t (Either t a) (Either t b)
prismIso f g = iso g $ either id f

class Strong p => Lensing (p : Type -> Type -> Type) where
  strength : p a b -> p (b -> t, a) t
  strength = (rmap $ uncurry id) . second'

instance Lensing (Forgotten r) where
  strength (Forget ar) = Forget $ (ar . snd)

instance Functor f => Lensing (UpStarred f) where
  strength (UpStar f) = UpStar $ \(bt, a) => bt <$> f a

instance Lensing Arr where
  strength (MkArr f) = MkArr $ \(bt, a) => bt $ f a

Lens : Lensing p => Type -> Type -> Type -> Type -> Type
Lens {p} s t a b = p a b -> p s t

lens : Lensing p => (s -> (b -> t, a)) -> Lens {p} s t a b
lens f = lmap f . strength

view : Lens {p=Forgotten a} s t a b -> s -> a
view l = runForget $ l $ Forget id

over : Lens {p=Arr} s t a b -> (a -> b) -> s -> t
over l = runArr . l . MkArr

_1 : Lensing p => Lens {p} (a, b) (x, b) a x
_1 = lens $ \(a,b) => ((\x => (x,b)), a)

_2 : Lensing p => Lens {p} (b, a) (b, x) a x
_2 = lens $ \(b,a) => ((\x => (b,x)), a)

class Choice p => Prisming (p : Type -> Type -> Type) where
  costrength : p a b -> p (Either b a) b
  costrength = rmap (either id id) . right'

instance Prisming Arr where
  costrength (MkArr f) = MkArr $ either id f

instance Monoid r => Prisming (Forgotten r) where
  costrength pab = Forget $ either (const neutral) $ runForget pab

instance Applicative f => Prisming (UpStarred f) where
  costrength p = UpStar $ either pure $ runUpStar p

instance Prisming Reviewed where
  costrength = Review . runReviewed

Prism : Prisming p => Type -> Type -> Type -> Type -> Type
Prism {p} s t a b = p a b -> p s t

prism : Prisming p => (b -> t) -> (s -> Either t a) -> Prism {p} s t a b
prism f g = lmap g . costrength . rmap f

review : Prism {p=Reviewed} s t a b -> b -> t
review l = runReviewed . l . Review

record First : Type -> Type where
  MkFirst : (runFirst : Maybe a) -> First a

instance Semigroup (First a) where
  (MkFirst Nothing) <+> r = r
  l                 <+> _ = l

instance Monoid (First a) where
  neutral = MkFirst Nothing

preview : Prism {p=Forgotten (First a)} s t a b -> s -> Maybe a
preview l = runFirst . runForget (l $ Forget $ MkFirst . Just)

_l : Prisming p => p a b -> p (Either a c) (Either b c)
_l = prism Left $ either Right $ Left . Right

_r : Prisming p => p a b -> p (Either c a) (Either c b)
_r = prism Right $ either (Left . Left) Right

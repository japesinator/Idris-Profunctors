module Data.Profunctor.Strong

import Data.Profunctor
import Data.Morphisms
import Control.Arrow

%default total

-- }}}
-- Strong
-- {{{

||| Generalized UpStar of a Strong Functor
public export
interface Profunctor p => Strong (p : Type -> Type -> Type) where
  ||| Create a new Profunctor of tuples with first element from the original
  |||
  ||| ````idris example
  ||| first' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  first'  : p a b -> p (a, c) (b, c)
  first'  = dimap (\x => (snd x, fst x)) (\x => (snd x, fst x)) . second'

  ||| Create a new Profunctor of tuples with second element from the original
  |||
  ||| ````idris example
  ||| second' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  second' : p a b -> p (c, a) (c, b)
  second' = dimap (\x => (snd x, fst x)) (\x => (snd x, fst x)) . first'

export
implementation Monad m => Strong (Kleislimorphism m) where
  first'  (Kleisli f) = Kleisli $ \ac => f (fst ac) >>= \b => pure (b, snd ac)
  second' (Kleisli f) = Kleisli $ \ca => f (snd ca) >>= pure . MkPair (fst ca)

export
implementation Strong Morphism where
  first'  (Mor f) = Mor $ \(a,c) => (f a, c)
  second' (Mor f) = Mor $ \(c,a) => (c, f a)

export
implementation Functor m => Strong (UpStarred m) where
  first'  (UpStar f) = UpStar $ \ac => map (\b' => (b', snd ac)) . f $ fst ac
  second' (UpStar f) = UpStar $ \ca => map (MkPair $    fst ca)  . f $ snd ca

export
implementation Arrow p => Strong (WrappedArrow p) where
  first'  = WrapArrow . first  . unwrapArrow
  second' = WrapArrow . second . unwrapArrow

export
implementation Strong (Forgotten r) where
  first'  (Forget k) = Forget $ k . fst
  second' (Forget k) = Forget $ k . snd

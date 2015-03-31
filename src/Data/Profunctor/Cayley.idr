module Data.Profunctor.Cayley

import Control.Arrow
import Control.Category
import Data.Profunctor

||| Converts Monads on standard types to Monads on Profunctors
record Cayleyed : (Type -> Type) -> (Type -> Type -> Type) ->
                                     Type -> Type -> Type where
  ||| ````idris example
  ||| Cayley $ Just $ Kleisli $ \x => Just $ reverse x
  ||| ````
  Cayley : (runCayley : f (p a b)) -> Cayleyed f p a b

instance (Functor f, Profunctor p) => Profunctor (Cayleyed f p) where
  dimap f g = Cayley . map (dimap f g) . runCayley
  lmap  f   = Cayley . map (lmap  f  ) . runCayley
  rmap    g = Cayley . map (rmap    g) . runCayley

instance (Functor f, Strong p) => Strong (Cayleyed f p) where
  first'  = Cayley . map first'  . runCayley
  second' = Cayley . map second' . runCayley

instance (Functor f, Choice p) => Choice (Cayleyed f p) where
  left'  = Cayley . map left'  . runCayley
  right' = Cayley . map right' . runCayley

instance (Applicative f, Category p) => Category (Cayleyed f p) where
  id                            = Cayley $ pure id
  (Cayley fpbc) . (Cayley fpab) = Cayley $ liftA2 (.) fpbc fpab

instance (Applicative f, Arrow p) => Arrow (Cayleyed f p) where
  arrow f                     = Cayley $ pure               $ arrow f
  first                       = Cayley . map first          . runCayley
  second                      = Cayley . map second         . runCayley
  (Cayley ab) *** (Cayley cd) = Cayley $ liftA2 (***) ab cd
  (Cayley ab) &&& (Cayley ac) = Cayley $ liftA2 (&&&) ab ac

instance (Applicative f, ArrowChoice p) => ArrowChoice (Cayleyed f p) where
  left                        = Cayley . map left . runCayley
  right                       = Cayley . map right . runCayley
  (Cayley ab) +++ (Cayley cd) = Cayley $ liftA2 (+++) ab cd
  (Cayley ac) \|/ (Cayley bc) = Cayley $ liftA2 (\|/) ac bc

instance (Applicative f, ArrowLoop p) => ArrowLoop (Cayleyed f p) where
  loop = Cayley . map loop . runCayley

instance (Applicative f, ArrowZero p) => ArrowZero (Cayleyed f p) where
  zeroArrow = Cayley $ pure zeroArrow

instance (Applicative f, ArrowPlus p) => ArrowPlus (Cayleyed f p) where
  (Cayley f) <++> (Cayley g) = Cayley (liftA2 (<++>) f g)

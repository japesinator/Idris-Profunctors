module Data.Profunctor.Cayley

import Data.Profunctor
import Data.Profunctor.Monad

record Cayleyed : (Type -> Type) -> (Type -> Type -> Type) ->
                                     Type -> Type -> Type where
  Cayley : (runCayley : f (p a b)) -> Cayleyed f p a b

instance Functor f => ProfunctorFunctor (Cayleyed f) where
  promap f (Cayley p) = Cayley (map f p)

instance (Functor f, Monad f) => ProfunctorMonad (Cayleyed f) where
  proreturn          = Cayley . return
  projoin (Cayley m) = Cayley $ m >>= runCayley

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

module Data.Profunctor.Tambara

import Control.Arrow
import Control.Category
import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad

||| Tambara adjoins a Strong structure to any Profunctor
data Tambarred : {c : Type} -> (Type -> Type -> Type) ->
                 Type -> Type -> Type where
  Tambara : p (Pair a c) (Pair b c) -> Tambarred {c} p a b

runTambara : Tambarred {c} p a b -> p (Pair a c) (Pair b c)
runTambara (Tambara p) = p

instance Profunctor p => Profunctor (Tambarred {c} p) where
  dimap f g (Tambara p) = Tambara $ dimap (mapFst f) (mapFst g) p
    where
      -- Ticks are used in local functions because otherwise idris gets super
      --   confused about names
      mapFst : (a' -> b') -> (a', c') -> (b',    c')
      mapFst   f'            (a', b') =  (f' a', b')

instance ProfunctorFunctor (Tambarred {c}) where
  promap f _ _ (Tambara p) = Tambara $ f <-$-> p

instance Category p => Category (Tambarred {c} p) where
  id                        = Tambara id
  (Tambara p) . (Tambara q) = Tambara (p . q)

instance Arrow p => Arrow (Tambarred {c} p) where
  arrow          f  = Tambara $ first $ arrow f
  first (Tambara f) = Tambara (arrow go . first f . arrow go)
    where
      -- Ticks are used in local functions because otherwise idris gets super
      --   confused about names
      go : ((a',b'),c') -> ((a',c'),b')
      go   ((x',y'),z') =  ((x',z'),y')
  second         f  = arrow swap >>> first f >>> arrow swap
    where
      -- Ticks are used in local functions because otherwise idris gets super
      --   confused about names
      swap : (a',b') -> (b',a')
      swap   (x',y') =  (y',x')
  f      ***     g  = first f >>> second g
  f      &&&     g  = arrow (\b => (b,b)) >>> f *** g

instance Choice p => Choice (Tambarred {c} p) where
  left' (Tambara p) = Tambara $ dimap hither yon $ left' p
    where
      hither : (Either  y      z,    s) ->  Either  (y, s) (z, s)
      hither   (Left    y,           s)  =  Left    (y, s)
      hither   (Right          z,    s)  =  Right          (z, s)
      yon    :  Either (y, s) (z, s)    -> (Either   y      z,   s)
      yon      (Left   (y, s))           = (Left     y,          s)
      yon      (Right         (z, s))    = (Right           z,   s)

instance Profunctor p => Functor (Tambarred {c} p a) where
  map = rmap

instance (Profunctor p, Arrow p) => Applicative (Tambarred {c} p a) where
  pure x  = arrow (const x)
  f <*> g = arrow (uncurry id) . (f &&& g)

||| Pastroyed is left adjunct to Tambarred
data Pastroyed : (Type -> Type -> Type) -> Type -> Type -> Type where
  Pastro : ((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastroyed p a b

instance Profunctor p => Profunctor (Pastroyed p) where
  dimap f g (Pastro l m r) = Pastro (g . l) m (r . f)
  lmap  f   (Pastro l m r) = Pastro      l  m (r . f)
  rmap    g (Pastro l m r) = Pastro (g . l) m  r

instance ProfunctorFunctor Pastroyed where
  promap f _ _ (Pastro l m r) = Pastro l (f <-$-> m) r

||| Cotambara is Tambara for Choice instead of Strong
data Cotambarred : {c : Type} -> (Type -> Type -> Type) ->
                 Type -> Type -> Type where
  Cotambara : p (Either a c) (Either b c) -> Cotambarred {c} p a b

runCotambara : Cotambarred {c} p a b -> p (Either a c) (Either b c)
runCotambara (Cotambara p) = p

instance Profunctor p => Profunctor (Cotambarred {c} p) where
  dimap f g (Cotambara p) = Cotambara $ dimap (mapLeft f) (mapLeft g) p
    where
      mapLeft : (a' -> b') -> Either a' c' -> Either b'     c'
      mapLeft   f'            (Left  a')    = Left   (f' a')
      mapLeft   _             (Right    b') = Right         b'

instance ProfunctorFunctor (Cotambarred {c}) where
  promap f _ _ (Cotambara p) = Cotambara $ f <-$-> p

instance Category p => Category (Cotambarred {c} p) where
  id                            = Cotambara $ id
  (Cotambara f) . (Cotambara g) = Cotambara   (f . g)

instance Profunctor p => Functor (Cotambarred {c} p a) where
  map = rmap

||| Copastro is left adjunct to Cotambara
data Copastroyed : (Type -> Type -> Type) -> Type -> Type -> Type where
  Copastro : (Either y z -> b) -> p x y -> (a -> Either x z) -> Copastroyed p a b

instance Profunctor p => Profunctor (Copastroyed p) where
  dimap f g (Copastro l m r) = Copastro (g . l) m (r . f)
  lmap  f   (Copastro l m r) = Copastro      l  m (r . f)
  rmap    g (Copastro l m r) = Copastro (g . l) m  r

instance ProfunctorFunctor Copastroyed where
  promap f _ _ (Copastro l m r) = Copastro l (f <-$-> m) r

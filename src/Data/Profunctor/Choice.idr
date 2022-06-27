module Data.Profunctor.Choice

import Data.Either
import Data.Morphisms
import Data.Profunctor
import Control.Arrow
import Control.Category

%default total

-- }}}
-- Choice
-- {{{

||| Generalized DownStar of a Costrong Functor
public export
interface Profunctor p => Choice (p : Type -> Type -> Type) where
  ||| Like first' but with sum rather than product types
  |||
  ||| ````idris example
  ||| left' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  left' : p a b -> p (Either a c) (Either b c)
  left' = dimap mirror mirror . right'

  ||| Like second' but with sum rather than product types
  |||
  ||| ````idris example
  ||| right' (Kleisli $ \x => Just $ reverse x)
  ||| ````
  |||
  right' : p a b -> p (Either c a) (Either c b)
  right' = dimap mirror mirror . left'

export
implementation Monad m => Choice (Kleislimorphism m) where
  left'  f = Kleisli $ either (applyKleisli       $ f        >>> arrow Left)
                              (applyKleisli       $ arrow id >>> arrow Right)
  right' f = Kleisli $ either (applyKleisli {f=m} $ arrow id >>> arrow Left)
                              (applyKleisli       $ f        >>> arrow Right)

export
implementation Choice Morphism where
  left'  (Mor f) = Mor $ either (Left . f) Right
  right' (Mor f) = Mor $ either Left (Right . f)

export
implementation Choice Tagged where
  left'  = Tag . Left  . runTagged
  right' = Tag . Right . runTagged

export
implementation Applicative f => Choice (UpStarred f) where
  left'  (UpStar f) = UpStar $ either (map Left . f   ) (map Right . pure)
  right' (UpStar f) = UpStar $ either (map Left . pure) (map Right . f   )

export
implementation Monoid r => Choice (Forgotten r) where
  left'  (Forget k) = Forget .      either k $ const neutral
  right' (Forget k) = Forget . flip either k $ const neutral

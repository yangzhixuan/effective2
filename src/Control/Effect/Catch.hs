module Control.Effect.Catch where
import Control.Effect

data Catch k where
  Catch :: k -> k -> Catch k
  deriving Functor

catch :: Member Catch sig => Prog sig a -> Prog sig a -> Prog sig a
catch p q = injCall (Scp (Catch (fmap return p) (fmap return q)))

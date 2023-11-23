{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import qualified Control.Monad.Trans.Writer as W
import Data.HFunctor ( HFunctor(..) )

instance HFunctor (W.WriterT w) where
  hmap h (W.WriterT mx) = W.WriterT (h mx)

data Tell w k where
  Tell :: w -> k -> Tell w k
  deriving Functor

tell :: (Member (Tell w) effs, Monoid w) => w -> Prog effs ()
tell w = (Call . inj) (Alg (Tell w (return ())))

writerAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg oalg = undefined

writerFwd
  :: Monad m
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (W.WriterT w m) x -> W.WriterT w m x)
writerFwd alg = undefined

writer :: Monoid w => Handler '[Tell w] '[W.WriterT w] '[(,) w] '[] 
writer = handler (fmap swap . W.runWriterT) writerAlg writerFwd


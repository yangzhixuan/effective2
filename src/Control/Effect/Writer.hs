{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import Control.Monad.Trans.Class (MonadTrans, lift)
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
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg oalg eff
  | Just (Alg (Tell w k)) <- prj eff =
      do W.tell w
         return k

writerFwd
  :: (Monad m, Monoid w)
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (W.WriterT w m) x -> W.WriterT w m x)
writerFwd alg (Eff (Alg x)) = lift (alg (Eff (Alg x)))
writerFwd alg (Eff (Scp x)) = W.WriterT (alg (Eff (Scp (fmap W.runWriterT x))))
writerFwd alg (Effs effs)   = writerFwd (alg . Effs) effs

writer :: Monoid w => Handler '[Tell w] '[W.WriterT w] '[(,) w] '[]
writer = handler (fmap swap . W.runWriterT) writerAlg writerFwd

-- TODO: The following causes GHC to panic!
-- writer_ :: Monoid w => Handler '[Tell w] '[W.WriterT w] '[] '[]
-- writer_ = writer { run = \oalg -> fmap (CNil . fst) . W.runWriterT . hdecomps }

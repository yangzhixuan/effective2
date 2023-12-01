{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.Writer as W
import Data.HFunctor ( HFunctor(..) )
import Data.Functor.Composes (Comps(CNil))

data Tell w k where
  Tell :: w -> k -> Tell w k
  deriving Functor

tell :: (Member (Tell w) effs, Monoid w) => w -> Prog effs ()
tell w = (Call . inj) (Alg (Tell w (return ())))

writerAlg
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg _ eff
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

writer :: Monoid w => Handler '[Tell w] '[] '[(,) w]
writer = handler (fmap swap . W.runWriterT) writerAlg writerFwd

-- A silent writer. Bonus marks for making this useful.
writer_ :: Monoid w => Handler '[Tell w] '[] '[]
writer_ = Handler $ Handler' (\oalg -> fmap (CNil . fst) . W.runWriterT) writerAlg writerFwd

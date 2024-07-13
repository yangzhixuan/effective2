{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Writer where
import Control.Effect
import Data.Tuple (swap)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Identity
import Control.Family.Algebraic
import Control.Family.Scoped
import qualified Control.Monad.Trans.Writer as W
import Data.HFunctor


type Tell w = Alg (Tell' w)
data Tell' w k where
  Tell :: w -> k -> Tell' w k
  deriving Functor

tell :: (Monoid w) => w -> Progs '[Tell w] ()
tell w = (Call . inj) (Alg (Tell w (return ())))

writerAlg
  :: (Monad m, Monoid w)
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs '[Tell w] (W.WriterT w m) x -> W.WriterT w m x)
writerAlg _ eff
  | Just (Alg (Tell w k)) <- prj eff =
      do W.tell w
         return k

writer :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] '[(,) w]
writer = handler (fmap swap . W.runWriterT) writerAlg

writer_ :: Monoid w => Handler '[Tell w] '[] '[W.WriterT w] '[]
writer_ = handler (fmap fst . W.runWriterT) writerAlg


type Censor w = Scp (Censor' w)
data Censor' w k where
  Censor :: (w -> w) -> k -> Censor' w k
  deriving Functor

censor :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig a
censor cipher p = (Call . inj) (Scp (Censor cipher (fmap return p)))

censors :: forall w . Monoid w => (w -> w) -> Handler '[Tell w, Censor w] '[Tell w]  '[ReaderT (w -> w)] '[]
censors cipher = handler run alg where
  run :: Monad m => (forall x. ReaderT (w -> w) m x -> m (x))
  run (ReaderT mx) = mx cipher

  alg :: Monad m
      => (forall x. Effs '[Tell w] m x -> m x)
      -> (forall x. Effs '[Tell w, Censor w] (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  alg oalg eff
    | Just (Alg (Tell w k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Eff (Alg (Tell (cipher w) k))))
    | Just (Scp (Censor (cipher' :: w -> w) k)) <- prj eff =
        do cipher <- ask
           lift (runReaderT k (cipher . cipher'))
           -- lift (oalg (Effs (Eff (Scp (Censor cipher' (runReaderT k (cipher . cipher')))))))

  fwd :: Monad m
      => (forall x. Effs sig m x -> m x)
      -> (forall x. Effs sig (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  fwd oalg c = ReaderT (\f -> oalg $ hmap (flip runReaderT f) c)

uncensors :: forall w . Monoid w => Handler '[Censor w] '[] '[IdentityT] '[]
uncensors = handler run alg where
  run :: Monad m => (forall x. IdentityT m x -> m x)
  run (IdentityT mx) = mx

  alg :: Monad m
      => (forall x. Effs '[] m x -> m x)
      -> (forall x. Effs '[Censor w] (IdentityT m) x -> IdentityT m x)
  alg oalg (Eff (Scp (Censor (_ :: w -> w) k))) = k

-- NOTE: this cannot be done as the fusion of `censorsTell` and `censorsCensor`,
-- since `tell` must be sensitive to any encapsulating `censor`.
recensors :: forall w . Monoid w => (w -> w) -> Handler '[Tell w, Censor w]  '[Tell w, Censor w] '[ReaderT (w -> w)] '[]
recensors cipher = handler run alg where
  run :: Monad m => (forall x. ReaderT (w -> w) m x -> m x)
  run = ($ cipher) . runReaderT

  alg :: Monad m
      => (forall x. Effs '[Tell w, Censor w] m x -> m x)
      -> (forall x. Effs '[Tell w, Censor w] (ReaderT (w -> w) m) x -> ReaderT (w -> w) m x)
  alg oalg eff
    | Just (Alg (Tell w k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Eff (Alg (Tell (cipher w) k))))
    | Just (Scp (Censor (cipher' :: w -> w) k)) <- prj eff =
        do cipher <- ask
           lift (oalg (Effs (Eff (Scp (Censor cipher' (runReaderT k (cipher . cipher')))))))
  -- | Just (Alg (Tell w k)) <- prj eff =
  --     do W.tell w
  --        return k
  -- | Just (Scp (Censor f p)) <- prj eff =
  --     do W.censor f p

{-|
Module      : Control.Effect.Scoped
Description : The scoped effect family
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Scoped where

import Control.Effect

import Data.Kind ( Type )
import Data.HFunctor

import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

-- A scoped operation has the following type:
--
-- > newtype Scp (sig :: Type -> Type)
-- >             (f :: Type -> Type)
-- >             k
-- >             = Scp (sig (f k))
--
-- We can optimise the constructor by using a Coyoneda representation so that
-- instead the constructor becomes:
--
-- > forall x y . Scp !(sig x) !(x -> f y) !(y -> k)
--
-- But this creates 2 additional fields, and `hmap` is not often used.
-- Benchmarks reveal that applying coyoneda only to the data yields
-- marginally less allocation and time.

-- | The family of scoped operations. Forwarding scoped operations through a
-- transformer must be given explicitly using the `Forward` class.
data Scp (sig :: Type -> Type)
         (f :: Type -> Type)
         k
         = forall x . Scp !(sig (f x)) !(x -> k)

instance Functor (Scp sig f) where
  {-# INLINE fmap #-}
  fmap f (Scp x k) = Scp x (f . k)

instance Functor sig => HFunctor (Scp sig) where
  {-# INLINE hmap #-}
  hmap h (Scp x k) = Scp (fmap h x) k

instance Functor sig => Forward (Scp sig) IdentityT where
  {-# INLINE fwd #-}
  fwd alg (Scp op k) = IdentityT (alg (Scp (fmap runIdentityT op) k))

instance Functor sig => Forward (Scp sig) (ExceptT e) where
  {-# INLINE fwd #-}
  fwd alg (Scp op k) = ExceptT (alg (Scp (fmap runExceptT op) (fmap k)))

instance Functor sig => Forward (Scp sig) MaybeT where
  {-# INLINE fwd #-}
  fwd alg (Scp op k) = MaybeT (alg (Scp (fmap runMaybeT op) (fmap k)))

instance Functor sig => Forward (Scp sig) (StateT s) where
  {-# INLINE fwd #-}
  fwd alg (Scp op k) = StateT (\s -> (alg (Scp (fmap (flip runStateT s) $ op) (\(z, s) -> (k z, s)))))

instance Functor sig => Forward (Scp sig) (WriterT s) where
  {-# INLINE fwd #-}
  fwd alg (Scp op k) = WriterT (alg (Scp (fmap runWriterT op) (\(z, s) -> (k z, s))))

instance Functor sig => Forward (Scp sig) (ReaderT w) where
  {-# INLINE fwd #-}
  fwd alg (Scp op k) = ReaderT (\r -> alg (Scp (fmap (flip runReaderT r) op) k))

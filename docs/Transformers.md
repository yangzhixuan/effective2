Internal transformer handlers
-----------------------------

```haskell
{-# LANGUAGE DataKinds #-}

module Transformers where

import Data.Kind ( Type )

import Control.Effect
import Control.Monad.Trans.Class
import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Composes
import Data.HFunctor.HComposes
```

The transformer stack argument to handlers may seem superfluous. One attempt to
hide it from the interface is to use an existential:
```haskell
type Handler'
  :: [Signature]                         -- effs  : input effects
  -> [Type -> Type]                      -- f     : carrier type
  -> [Signature]                         -- oeffs : output effects
  -> Type
data Handler' effs fs oeffs =
  forall ts . (All MonadTrans ts,  Monad (HComps ts Identity))
  => Handler' (Handler effs ts fs oeffs)
```
This can then be used with a modified `handle'` function:
```haskell
handle' :: forall ieffs fs a .
  ( Recompose fs )
  => Handler' ieffs fs '[]
  -> Prog ieffs a -> (Composes fs a)
handle' (Handler' h) p  = handle h p
```
A benefit is that end users do not need to concern themselves with the transformer
stack that is passed around.

The problem is that that the `fuse` function cannot work with the `All
MonadTrans` constraint properly:
```haskell ignore
fuse'
  :: Handler' effs1 fs1 oeffs1
  -> Handler' effs2 fs2 oeffs2
  -> Handler' (effs1 `Union` effs2) (fs2 :++ fs1) ((oeffs1 :\\ effs2) `Union` oeffs2 )
fuse' (Handler' h1) (Handler' h2) = Handler' (fuse h1 h2)
```
This fails with
```
• Could not deduce ‘All MonadTrans (ts :++ ts1)’
```

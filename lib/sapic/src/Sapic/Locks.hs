-- |
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.Locks (
    annotateLocks
) where
-- import Data.Maybe
-- import Data.Foldable
import Control.Exception
import Control.Monad.Fresh
import Control.Monad.Catch
import qualified Data.Traversable as T
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Sapic.Annotation
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh

newtype LocalException = LocalException WFLockTag deriving (Show)
instance Exception LocalException

annotateEachClosestUnlock :: MonadThrow m => 
                            Theory.Sapic.SapicTerm
                             -> AnLVar
                             -> AnProcess ProcessAnnotation
                             -> m( AnProcess ProcessAnnotation)
annotateEachClosestUnlock t v (ProcessNull a') = return $ ProcessNull a'
annotateEachClosestUnlock t v (ProcessAction (Unlock t') a' p) = 
            if t == t' then -- TODO do we need more precise equality? test this
                return $ ProcessAction (Unlock t') (a' `mappend` annUnlock v) p
            else do
                p' <- annotateEachClosestUnlock t v p
                return $ProcessAction (Unlock t') a' p'
annotateEachClosestUnlock t v (ProcessAction Rep _ _) = throwM $ LocalException WFRep
annotateEachClosestUnlock t a (ProcessComb Parallel _ _ _) = throwM $ LocalException WFPar
annotateEachClosestUnlock t v (ProcessAction ac a' p) = do p' <- annotateEachClosestUnlock t v p
                                                           return $ ProcessAction ac a' p'
annotateEachClosestUnlock t v (ProcessComb c a' pl pr ) = do pl' <- annotateEachClosestUnlock t v pl
                                                             pr' <- annotateEachClosestUnlock t v pr
                                                             return $ ProcessComb c a' pl' pr'

annotateLocks :: ( MonadThrow m,
                   MonadFresh m
                 -- , Monoid (m (AnProcess ProcessAnnotation))
                  -- ,Foldable (AnProcess ProcessAnnotation)
                )
                    => AnProcess ProcessAnnotation -> m (AnProcess ProcessAnnotation)
annotateLocks (ProcessAction (Lock t) a p) = do 
            v <- freshLVar "lock" LSortMsg
            p' <- annotateEachClosestUnlock t (AnLVar v) p
            p'' <- annotateLocks p'
            -- return (ProcessAction (Lock t) (a `mappend` annLock (AnLVar v)) p')
            return (ProcessAction (Lock t) (annLock (AnLVar v)) p'')
annotateLocks (ProcessAction ac an p) = do
            p' <- annotateLocks p
            return (ProcessAction ac an p')
annotateLocks (ProcessNull an ) = 
            return (ProcessNull an)
annotateLocks (ProcessComb comb an pl pr ) = do
            pl' <- annotateLocks pl
            pr' <- annotateLocks pr
            return (ProcessComb comb an pl' pr')
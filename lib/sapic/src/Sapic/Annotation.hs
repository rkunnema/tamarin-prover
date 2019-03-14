{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- {-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- Copyright   : (c) 2019 Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- TODO
module Sapic.Annotation (
    ProcessAnnotation(..)
    , AnnotatedProcess
    , annLock
    , annUnlock
    , toAnProcess
    , toProcess
    , AnLVar (..)
    , GoodAnnotation
) where
import           Data.Data
-- import Data.Maybe
-- import Data.Foldable
-- import Control.Exception
-- import Control.Monad.Fresh
-- import Control.Monad.Catch
-- import Sapic.Exceptions
-- import Theory
import Theory.Sapic
import           GHC.Generics                     (Generic)
import           Data.Binary
-- import Theory.Model.Rule
-- import Data.Typeable
-- import qualified Data.Set                   as S
-- import Control.Monad.Trans.FastFresh
-- import Control.Monad.Trans.FastFresh
import Term.LTerm

newtype AnLVar = AnLVar LVar
     deriving( Typeable, Data, Generic, Binary, Show )
     -- original definition: deriving( Typeable, Data, Generic, NFData, Binary )

instance Semigroup AnLVar where  -- override annotations if necessary
    (<>) _ b = b

class GoodAnnotation a where
    getProcessNames :: a ->  [String]

data ProcessAnnotation = ProcessAnnotation {
    processnames :: [String]
  , lock :: Maybe AnLVar 
  , unlock :: Maybe AnLVar  } deriving (Show, Typeable)

-- Minimum requirement for process annotations: carry enough information to
-- annotate the multiset rewrite rules with:
--      - the Name or Names of the process (e.g., [A, B] in let B = 0 let A = B | 0)
instance GoodAnnotation ProcessAnnotation
    where
        getProcessNames = processnames
  
instance Monoid ProcessAnnotation where
    mempty = ProcessAnnotation [] Nothing Nothing
    mappend p1 p2 = ProcessAnnotation 
        (processnames p1 `mappend` processnames p2)
        (lock p1 `mappend` lock p2)
        (unlock p1 `mappend` unlock p2)

instance Semigroup ProcessAnnotation where
    (<>)  _ p2 =  p2
    -- ProcessAnnotation 
    --     (processnames p1 `mappend` processnames p2)
    --     (lock p1 `mappend` lock p2)
    --     (unlock p1 `mappend` unlock p2)


newtype AnnotatedProcess = AnProcess ProcessAnnotation
    deriving (Typeable, Monoid,Semigroup,Show)

-- deriving instance (Monoid a,Semigroup a) => Monoid (AnProcess a)

-- deriving instance (Monad m, Monoid m') => Semigroup (FreshT m m')
-- deriving instance (Monad m, Monoid m') => Monoid (FreshT m m')

annLock :: AnLVar -> ProcessAnnotation
annLock v = ProcessAnnotation { processnames = [], lock = Just v, unlock = Nothing }
annUnlock :: AnLVar -> ProcessAnnotation
annUnlock v = ProcessAnnotation { processnames = [], lock = Nothing, unlock = Just v }

toAnProcess :: Process -> AnProcess ProcessAnnotation
toAnProcess = fmap f
    where
        f l = ProcessAnnotation { processnames = l, lock = Nothing, unlock = Nothing }

toProcess :: GoodAnnotation an => AnProcess an -> Process
toProcess = fmap f
    where
        f l = getProcessNames l

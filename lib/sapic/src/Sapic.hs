{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
-- |
-- Copyright   : (c) 2019 Robert Künnemann and Alexander Dax
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Theories with Processes to multiset rewrite rules

module Sapic (
    translate
) where
import Control.Exception
import Control.Monad.Fresh
import Control.Monad.Catch
import Sapic.Exceptions
import Theory
import Theory.Sapic
import Data.Typeable
import qualified Data.Set              as S
import Control.Monad.Trans.FastFresh   ()
import Sapic.Annotation
import Sapic.Facts
import Sapic.Locks
import Sapic.ProcessUtils
import qualified Sapic.Basetranslation as BT
import Sapic.Restrictions
import Theory.Text.Pretty


-- Translates the process (singular) into a set of rules and adds them to the theory 
translate :: (Monad m, MonadThrow m, MonadCatch m) =>
             Monoid (m (AnProcess ProcessAnnotation)) => 
             OpenTheory
             -> m OpenTheory
translate th = case theoryProcesses th of
      []  -> return th
      [p] -> do 
                an_proc <- evalFreshT (annotateLocks (toAnProcess p)) 0
                msr <- noprogresstrans an_proc -- TODO check options to chose progress translation
                th' <- foldM liftedAddProtoRule th msr
                sapic_restrictions <- generateSapicRestrictions option an_proc
                th'' <- foldM liftedAddRestriction th' sapic_restrictions
                return th''
      _   -> throw (MoreThanOneProcess :: SapicException AnnotatedProcess)
  where
    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> throwM ((RuleNameExists (render (prettyRuleName ru) ) )  :: SapicException AnnotatedProcess)
    liftedAddRestriction thy rest = case addRestriction rest thy of
        Just thy' -> return thy'
        Nothing   -> throwM ((RestrictionNameExists (render (prettyRestriction rest)))  :: SapicException AnnotatedProcess)
        -- option = RestrictionOptions { hasAccountabilityLemmaWithControl = False, hasProgress = False }
    option = RestrictionOptions False False
  -- TODO This function is not yet complete. This is what the ocaml code
  -- was doing:  
  -- let msr =  
  --     if input.op.progress 
  --     then progresstrans annotated_process
  --     else noprogresstrans annotated_process 
  -- and predicate_restrictions = print_predicates input.pred
  -- and sapic_restrictions = print_lemmas (generate_sapic_restrictions input.op annotated_process)
  -- in
  -- let msr' = if Lemma.contains_control input.lem (* equivalent to op.accountability *)
  --            then annotate_eventId msr 
  --            else msr
  -- in
  -- input.sign ^ ( print_msr msr' ) ^ sapic_restrictions ^
  -- predicate_restrictions ^ lemmas_tamarin 
  -- ^ "end"

-- | Standard translation without progress:
-- | use gen and basetranslation and add a simple Init rule.   
noprogresstrans anP = do
    msrs <- gen BT.baseTrans anP [] S.empty
    return $ map toRule (initrule:msrs)
    where 
          initrule = AnnotatedRule (Just "Init") anP [] l a r 0
          l = []
          a = [InitEmpty ] 
          r = [State LState [] S.empty]

-- | Processes through an annotated process and translates every single action
-- | according to trans. It substitutes states by pstates for replication and
-- | makes sure that tildex, list of variables in state is updated for the next
-- | call. It also performs the substituion necessary for NDC 
-- | Input: 
-- |      three-tuple of algoriths for translation of null processes, actions and combinators
-- |      annotated process
-- |      current position in this process
-- |      tildex, the set of variables in the state
gen :: (Typeable ann, Show ann, MonadCatch m ) =>
        (ann
         -> ProcessPosition -> t -> [([TransFact], [TransAction], [TransFact])],
         SapicAction
         -> ann
         -> ProcessPosition
         -> t
         -> ([([TransFact], [TransAction], [TransFact])], t),
         ProcessCombinator
         -> ann
         -> ProcessPosition
         -> t
         -> ([([TransFact], [TransAction], [TransFact])], t, t))
        -> AnProcess ann -> ProcessPosition -> t -> m ( [AnnotatedRule ann])
gen (trans_null, trans_action, trans_comb) anP p tildex  =
    do
        proc' <- processAt anP p
        case proc' of
            ProcessNull ann -> return $ mapToAnnotatedRule proc' ( trans_null ann p tildex )
            (ProcessComb NDC _ _ _) -> 
               let  subst p_new = map_prems (substStatePos p p_new) in
               do
                   l <- gen trans anP ( p++[1] ) tildex
                   r <- gen trans anP (p++[2]) tildex
                   return $ subst (p++[1]) l ++ subst (p++[2]) r
            (ProcessComb c ann _ _) ->  
                let (msrs, tildex'1, tildex'2) = trans_comb c ann p tildex in
                do
                msrs_l <- gen trans anP (p++[1]) tildex'1
                msrs_r <- gen trans anP (p++[2]) tildex'2
                return  $
                    mapToAnnotatedRule proc' msrs ++ msrs_l ++ msrs_r
            (ProcessAction  ac ann _) ->
                let (msrs, tildex') = trans_action ac ann p tildex in
                do 
                    msr' <-  gen trans anP (p++[1]) tildex' 
                    return $ mapToAnnotatedRule proc' msrs ++ msr'
    where
        map_prems f = map (\r -> r { prems = map f (prems r) })
        --  Substitute every occurence of  State(p_old,v) with State(p_new,v)
        substStatePos p_old p_new fact
             | (State s p' vs) <- fact, p'==p_old, not $ isSemiState s = State LState p_new vs
             | otherwise = fact
        trans = (trans_null, trans_action, trans_comb)
        -- convert prems, acts and concls generated for current process
        -- into annotated rule
        toAnnotatedRule proc (l,a,r) = AnnotatedRule Nothing proc p l a r 
        mapToAnnotatedRule proc l = -- distinguishes rules by  adding the index of each element to it
            snd $ foldl (\(i,l') r -> (i+1,l' ++ [toAnnotatedRule proc r i] )) (0,[]) l

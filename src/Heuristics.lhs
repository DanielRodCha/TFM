\begin{code}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Heuristics
    ( heuristics
    ) where

--import PolAux
import Math.CommutativeAlgebra.Polynomial(vars)

import qualified Data.Set as S
import Data.List (foldl', sortOn)
import F2
-------------------------------------------------------------------------------
-- | The data type Heuristic is the rule that dictates in which order variables
-- are chosen.



-------------------------------------------------------------------------------

frequency ps v = length $ filter (== v) $ foldl' (\acc p -> (vars p) ++ acc) [] ps

heuristics ps vs = sortOn (frequency ps) vs

--saturaKB :: (S.Set PolF2,[PolF2]) -> Bool
--saturaKB (ps,[])                   = S.notMember 0 ps
--saturaKB (ps,v:vs) | S.member 0 ps = False
--                   | otherwise     = saturaKB (aux, heuristics aux vs)
--                       where aux = omiteVariableKB v ps
\end{code}

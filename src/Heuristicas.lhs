\begin{code}
module Heuristicas where

import Haskell4Maths (var
                     , vars)
import F2
import Preprocesado (dimacsAPolinomios)
import Saturacion (omiteVariableKB)

import Data.List (foldl', sortOn)
import qualified Data.Set as S
\end{code}

 A continuación, se define el tipo \texttt{Heuristica}. Este es una función que
 recibe un conjunto de polinomios y una lista de sus variables, y devuelve una
 lista ordenada de dichas variables.

\index{\texttt{Heurisitica}}
\begin{code}

type Heuristica = S.Set PolF2 -> [PolF2] -> [PolF2]

\end{code}

 La primera heurística es la inducida por el orden monomial, en este caso el
 lexicográfico. Como por construcción, $vs$ ya está ordenada de tal forma, la
 heurística \texttt{(heuristicaOM ps vs)} devuelve invariante la lista $vs$.

\index{\texttt{heuristicaOrdMon}}
\begin{code}
-- | Por ejemplo:
--
-- >>> [x1,x2] = map var ["x1","x2"] :: [PolF2]
-- >>> heuristicaOrdMon (S.fromList [x1,x2,x1+1]) [x1,x2]
-- [x1,x2]
heuristicaOrdMon :: Heuristica
heuristicaOrdMon ps vs = vs

\end{code}

\newpage

 La segunda heurística \texttt{(heuristicaFrecuencia ps vs)} devuelve una lista
 con las variables de $vs$ ordenadas de menor a mayor frecuencia de aparición en los
 polinomios de $ps$.

\index{\texttt{heuristicaFrecuencia}}
\begin{code}
-- | Por ejemplo:
--
-- >>> [x1,x2] = map var ["x1","x2"] :: [PolF2]
-- >>> heuristicaFrecuencia (S.fromList [x1,x2,x1+1]) [x1,x2]
-- [x2,x1]

heuristicaFrecuencia :: Heuristica
heuristicaFrecuencia ps vs = sortOn frecuencia vs
   where frecuencia v = length ( filter (== v) ps')
         ps' = foldl' (\acc p -> (vars p) ++ acc) [] ps

\end{code}

 Finalmente, la heurística \texttt{(heuristicaFrecRev ps vs)} devuelve una
 lista con las variables de $vs$ ordenadas de mayor a menor frecuencia de aparición en
 los polinomios de $ps$.

\index{\texttt{heuristicaFrecRev}}
\begin{code}
-- | Por ejemplo:
--
-- >>> [x1,x2] = map var ["x1","x2"] :: [PolF2]
-- >>> heuristicaFrecRev (S.fromList [x1,x2,x1+1]) [x1,x2]
-- [x1,x2]

heuristicaFrecRev :: Heuristica
heuristicaFrecRev ps = (reverse . heuristicaFrecuencia ps)

\end{code}

 Para introducir esta variante es necesario que se ordene la lista de variables
 cada vez que se olvide una de ellas ya que también se modifican los polinomios
 y, por ejemplo, las frecuencias cambiarían. Es por esto que se redefinirá las
 funciones \texttt{saturaKB} y \texttt{satSolver} tal y como sigue:

\index{\texttt{saturaKB}}
\index{\texttt{satSolver}}
\begin{code}
saturaKB :: (S.Set PolF2,[PolF2]) -> Heuristica -> Bool
saturaKB (ps,[])   h                 = S.notMember 0 ps
saturaKB (ps,v:vs) h | S.member 0 ps = False
                     | otherwise     = saturaKB (aux, h aux vs) h
                       where aux     = omiteVariableKB v ps

satSolver h f = do
  f' <- dimacsAPolinomios f
  return (saturaKB f' h)
\end{code}


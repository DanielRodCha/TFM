\begin{code}

module Saturacion where

import Data.List
import Data.Char (isSpace)
import Data.Foldable (sum, product)
import System.Environment

import qualified Data.Set as S


import Haskell4Maths (var
                     , vars
                     , zerov)
import F2
import Transformaciones ( phi)
import Regla (reglaIndependencia)
import Preprocesado
\end{code}

 Sin embargo, antes de implementar estas funciones hay una modificación que
 mejora la eficiencia de las funciones \texttt{(reglaIndependenciaAux} y
 \texttt{(reglaIndependenciaKB)}. Esta mejora se basa en el hecho de
 que si en algún 
 momento de la computación hay un cero en el conjunto de polinomios (que
 traducido a fórmula es un $\bot$) éste permanecerá hasta finalizar la
 saturación. De hecho, tras saturar dicho conjunto, será el único polinomio que
 esté en el conjunto (junto con el 1, correspondiente a la tautología $\top$, y
 se puede obviar si aparece acompañado). Por tanto, aplicando el corolario
 \ref{cor:cero}, la base de conocimiento original es inconsistente.\\

 Teniendo en cuenta lo comentado anteriormente, se pueden modificar las
 definiciones anteriores de \texttt{(reglaIndependenciaAux} y
 \texttt{(reglaIndependenciaKB} para obtener un método de saturación más
 eficiente. Para ello basta añadir al bucle de la primera la siguiente línea de
 código:\\

\texttt{| dR == 0   = S.fromList [0]}\\

Quedando la implementación de dicha función tal y como sigue:

\begin{code}
reglaIndependenciaAux :: PolF2 -> PolF2 -> S.Set PolF2 ->
                            S.Set PolF2 -> S.Set PolF2
reglaIndependenciaAux v p ps acum
  | S.null ps = acum
  | dR == 0   = S.fromList [0]
  | otherwise = reglaIndependenciaAux v p ps' (S.insert dR acum)
                where (p',ps') = S.deleteFindMin ps
                      dR       = reglaIndependencia v p p'
\end{code}

 En cuanto a la función \texttt{(reglaIndependenciaKB}, si en algún momento de
 la computación el acumulador es el conjunto cuyo único elemento es el 0,
 querrá decir que se ha obtenido al aplicar la regla de independencia. Por
 tanto la base de conocimiento de la que proviene dicho conjunto de polinomios
 es inconsistente. Para implementar esto sólo se debe añadir al principio del
 bucle la siguiente línea:\\ 

\texttt{| acum == S.fromList [0] = S.fromList [0]} \\

 Y por tanto, la función queda:

\begin{code}
reglaIndependenciaKB :: PolF2 -> S.Set PolF2 ->
                  S.Set PolF2 -> S.Set PolF2
reglaIndependenciaKB v pps acum
  | acum == S.fromList [0] = S.fromList [0]
  | S.null pps   = acum
  | otherwise    = reglaIndependenciaKB v ps
                   (reglaIndependenciaAux v p pps acum)
      where (p,ps) = S.deleteFindMin pps
\end{code}

 Usando esta mejora, ya se está en condiciones de implementar las funciones que
 ejecutan la saturación.\\

 La función \texttt{(omiteVariableKB v ps)} devuelve el conjunto de polinomios
 obtenido tras aplicar la regla de independencia respecto de la variable $v$
 entre cada uno de los polinomios del conjunto $ps$. En caso de que como
 resultado de aplicar dicha regla se obtenga el polinomio cero, los cálculos se
 detendrán y se devolverá un conjunto unitario cuyo único elemento sea el cero.

\begin{code}
-- | Por ejemplo,
-- >>> x1 = (var "x1") :: PolF2
-- >>> x2 = (var "x2") :: PolF2
-- >>> omiteVariableKB x2 (S.fromList [x2,x1*x2,x1+1])
-- fromList [x1,x1+1,1]
-- >>> omiteVariableKB x1 (S.fromList [x1,x1+1,1])
-- fromList [0]

omiteVariableKB :: PolF2 -> S.Set PolF2 -> S.Set PolF2
omiteVariableKB v ps = reglaIndependenciaKB v ps1 ps2
       where (ps1,ps2) = S.partition (\p -> elem v (vars p)) ps
\end{code}

 Conviene destacar que se divide el conjunto original de polinomios en dos,
 según si ocurre la variable que se quiere omitir o no. De esta forma se evitan
 cálculos redundantes.\\

 La función que satura el conjunto $ps$ usando la regla de independencia según un
 orden dado por la lista $vs$ es \texttt{(saturaKB (ps,vs))}. Dicha función
 devuelve \texttt{True} si la fórmula original de la que proviene el conjunto
 de polinomios $ps$ es satisfacible, y \texttt{False} si es insatisfacible.

\begin{code}                            
-- | Por ejemplo,
--
-- >>> saturaKB (S.fromList[1],[])
-- True
-- >>> x1 = (var "x1") :: PolF2
-- >>> saturaKB (S.fromList[x1,x1+1],[x1])
-- False

saturaKB :: (S.Set PolF2,[PolF2]) -> Bool
saturaKB (ps,[])                   = S.notMember 0 ps
saturaKB (ps,v:vs) | S.member 0 ps = False
                   | otherwise     = saturaKB (omiteVariableKB v ps, vs)
                       where nextVPS = omiteVariableKB v ps

\end{code}

 Finalmente, se combinan ambas etapas (Preprocesado y Saturación) en la función
 \texttt{satSolver f}. Esta función recibe un fichero donde se codifica una
 fórmula en formato \texttt{DIMACS} y devuelve \texttt{True} si dicha fórmula
 es satisfacible y \texttt{False} en caso contrario.

\begin{code}
-- | Por ejemplo,
--
-- >>> satSolver "exDIMACS/easy/example1.txt"
-- True
-- >>> satSolver "exDIMACS/easy/example4.txt"
-- False
-- >>> satSolver "exDIMACS/medium/exampleSat0.txt"
-- True
satSolver f = do
  f' <- dimacsAPolinomios f
  return (saturaKB f')
\end{code}

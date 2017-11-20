
\begin{code}
module SAT_Solver where

import F2
import Logica
import Regla (reglaIndependencia)
import Test.QuickCheck
import qualified Data.Set as S
\end{code}

 Destacar que si en algún momento de la computación hay un cero en el conjunto
 de polinomios (que traducido a fórmula es un $\bot$) éste nunca
 desaparecerá. De hecho, tras saturar dicho conjunto, será el único polinomio
 (junto con el 1, que corresponde a la tautología $\top$, y se puede obviar si
 aparece acompañado). De esta forma, aplicando el corolario \ref{cor:cero},
 la base de conocimiento original es inconsistente.

 Teniendo en cuenta lo comentado anteriormente, se pueden modificar las
 definiciones anteriores de \texttt{(reglaIndependenciaAux} y
 \texttt{(reglaIndependenciaKB} para obtener un método de saturación más
 eficiente. Para ello basta añadir al bucle la siguiente línea de código:\\

\texttt{| dR == 0   = S.fromList [0]}\\

Quedando esta función:

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

 En cuanto a la segunda función, si en algún momento de la computación el
 acumulador es el conjunto cuyo único elemento es el 0, querrá decir que se ha
 obtenido al aplicar la regla de independencia. Por tanto la base de
 conocimiento de la que proviene dicho conjunto de polinomios es
 inconsistente. Para implementar esto sólo se debe añadir al principio del
 bucle la siguiente línea:\\

\texttt{| acum == S.fromList [0] = S.fromList [0]} \\

\begin{code}
reglaIndependenciaKB :: PolF2 -> S.Set PolF2 ->
                  S.Set PolF2 -> S.Set PolF2
reglaIndependenciaKB v pps acum
  | S.null pps   = acum
  | otherwise    = reglaIndependenciaKB v ps
                   (reglaIndependenciaAux v p pps acum)
      where (p,ps) = S.deleteFindMin pps
\end{code}

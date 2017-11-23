\begin{code}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Preprocesado where

import Data.List

import qualified Data.Set as S

import F2
import Haskell4Maths (var
                     , zerov)
import Transformaciones ( phi)
\end{code}

 La función \texttt{(literalAPolinomio lit)} recibe una cadena que codifica un
 literal en formato \texttt{DIMACS} y devuelve un par \texttt{(p,v)} donde $p$
 es el polinomio correspondiente a dicho literal (la proyección por $\pi$) y
 $v$ es la variable que interviene en dicho polinomio. 

\index{\texttt{literalAPolinomio}}
\begin{code}
-- | Por ejemplo,
--
-- >>> literalAPolinomio "0"
-- (0,0)
-- >>> literalAPolinomio "1"
-- (x1,x1)
-- >>> literalAPolinomio "-1"
-- (x1+1,x1)

literalAPolinomio :: String -> (PolF2,PolF2)
literalAPolinomio "0"       = (zerov,zerov)
literalAPolinomio ('-':lit) = (1 + x,x)
                   where x = var ('x':lit)
literalAPolinomio lit       = (x,x)
                   where x = var ('x':lit)
\end{code}

 La función \texttt{(clausulaAPolinomio cs)} recibe una cadena que codifica una
 cláusula en formato \texttt{DIMACS} y devuelve un par \texttt{(p,vs)} donde
 $p$ es el polinomio que le corresponde según la función $\pi$ y $vs$ las
 variables que intervienen en él.

\index{\texttt{clausulaAPolinomio}}
\begin{code}
-- | Por ejemplo,
--
-- >>> clausulaAPolinomio ["1"]
-- (x1,fromList [x1])
-- >>> clausulaAPolinomio ["1","-2"]
-- (x1x2+x2+1,fromList [x1,x2])

clausulaAPolinomio :: [String] -> (PolF2, S.Set (PolF2))
clausulaAPolinomio (c:cs) | c == "c" || c == "p" = (1, S.empty)
clausulaAPolinomio cs = aux $ foldl' (\acc x -> disj (literalAPolinomio x) acc)
                                     (zerov,S.empty) cs
  where aux (a,b) = (phi a,b)
        disj (x,v) (y,vs) | v == zerov = (y,vs)
                          | otherwise   = (x + y + x*y, S.insert v vs)

\end{code}

\index{\texttt{readFile}}
 Además de las anteriores, serán necesaria tres funciones predefindas de
 Haskell. La primera es la función \texttt{readFile}, que transforma el
 archivo \texttt{.txt} en una cadena de caracteres.\\

\index{\texttt{lines}}
 También se usará la función
 \texttt{lines} que divide una cadena de caracteres en una lista de cadenas de
 la siguiente forma: empieza leyendo desde el principio y cada vez que se
 encuentra un salto de línea acaba la cadena y comienza una nueva.\\

\index{\texttt{words}}
 La tercera y última función necesaria es \texttt{words}, homóloga a la
 anterior pero que divide una cadena en función de los espacios.\\

 Finalmente, ya se está en disposición de implementar la función que reciba un
 archivo  \texttt{.txt} y devuelve un conjunto de polinomios. Además, se
 devolverá una lista ordenada que servirá más adelante para indicar las
 variables que aún no se han omitido. \\


 En definitiva, la función \texttt{(dimacsAPolinomios f)} recibe el archivo $f$
 y devuelve el par \texttt{(ps,vs)}; donde $ps$ es el conjunto de polinomios
 correspondientes (por la función $\pi$) a la fórmula codificada en el archivo
 $f$, mientras que $vs$ es la lista de variables que intervienen en alguno de
 estos polinomios.                                                

\index{\texttt{dimacsAPolinomios}}
\begin{code}
-- | Por ejemplo,
--
-- >>> dimacsAPolinomios "exDIMACS/easy/example1.txt"
-- (fromList [x1x2+x1+x2,1],[x1,x2])
-- >>> dimacsAPolinomios "exDIMACS/easy/example4.txt"
-- (fromList [x1x2+x1+x2,x1x2+x1+1,x1x2+x2+1,x1x2+1,1],[x1,x2])


dimacsAPolinomios f = do
  s0 <- readFile f
  return $
    aux1 $ (foldr (\x acc -> (aux2 ((clausulaAPolinomio . words) x) acc))
             (S.empty,S.empty)) $ lines $ s0
     where aux1 (a,b) = (a,S.toList b)
           aux2 (a,b) (acc,vs) = (S.insert  a acc, S.union vs b)
\end{code}


Para ello se crea el módulo \texttt{Derivada} y se importan los módulos necesarios.\\

\begin{code}
module Derivada (derivaPol) where

import Logica
import Haskell4Maths ( Lex
                     , lm
                     , var
                     , vars
                     , linear
                     , mindices)
import F2 (PolF2)
import Transformaciones (proyeccion
                        , theta)

import Math.CommutativeAlgebra.Polynomial

import Data.List (union)
import Test.QuickCheck
\end{code}

 Destacar que se restringirá la definición de la derivada
 $\frac{\partial}{\partial x_{p}}$ a polinomios en el espacio cociente. Esto
 implica que se supondrá que los polinomios son proyecciones de fórmulas y que
 por lo tanto, las variables que aparecen en dichos polinomios tienen a lo sumo
 exponente igual a 1.\\

 La función \texttt{(derivaMononomio m v)} es la derivada del monomio $m$
 respecto de la variable $v$, siempre que el exponente de todas sus variables
 sea menor o igual que 1.\\

\begin{code}
-- | Por ejemplo,
--
-- >>> x1 = var "x1" :: PolF2
-- >>> exampleMonomial1 = (Lex (M 1 []))
-- >>> exampleMonomial1
-- 1
-- >>> derivaMononomio exampleMonomial1 x1
-- 0
-- >>> exampleMonomial2 = (Lex (M 1 [("x1",1)]))
-- >>> exampleMonomial2
-- x1
-- >>> derivaMononomio exampleMonomial2 x1
-- 1
-- >>> exampleMonomial3 = (Lex (M 1 [("x1",1),("x2",1)]))
-- >>> exampleMonomial3
-- x1x2
-- >>> derivaMononomio exampleMonomial3 x1
-- x2
derivaMononomio :: (Lex String) -> PolF2 -> PolF2
derivaMononomio m v
  | varDif `elem` mIndices =
      product [var x ^ i | (x,i) <- mIndices, x /= fst varDif]
  | otherwise =  0
  where mIndices = mindices m
        varDif   = head (mindices (lm v))
\end{code}

 La función \texttt{(derivaPol p v)} es la derivada del polinomio $p$ respecto de
 la variable $v$, siempre que el exponente de todas sus variables sea menor o
 igual que 1.

\begin{code}
-- | Por ejemplo,
-- >>> [x1,x2,x3,x4] = (map var ["x1","x2","x3","x4"]) :: [PolF2]
-- >>> derivaPol x1 x1
-- 1
-- >>> derivaPol (1+x1+x2+x1*x2) x1
-- x2+1
-- >>> derivaPol (x1*x2+x1+x3*x4+1) x1
-- x2+1

derivaPol :: PolF2 -> PolF2 -> PolF2
derivaPol p v = linear (`derivaMononomio` v) p
\end{code}

  El siguiente resultado muestra una expresión semánticamente equivalente de
  esta derivada: 
 \prop $\frac{\partial}{\partial x_p} F \equiv \neg (F\{ p/\neg p \}
 \leftrightarrow F) $ 

 \noindent \textbf{Prueba:} Es fácil ver que
 $$\pi (F\{ p/\neg p \}) (x) = \pi (F) (x_1, \dots , x_p +1 ,\dots , x_n)$$
 \noindent Por otro lado, se cumple que para fórmulas polinomiales:
 $$\frac{\partial}{\partial x}a(x) = a(x+1)+a(x)$$
 \noindent Así que,
 $$\frac{\partial}{\partial x_p} \pi (F) = \pi (F) (x_1, \dots , x_p +1 ,\dots
 , x_n) + \pi (F) (x_1, \dots , x_n)$$ 
 \noindent Y por tanto, aplicando $\Theta$ se tiene
 $$\frac{\partial}{\partial p} F = \Theta (\frac{\partial}{\partial x_p} \, \pi
 (F)) \equiv \neg (F\{ p/\neg p \} \leftrightarrow F)$$ 
 \hspace{15cm} $\square$ \\

 Esta propiedad se implementa en Haskell de la siguiente manera:

\begin{code}
-- |
-- >>> quickCheck prop_derivada
-- +++ OK, passed 100 tests.

prop_derivada :: FProp -> Int -> Bool
prop_derivada f n = equivalentes (theta (derivaPol pol v))
                                 (no (Equi (sustituye f varP (no p)) f))
  where pol           = proyeccion f
        vs            = union (vars pol) [((var "x") :: PolF2)]
        v             = vs !! (n `mod` (length vs))
        p             = theta v
        aux (Atom xs) = xs
        varP          = aux p
\end{code}

\subsection{$\mathbb{F}_2[\textbf{x}]$ en Haskell}

 En esta subsección se realizarán las implementaciones necesarias para poder
 trabajar en Haskell con $\mathbb{F}_2[\textbf{x}]$.

\begin{code}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module F2 ( VarF2
          , PolF2
          , unbox ) where

import Haskell4Maths ( Vect
                     , Lex
                     , F2
                     , var)
import Test.QuickCheck ( Arbitrary
                       , Gen
                       , arbitrary
                       , vectorOf
                       , choose
                       , quickCheck)
\end{code}

 El primer paso tras el análisis realizado sobre la librería HaskellForMaths en
 el apartado anterior es definir el tipo de dato que representa
 $\mathbb{F}_2[\textbf{x}]$ (\texttt{PolF2}) , así como sus variables
 (\texttt{VarF2}):

\begin{code}
newtype VarF2 = Box (Vect F2 (Lex String))
  deriving (Eq, Ord)

type PolF2 = Vect F2 (Lex String)
\end{code}

 Notar que el tipo de las variables es simplemente un cambio de nombre respecto
 a los polinomios que ha sido metido dentro del constructor \texttt{Box}. Este
 artificio es necesario ya que no se pueden declarar instancias (como se hará a
 continuación) repetidas sobre un mismo tipo de dato aunque tengan nombres
 distintos. \\

 Sin embargo, es necesario definir la función auxiliar \texttt{(unbox
 x)} que saca a $x$ de la mónada \texttt{Var}:

\begin{code}
unbox :: VarF2 -> PolF2
unbox (Box x) = x
\end{code}

 Para poder mostrar por consola las variables de forma estética; es decir, sin
 mostrar el constructor \texttt{Box}, declaramos la instancia \texttt{Show}:

\begin{code}
instance Show VarF2 where
  show = show . unbox
\end{code}

 Para poder definir propiedades que involucren a estos tipos
 de datos y comprobarlas con \texttt{QuickCheck} es necesario añadir la
 instacia \texttt{Arbitrary}, así como definir generadores de dichos tipos. Se
 comenzará por el tipo \texttt{VarF2} ya que servirá como apoyo para el de los
 polinomios:

\begin{code}
instance Arbitrary VarF2 where
  arbitrary = varGen
\end{code}

 La función \texttt{varGen} es un generador de variables:

\begin{code}
varGen :: Gen VarF2
varGen = do
  n <- choose ((1::Int),100)
  return (Box (var ('x':(show n))))
\end{code}

 Se declara la instancia \texttt{Arbitrary} para el tipo de dato de los
 polinomios:

\begin{code}
instance Arbitrary PolF2 where
  arbitrary = polGen
\end{code}

 El generador aleatorio de polinomios seguirá la siguiente estructura: en
 primer lugar se generarán aleatoriamente pares de variable-exponente, con los
 que se formarán monomios. A partir de la suma de éstos se obtendrán los
 polinomios:

\begin{code}
varExpGen :: Gen (PolF2,Int)
varExpGen = do
  Box x <- varGen
  i <- choose ((1::Int),5)
  return $ (x,i)

monGen :: Gen PolF2
monGen = do
  n <- choose ((1::Int),5)
  xs <- vectorOf n varExpGen
  return $ product [ x ^ i | (x,i) <- xs]

polGen :: Gen PolF2
polGen = do
  n <- choose ((1::Int),5)
  xs <- vectorOf n monGen
  return $ sum xs
\end{code}

\subsubsection{Propiedades de $\mathbb{F}_2[\textbf{x}]$}

 Es importante comprobar que el nuevo tipo de dato que hemos definido cumple
 las propiedades básicas. Ya que el trabajo se basa en este tipo de dato y sus
 propiedades. Se comprobarán las propiedades de la suma y del producto de
 polinomios de $\mathbb{F}_2[\textbf{x}]$:

 La suma de polinomios es conmutativa, $\forall p,q \in
 \mathbb{F}_2[\textbf{x}] (p+q = q+p)$.

\begin{code}
-- |
-- >>> quickCheck prop_suma_conmutativa
-- +++ OK, passed 100 tests.
prop_suma_conmutativa :: PolF2 -> PolF2 -> Bool
prop_suma_conmutativa p q = p+q == q+p
\end{code}

 La suma de polinomios es asociativa: $\forall p,q,r \in
 \mathbb{F}_2[\textbf{x}] (p+(q+r) = (p+q)+r)$.

\begin{code}
-- |
-- >>> quickCheck prop_suma_asociativa
-- +++ OK, passed 100 tests.
prop_suma_asociativa :: PolF2 -> PolF2 -> PolF2 -> Bool
prop_suma_asociativa p q r = p+(q+r) == (p+q)+r
\end{code}

 El cero es el elemento neutro de la suma de polinomios: 

\begin{code}
-- |
-- >>> quickCheck prop_suma_neutro
-- +++ OK, passed 100 tests.
prop_suma_neutro :: PolF2 -> Bool
prop_suma_neutro p = (p + 0 == p) && (0 + p == p)
\end{code}

 Todo polinomio es simétrico de sí mismo respecto a la suma: $\forall p \in
 \mathbb{F}_2[\textbf{x}] : p+p = 0$. 

\begin{code}
-- |
-- >>> quickCheck prop_suma_simetrico
-- +++ OK, passed 100 tests.
prop_suma_simetrico :: PolF2 -> Bool
prop_suma_simetrico p = p+p == 0
\end{code}

 La multiplicación de polinomios es conmutativa: $\forall p,q \in
 \mathbb{F}_2[\textbf{x}] (p*q = q*p)$.

\begin{code}
-- |
-- >>> quickCheck prop_prod_conmutativa
-- +++ OK, passed 100 tests.
prop_prod_conmutativa :: PolF2 -> PolF2 -> Bool
prop_prod_conmutativa p q = p*q == q*p
\end{code}

 El producto es asociativo: $\forall p,q,r \in
 \mathbb{F}_2[\textbf{x}] (p*(q*r) = (p*q)*r)$.

\begin{code}
-- |
-- >>> quickCheck prop_prod_asociativo
-- +++ OK, passed 100 tests.
prop_prod_asociativo :: PolF2 -> PolF2 -> PolF2 -> Bool
prop_prod_asociativo p q r = p*(q*r) == (p*q)*r
\end{code}

 El 1 es el elemento neutro de la multiplicación de polinomios:
\begin{code}
-- |
-- >>> quickCheck prop_prod_neutro
-- +++ OK, passed 100 tests.
prop_prod_neutro :: PolF2 -> Bool
prop_prod_neutro p = (p * 1 == p) && (1 * p == p)
\end{code}

 Distributividad del producto respecto la suma: $\forall p,q,r \in
 \mathbb{F}_2[\textbf{x}] (p*(q+r) = p*q + p*r)$

\begin{code}
-- |
-- >>> quickCheck prop_distributiva
-- +++ OK, passed 100 tests.
prop_distributiva :: PolF2 -> PolF2 -> PolF2 -> Bool
prop_distributiva p q r = p*(q+r) == (p*q)+(p*r)
\end{code}

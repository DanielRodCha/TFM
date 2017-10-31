\begin{code}
module PFH where 
import Data.List
\end{code}

\section{Introducción a Haskell}

En esta sección se introducirán funciones básicas para la programación   
en Haskell. Como método didáctico, se empleará la definición de   
funciones ejemplos, así como la redefinición de funciones que Haskell
ya tiene predefinidas, con el objetivo de que el lector aprenda 
``\textit{a montar en bici, montando}''.

A continuación se muestra la definición \texttt{(cuadrado x)} es el cuadrado de \texttt{x}. 
Por ejemplo,
La definición es
\index{\texttt{cuadrado}}
\begin{code}
-- |
-- >>> cuadrado 3
-- 9
-- >>> cuadrado 4
-- 16
cuadrado :: Int -> Int
cuadrado x = x * x
\end{code}



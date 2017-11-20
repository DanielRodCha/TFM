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

\begin{code}
-- | Por ejemplo,
--
-- >>> var' "0"
-- (0,0)
-- >>> var' "1"
-- (x1,x1)
-- >>> var' "-1"
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

\begin{code}
-- | Por ejemplo,
--
-- >>> clause2pol ["1"]
-- (x1,fromList [x1])
-- >>> clause2pol ["1","-2"]
-- (x1x2+x2+1,fromList [x1,x2])

clausulaAPolinomio :: [String] -> (PolF2, S.Set (PolF2))
clausulaAPolinomio (c:cs) | c == "c" || c == "p" = (1, S.empty)
clausulaAPolinomio cs = aux $ foldl' (\acc x -> disj (literalAPolinomio x) acc)
                                     (zerov,S.empty) cs
  where aux (a,b) = (phi a,b)
        disj (x,v) (y,vs) | v == zerov = (y,vs)
                          | otherwise   = (x + y + x*y, S.insert v vs)

\end{code}

 Además de las anteriores, serán necesaria tres funciones predefindas de
 Haskell. La primera es la función \texttt{readFile}, que transforma el
 archivo \texttt{.txt} en una cadena de caracteres.\\

 También se usará la función
 \texttt{lines} que divide una cadena de caracteres en una lista de cadenas de
 la siguiente forma: empieza leyendo desde el principio y cada vez que se
 encuentra un salto de línea acaba la cadena y comienza una nueva.\\

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

\begin{code}
-- | Por ejemplo,
--
-- >>> dimacsAPolinomios "exDIMACS/easy/example1.txt"
-- (fromList [x1x2+x1+x2,1],[x1,x2])
-- >>> dimacsAPolinomios "exDIMACS/easy/example4.txt"
-- (fromList [x1x2+x1+x2,x1x2+x1+1,x1x2+x2+1,x1x2+1,1],[x1,x2])
-- >>> dimacsAPolinomios "exDIMACS/medium/exampleSat0.txt"
-- (fromList [x1x10x38+x1x10+x1x38+x1+x10x38+x10+x38,                                                      x1x19x25+x1x19+x19x25+x19+1,                                                                 x1x26x39+x1x39+1,x1x27x92+x1x27+1,x1x7x90+x1x90+x7x90+x90+1,                                 x10x14x82+x10x14+x10x82+x10+x14x82+x14+x82,x10x2x45+x10x45+x2x45+x45+1,                      x10x48x59+x10x59+x48x59+x59+1,x10x76x88+x10x76+x76x88+x76+1,                                 x100x11x52+x11x52+1,x11x28x41+x11x28+x28x41+x28+1,x11x68x77+x68x77+1,                        x12x54x92+x12x54+x12x92+x12+1,x13x52x63+x13x63+1,x13x55x57+x13x55+1,                         x13x6x78+x13x6+x13x78+x13+1,x14x34x50+x14x34+x14x50+x14+1,                                   x14x59x87+x59x87+1,x16x19x80+x16x19+1,                                                       x16x28x84+x16x28+x16x84+x16+x28x84+x28+x84,                                                  x16x73x92+x16x92+x73x92+x92+1,x16x90x96+x16x90+1,x18x55x64+x55x64+1,                         x19x3x30+x19x3+1,x19x44x50+x19x44+x44x50+x44+1,                                              x19x57x93+x19x57+x19x93+x19+1,x2x21x98+x21x98+1,                                             x2x51x67+x2x51+x2x67+x2+x51x67+x51+x67,x20x33x7+x20x7+x33x7+x7+1,                            x20x4x80+x20x80+1,x21x27x43+x21x27+x21x43+x21+x27x43+x27+x43,                                x21x61x91+x21x61+x21x91+x21+x61x91+x61+x91,x23x7x72+x23x72+1,                                x24x8x84+1,x25x28x84+x25x84+x28x84+x84+1,x25x32x99+x25x99+1,                                 x25x59x70+x25x59+x59x70+x59+1,                                                               x25x70x89+x25x70+x25x89+x25+x70x89+x70+x89,                                                  x26x53x95+x26x53+x26x95+x26+1,x28x60x8+x28x60+1,x3x35x96+x35x96+1,                           x30x55x92+x30x55+x55x92+x55+1,x31x42x89+x31x42+x42x89+x42+1,                                 x31x5x97+x5x97+1,x32x45x6+x32x45+x45x6+x45+1,x33x69x8+x33x69+1,                              x35x47x64+x35x47+1,x35x48x58+x35x48+x35x58+x35+1,x35x72x97+x35x97+1,                         x36x42x7+x36x42+1,x36x47x70+x47x70+1,x36x56x78+x36x78+x56x78+x78+1,                          x38x60x66+x38x60+x60x66+x60+1,x4x65x94+x4x65+x4x94+x4+1,                                     x42x43x59+x42x43+1,x42x44x66+x42x44+x42x66+x42+x44x66+x44+x66,                               x42x60x7+x60x7+1,x44x66x81+x66x81+1,x44x76x78+x44x78+1,                                      x45x74x98+x45x98+1,x48x52x63+x48x63+1,x48x53x75+x48x75+1,                                    x49x69x88+x49x69+x49x88+x49+x69x88+x69+x88,x5x50x83+x5x50+x50x83+x50+1,                      x50x6x70+x50x6+x6x70+x6+1,x52x71x95+x52x95+x71x95+x95+1,                                     x52x94x99+x52x94+x94x99+x94+1,                                                               x53x84x85+x53x84+x53x85+x53+x84x85+x84+x85,x54x6x67+x54x67+x6x67+x67+1,                      x55x63x90+x55x63+1,x58x60x93+x60x93+1,                                                       x59x75x9+x59x75+x59x9+x59+x75x9+x75+x9,x60x75x90+x60x75+x60x90+x60+1,                        x64x71x73+x64x71+x71x73+x71+1,x65x83x89+x65x83+x65x89+x65+1,                                 x68x75x80+x68x75+1,x68x84x88+x68x88+1,                                                       x70x90x99+x70x90+x70x99+x70+x90x99+x90+x99,x75x86x89+x75x86+1,                               x77x86x97+x86x97+1,x8x91x92+x8x91+1,x81x88x92+x81x88+1,1],                                   [x1,x10,x100,x11,x12,x13,x14,x16,x18,x19,x2,x20,x21,x23,x24,x25,x26,                          x27,x28,x3,x30,x31,x32,x33,x34,x35,x36,x38,x39,x4,x41,x42,x43,x44,                           x45,x47,x48,x49,x5,x50,x51,x52,x53,x54,x55,x56,x57,x58,x59,x6,x60,                           x61,x63,x64,x65,x66,x67,x68,x69,x7,x70,x71,x72,x73,x74,x75,x76,x77,                          x78,x8,x80,x81,x82,x83,x84,x85,x86,x87,x88,x89,x9,x90,x91,x92,x93,                           x94,x95,x96,x97,x98,x99])

dimacsAPolinomios f = do
  s0 <- readFile f
  return $ aux1 $ (foldr (\x acc -> (aux2 ((clausulaAPolinomio . words) x) acc))
             (S.empty,S.empty)) $ lines $ s0
     where aux1 (a,b) = (a,S.toList b)
           aux2 (a,b) (acc,vs) = (S.insert  a acc, S.union vs b)
\end{code}

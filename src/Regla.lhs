 La implementación en Haskell de dicha regla se hará en el módulo \texttt{Regla}

\begin{code}
module Regla where

import F2
import Logica
import Derivada
import Haskell4Maths ( var
                     , vars)
import Transformaciones ( phi
                        , theta
                        , proyeccion)

import Data.List (union)
import Test.QuickCheck
\end{code}

 La función \texttt{(reglaIndependencia x a1 a2)} es el polinomio obtenido de
 aplicar la regla de Independencia a los polinomios $a1$ y $a2$, respecto de la
 variable $x$.

\begin{code}
-- | Por ejemplo,
-- >>> [x1,x2,x3,x4] = (map var ["x1","x2","x3","x4"]) :: [PolF2]
-- >>> reglaIndependencia x1 1 1
-- 1
-- >>> reglaIndependencia x1 1 0
-- 0
-- >>> reglaIndependencia x1 x1 x1
-- 1
-- >>> reglaIndependencia x1 x1 x1*x2
-- x2
-- >>> reglaIndependencia x1 (x1*x3) (x1*x2)
-- x2x3
-- >>> reglaIndependencia x1 (1+x1*x3) (x1*x2)
-- x2x3+x2

reglaIndependencia :: PolF2 -> PolF2 -> PolF2 -> PolF2
reglaIndependencia x a1 a2 = aux + a1a2 + aux2
  where da1       = derivaPol a1 x
        da2       = derivaPol a2 x
        a1a2      = phi $ a1*a2
        a1da2     = phi $ a1*da2
        a2da1     = phi $ a2*da1
        da1da2    = phi $ da1*da2
        aux       = phi $ a1da2 + a2da1 + da1da2
        aux2      = phi $ a1a2*aux
\end{code}

 Recordar que la función \texttt{(phi p)} ó $\Phi (p)$ escogía el representante de
 menor grado del polinomio $p + \mathbb{I}_2$. Además, destacar que se aplica
 la función \texttt{phi} a cada multiplicación de forma aislada ya que es más
 eficiente que realizar las operaciones necesarias y finalmente
 aplicarla.\\

 Como caso particular, si los polinomios $a_i = b_i + x_p \cdot c_i$, con
 $deg_{x_p} (b_i) = deg_{x_p} (c_i) = 0$ para $i=1,2$, la regla se puede
 reescribir de la siguiente forma:
 $$ \partial_{x_p}(a_1,a_2) = \Phi [1+(1+b_1 \cdot b_2) \cdot
 [1+(b_1+c_1)(b_2+c_2)]]$$ 

 \noindent Por ejemplo, para hallar $a$ tal que:
 $$a= \partial_{x_2}(1+x_2x_3x_5+x_3x_5, 1 + x_1x_2x_3x_4x_5+x_1x_2x_3x_5)$$

 basta con saber que
 \begin{itemize}
 \item $b_1 = 1+x_3x_5$
 \item $c_1 = x_3x_5$
 \item $b_2 = 1$
 \item $c_2 = (1+x_4) x_1x_3x_5$
 \end{itemize}

 \noindent luego el resultado es $a = 1 + x_1x_3x_4x_5 + x_1x_3x_5$. Si se
 comprueba el resultado en Haskell se verá que coinciden:

\begin{code}
-- |
-- >>> [x1,x2,x3,x4,x5] = (map var ["x1","x2","x3","x4","x5"])::[PolF2]
-- >>> reglaIndependencia x2 (1+x2*x3*x5+x3*x5)                                                                   (1+x1*x2*x3*x4*x5+x1*x2*x3*x5)
-- x1x3x4x5+x1x3x5+1
\end{code}

 Notar que la regla de independencia es simétrica. Se comprobará aplicando
 \texttt{quickCheck} a la siguiente propiedad:

\begin{code}
-- |
-- >>> quickCheck prop_reglaIndep_simetrica
-- +++ OK, passed 100 tests.

prop_reglaIndep_simetrica :: PolF2 -> PolF2 -> Int -> Bool
prop_reglaIndep_simetrica a1 a2 n = reglaIndependencia x a1' a2' ==
                                    reglaIndependencia x a2' a1'
  where a1' = phi a1
        a2' = phi a2
        xs  = union (vars a1') (vars a2')
        xss = if (null xs) then [((var "x") :: PolF2)]
                           else xs
        x   = xss !! (n `mod` (length xss))
\end{code}

Para fórmulas, la regla de independencia se define como:
$$\partial_p (F_1,F_2) := \Theta (\partial_{x_p} (\pi (F_1), \pi (F_2))) $$

Mientras que su implementación es:

\begin{code}
reglaIndForm :: VarProp -> FProp -> FProp -> FProp
reglaIndForm p f1 f2 = theta $ reglaIndependencia x p1 p2
  where x  = proyeccion (Atom p)
        p1 = proyeccion f1
        p2 = proyeccion f2
\end{code}

Siguiendo con el ejemplo anterior,

\begin{table}[h]
\centering
\begin{tabular}{lll}
 & $\partial_{p_2}(p_3 \wedge p_5 \rightarrow p_2 \, , \, p_1 \wedge p_2 \wedge
 p_3 \wedge p_5 \rightarrow p_4)$ & $=$ \\\\
 $=$ & $\Theta (\partial_{x_2}(1+x_2x_3x_5+x_3x_5, 1 +
 x_1x_2x_3x_4x_5+x_1x_2x_3x_5))$ & $=$ \\\\
 $=$ & $\Theta (1 + x_1x_3x_4x_5 + x_1x_3x_5) = \neg (p_1 \wedge p_3 \wedge p_4
 \wedge p_5 \leftrightarrow p_1 \wedge p_3 \wedge p_5) $ & $=$ \\\\
 $=$ & $p_1 \wedge p_3 \wedge p_5 \rightarrow p_4$
\end{tabular}
\end{table}

 Mientras que en Haskell:

\begin{code}
-- |
-- >>> [p1,p2,p3,p4,p5] = map Atom ["p1","p2","p3","p4","p5"]
-- >>> f1 = p3 ∧ p5 → p2
-- >>> f2 = p1 ∧ p2 ∧ p3 ∧ p5 → p4
-- >>> g = p1 ∧ p3 ∧ p5 → p4
-- >>> reglaIndForm "p2" f1 f2
-- ¬((p1 ∧ (p3 ∧ (p4 ∧ p5))) ↔ ¬((p1 ∧ (p3 ∧ p5)) ↔ ⊤))
-- >>> equivalentes g (reglaIndForm "p2" f1 f2)
-- True
\end{code}

 Es importante destacar las siguientes características sobre la regla
 $\partial_p$:

 \begin{itemize}
 \item[•] Si $\partial_p (F,G)$ es una tautología, entonces $\partial_p (F,G) =
 \top$.
 \item[•] Si $\partial_p (F,G)$ es inconsistente, entonces $\partial_p (F,G) =
 \bot$.
 \end{itemize}

 Ambas características son consecuencia de la transformación a polinomios, y es
 que las fórmulas polinomiales que corresponden a tautologías o inconsistencias
 son algebraicamente simplificadas a 1 ó 0 en $\mathbb{F}_2 [\textbf{x}] /
 \mathbb{I}_2$, respectivamente. De hecho, se trabaja con las proyecciones
 polinomiales para explotar dicha propiedad. Por ejemplo,

\begin{code}
-- |
-- >>> proyeccion $ p1 ∨ (no p1)
-- 1
-- >>> proyeccion $ p1 ∧ (no p1)
-- 0
\end{code}

\vspace{0.5cm}
A continuación, se expondrán diversos resultados sobre la regla de independencia, que justificarán usar la misma como herramienta para probar teoremas.

\prop Sea $p$ una variable proposicional, entonces $\partial_p$ es robusto.

 \noindent \textbf{Prueba:} Hay que probar que $F_1 \wedge F_2 \vDash \partial_p (F_1,F_2)$. Para ello, se supone que:
 $$\pi (F_1) = b_1 + x_p \cdot c_1 \;\;  , \;\; \pi (F_2) = b_2 + x_p \cdot c_2$$
 De acuerdo al teorema \ref{thm:123}, basta probar que
 $$\mathcal{V} (1+\pi (F_1) \cdot \pi (F_2)) \subseteq \mathcal{V} (1+ \partial_{x_p} (\pi (F_1) , \pi (F_2)))$$
 Sea $\textbf{u} \in \mathcal{V} (1+\pi (F) \cdot \pi (G)) \subseteq \mathbb{F}^n_2$, es decir,
 \begin{equation} \label{eq}
 (b_1+x_pc_1)(b_2+x_pc_2)|_{x=u} = 1
 \end{equation}

Ahora se pueden distinguir dos casos:
\begin{itemize}
\item[•] La coordenada $p$-ésima de \textbf{u} es 0, entonces por \ref{eq} se tiene que 
$$b_1 |_{x=u}=b_2 |_{x=u} = 1$$
Y por lo tanto, $1+b_1b_2 |_{x=u} = 0$
\item[•] La coordenada $p$-ésima de \textbf{u} es 1. En este caso, $(b_1+c_1)(b_2+c_2) |_{x=u} = 1$
\end{itemize}

Examinando la definición de $\partial_p$ se concluye que en ambos casos
$$\partial_{x_p}(\pi (F_1) , \pi (F_2))|_{x=u} =1$$
así que $\textbf{u} \in \mathcal{V} (1+\partial_{x_p} (\pi (F_1) , \pi (F_2)))$ . \hspace{8.5cm} $\square$ \\

El siguiente resultado es,

\thm \label{thm:opOmision} $\partial_p$ es un operador de omisión.

\noindent \textbf{Prueba:} El objetivo es probar que
$$[\{ F_1 , F_2 \} , \mathcal{L} \setminus \{ p \}] \equiv \partial_p (F_1 , F_2)$$

Se supone que $F_1,F_2 \in Form(\mathcal{L})$ y que $\pi (F_i) = b_i + x_pc_i$ con $i=1,2$, y donde $b_i$ y $c_i$ son polinomios sin la variable $x_p$. Recordar que en este caso la expresión de la regla es:

$$ \partial_{x_p}(\pi (F_1), \pi (F_2)) = \Phi [1+(1+b_1 \cdot b_2) \cdot
 [1+(b_1+c_1)(b_2+c_2)]]$$
 
Como se ha probado la robustez del operador $\partial_p$ en la proposición anterior, por el corolario \ref{cor:robusto} es suficiente probar que cualquier valoración $v$ sobre $\mathcal{L} \setminus \{ p \}$ que sea modelo de $\partial_p (F_1 , F_2)$ se puede extender a $\hat{v} \vDash \{ F_1,F_2 \} $ .\\

Sea $v \vDash \partial_p (F_1, F_2)$. Se considerará el punto de $\mathbb{F}^n_2$ asociado a   $v$, $o_v$. Se sigue que,

\begin{table}[h]
\centering
\begin{tabular}{rll}
 $o_v \in $ & $\mathcal{V} (1+\pi (\partial_p (F_1, F_2)))$ & $=$ \\\\
 $=$ & $\mathcal{V} (1+(\partial_{x_p} (\pi (F_1), \pi (F_2))))$ & $=$ \\\\
 $=$ & $\mathcal{V} ((1+b_1 \cdot b_2)[1+(b_1+c_1)(b_2+c_2)])$
\end{tabular}
\end{table}

luego
$$((1+b_1 \cdot b_2)[1+(b_1+c_1)(b_2+c_2)]) |_{x=o_v} = 0$$

Con el objetivo de construir la extensión requerida $\hat{v}$, se distinguen dos casos:

\begin{itemize}
\item[•] Si $(1+b_1\cdot b_2) |_{x=o_v} = 0$, entonces $$\hat{v} = v \cup \{ (x_p,0) \} \vDash F_1 \wedge F_2 $$
\item[•] Si $[1+(b_1+c_1)(b_2+c_2)]|_{x=o_v} = 0$, entonces $$\hat{v} = v \cup \{ (x_p,1) \} \vDash F_1 \wedge F_2 $$
\end{itemize}
\hspace{15.5cm} $\square$ \\

Abusando de notación, se usará el mismo símbolo $\vdash_{\partial}$ tanto para denotar lo definido en \ref{def:prueba} como para la noción equivalente que en lugar de ser para fórmulas es para polinomios. De esta forma, se pueden describir $\vdash_{\partial}$-pruebas sobre polinomios. Por ejemplo, una $\partial$-refutación para el conjunto $\pi [\{ p \rightarrow q , q \vee r \rightarrow s, \neg (p \rightarrow s) \}]$ es:

\begin{table}[h]
\centering
\begin{tabular}{llr}
 $1.$ & $1+x_1+x_1x_2$ & $\llbracket \pi (p \rightarrow q) \rrbracket$ \\
 $2.$ & $1+ (x_2+x_3+x_2x_3)(1+x_4)$ & $\llbracket \pi (q \vee r \rightarrow s) \rrbracket$ \\
 $3.$ & $x_1(1+x_4)$ & $\llbracket \pi (\neg (p \rightarrow s)) \rrbracket$ \\
 $4.$ & $1+x_1+x_3+x_1x_4+x_3x_4+x_1x_3+x_1x_3x_4$ & $\llbracket \partial_{x_2}((1.)(2.)) \rrbracket$ \\
 $5.$ & $0$ & $\llbracket \partial_{x_1}((3.)(4.)) \rrbracket$ \\
\end{tabular}
\end{table}

 El mismo ejemplo en Haskell, salvando que se cambiarán las variables
 proposicionales $p,q,r,s$ por $p_1,p_2,p_3,p_4$:

\begin{code}
-- |
-- >>> [p1,p2,p3,p4] = map Atom ["p1","p2","p3","p4"]
-- >>> [f1,f2,f3] = [p1 → p2, p2 ∨ p3 → p4, no (p1 → p4)]
-- >>> proyeccion f1
-- x1x2+x1+1
-- >>> proyeccion f2
-- x2x3x4+x2x3+x2x4+x2+x3x4+x3+1
-- >>> proyeccion f3
-- x1x4+x1
-- >>> x1 = proyeccion p1
-- >>> x2 = proyeccion p2
-- >>> reglaIndependencia x2 (proyeccion f1) (proyeccion f2)
-- x1x3x4+x1x3+x1x4+x1+x3x4+x3+1
-- >>> reglaIndependencia x1 (proyeccion f3)                                                          (reglaIndependencia x2 (proyeccion f1) (proyeccion f2))
-- 0
\end{code}

 Del teorema anterior se deduce que:

 \cor \cite{Borrego2009} $K$ es inconsistente si y sólo si $K \vdash_{\partial}
 \bot$.

 \noindent \textbf{Prueba:} Es consecuencia directa de los teoremas
 \ref{teo:completo} y  \ref{thm:opOmision}. \hspace{4cm} $\square$
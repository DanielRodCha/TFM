\subsection{Transformaciones entre fórmulas y polinomios}

 La traducción o transformación de la lógica proposicional en álgebra
 polinomial viene dada por \cite{Kapur-1985} y se ilustra en la figura
 \ref{fig:esquema}. \\

 La idea principal es que las fórmulas se pueden ver como polinomios sobre
 fórmulas atómicas cuando éstas están expresadas en términos de las conectivas
 booleanas \textit{o exclusivo} e \textit{y}; así como de las constantes 1 y 0,
 que equivalen a los conceptos de \textit{Verdad} y \textit{Falsedad},
 respectivamente. Las operaciones básicas de suma y multiplicación se
 corresponden con las conectivas booleanas \textit{o exclusivo} e \textit{y},
 respectivamente.\\

 Por tanto, el mapeo $P: Form (\mathcal{L} \rightarrow \mathbb{F}_2[x])$ que
 aparece en la página  \pageref{fig:esquema} se define por:

\begin{itemize}
\item[•] $P(\perp)=0$, $P(p_i)=x_i$, $P(\neg F)=1+P(F)$
\item[•] $P(F_1 \wedge F_2) = P(F_1) \cdot P(F_2)$
\item[•] $P(F_1 \vee F_2) = P(F_1) + P(F_2) + P(F_1) \cdot P(F_2)$
\item[•] $P(F_1 \rightarrow F_2) = 1 + P(F_1) + P(F_1) \cdot P(F_2)$
\item[•] $P(F_1 \leftrightarrow F_2) = 1 + P(F_1) + P(F_2)$
\end{itemize}

 En resumen, consiste en hacer corresponder las fórmulas falsas con el valor
 cero y las verdaderas con el uno. Por ejemplo, si una fórmula ($p_1 \wedge
 p_2$) dada una valoración ($p_1=True$, $p_2=True$) es verdadera, su
 correspondiente polinomio ($x_1 * x_2$) teniendo en cuenta la interpretación
 ($x_1=1$, $x_2=1$) debe valer uno ($1 + 1 =_{\mathbb{F}_2} 1$).

 La implementación se hará en el módulo \texttt{Transformaciones}:

\begin{code}
module Transformaciones where

import Logica
import Haskell4Maths (Vect(..)
                     , var
                     , vars
                     , mindices
                     , eval
                     , linear
                     , (%%))
import F2 (PolF2)

import Test.QuickCheck
\end{code}

 La función encargada de hacer dicha traducción es la función \texttt{tr}., que
 equivale al mapeo $P$ descrito anteriormente. Ésta recibe una fórmula
 proposicional del tipo \texttt{FProp} y devuelve un polinomio con coeficientes
 en $\mathbb{F}_2$, es decir, del tipo \texttt{PolF2}.

\begin{code}
-- | Por ejemplo,
--
-- >>> let [p1,p2] = [Atom "p1",Atom "p2"]
-- >>> tr p1
-- x1
-- >>> tr (p1 ∧ p2)
-- x1x2
-- >>> tr (p ∧ (q ∨ r))
-- qrx+qx+rx
tr :: FProp -> PolF2
tr T               = 1
tr F               = 0
tr (Atom ('p':xs)) = var ('x':xs)
tr (Atom xs)       = var xs
tr (Neg a)         = 1 + tr a
tr (Conj a b)      = tr a * tr b
tr (Disj a b)      = a' + b' + a' * b'
                    where a' = tr a
                          b' = tr b
tr (Impl a b)      = 1 + a' + a' * tr b
                    where a' = tr a
tr (Equi a b)      = 1 + tr a + tr b
\end{code}

 Para la transformación contraria (de polinomios a fórmulas) se usará la función
 $\Theta :\mathbb{F}_2[x] \rightarrow Form(\mathcal{L})$ definida por:

\begin{itemize}
\item[•] $\Theta (0) = \perp$
\item[•] $\Theta (1) = \top$
\item[•] $\Theta (x_i) = p_i$
\item[•] $\Theta (a+b) = \neg(\Theta(a) \leftrightarrow \Theta(b))$
\item[•] $\Theta (a \cdot b) = \Theta(a) \wedge \Theta(b)$
\end{itemize}

 La función (\texttt{theta p}) transforma el polinomio \texttt{p} en la
 fórmula proposicional que le corresponde según la definición anterior.

\begin{code}
-- | Por ejemplo,
--
-- >>> let [x1,x2] = [var "x1", var "x2"] :: [PolF2]
-- >>> theta 0
-- ⊥
-- >>> theta (x1*x2)
-- (p1 ∧ p2)
-- >>> theta (x1 + x2 +1)
-- ¬(p1 ↔ ¬(p2 ↔ ⊤))

theta :: PolF2 -> FProp
theta 0          = F
theta 1          = T
theta (V [m])    = (theta' . mindices . fst) m
theta (V (x:xs)) = no (((theta' . mindices . fst) x) ↔ (theta (V xs)))

theta' :: [(String, t)] -> FProp
theta' []               = T
theta' [(('x':v),i)]    = Atom ('p':v) 
theta' ((('x':v),i):vs) = Conj (Atom ('p':v)) (theta' vs)
theta' [(v,i)]          = Atom v 
theta' ((v,i):vs)       = Conj (Atom v) (theta' vs)
\end{code}

 A continuación se definen dos propiedades que deben cumplir las funciones
 \texttt{tr} y \texttt{theta}.

 \prop Sea $f$ una fórmula proposicional cualquiera, $\Theta (P(f))$ es
 equivalente a $f$. La implementación de esta propiedad es:

\begin{code}
-- |
-- >>> quickCheckWith (stdArgs {maxSize = 50}) prop_theta_tr
-- +++ OK, passed 100 tests.
prop_theta_tr :: FProp -> Bool
prop_theta_tr f = equivalentes (theta (tr f)) f
\end{code}

 Notar que a la hora de chequear la propiedad anterior se ha acotado el tamaño
 máximo de las fórmulas proposicionales ya que en caso contrario se demora
 demasiado en ejecutarse.\\

 Se define ahora la propiedad inversa:
  
 \prop Sea $p$ un polinomio de $\mathbb{F}_2[x]$, $P (\Theta(p)) = p$. Cuya
 implementación es:

\begin{code}
prop_tr_theta :: PolF2 -> Bool
prop_tr_theta p = tr (theta p) == p
\end{code}

 Sin embargo, al ejecutarlo nos devuelve \texttt{Failed}:

\begin{code}
-- >>> quickCheck prop_tr_theta
--  *** Failed! Falsifiable (after 1 test):
--  x29^3x87^5+x30x74^2x80^4+x38^5x62^2
\end{code}

 Esto se debe a los exponentes, que se pierden al transformar el polinomio en
 una fórmula proposicional. Por tanto, al reescribir el polinomio, éste es
 idéntico pero sin exponentes. Se tratará esto en la siguiente subsección y se
 comprobará que realmente ambos polinomios son iguales al estar en
 $\mathbb{F}_2[x]$.

\subsection{Correspondencia entre valoraciones y puntos en $\mathbb{F}_2^n$}

 El comportamiento similar como funciones de la fórmula $F$ y su traducción
 polinomial $P(F)$ son la base entre la semántica y las funciones
 polinomiales. Con idea de esclarecer qué se quiere decir con esto se explicará
 qué quiere decir \textit{un comportamiento similar}:

 \begin{itemize}
 \item[•] \textit{De valoraciones a puntos}: Dada una valoración o
 interpretación $v: \mathcal{L} \rightarrow \{0,1\}$ el valor de verdad de $F$
 respecto de $v$ coincide con el valor de $P(F)$ en el punto $o_v \in
 \mathbb{F}^n$ definido por los valores dados por $v$; $(o_v)_i = v(p_i)$. Es
 decir, para cada fórmula $F \in Form(\mathcal{L})$,
 $$v(F)=P(F)((o_v)_1,\dots , (o_v)_n)$$

 \item[•] \textit{De puntos a valoraciones}: Cada $o=(o_1 \dots o_n)\in
 \mathbb{F}_2^n$ define una valoración $v_o$ de la siguiente forma:
 $$v_o(p_i)=1 \text{ si y sólo si } o_i=1$$
 Entonces,
 $$v_o \vDash F \;\; \Leftrightarrow \;\; P(F)(o_v)+1=0 \;\; \Leftrightarrow
 o_v\in \mathcal{V}(1+P(F))$$
 donde $V(.)$ se define como: Dado $a(\textbf{x}) \in \mathbb{F}_2[x]$,
 $$V(a(\textbf{x})) = \{o\in  \mathbb{F}_2^n : a(o) = 0 \}$$
 \end{itemize}

 Por consiguiente, hay dos mapeos entre el conjunto de interpretaciones o
 valoraciones y los pontos de $\mathbb{F}_2^n$, que definen biyecciones entre
 modelos de $F$ y puntos de la variedad algebraica $\mathcal{V}(1+P(F))$;

\begin{table}[h]
\centering
\begin{tabular}{cc}
$Mod(F) \rightarrow \mathcal{V}(1+P(F))$ & $\mathcal{V}(1+P(F)) \rightarrow
 Mod(F)$ \\
 $v \rightarrow o_v$ & $o \rightarrow v_o$
\end{tabular}
\end{table}

 Por ejemplo, sea la fórmula $F=p_1\rightarrow p_2 \wedge p_3$. El polinomio
 asociado es $P(F)=1+x_1+x_1x_2x_3$ . La valoración $v=\{(p_1,0), (p_2,1),
 (p_3,0)\}$ es modelo de $F$ e induce el punto $o_v = (0,1,0) \in
 \mathbb{F}_2^3$ que a su vez pertenece a
 $\mathcal{V}(1+P(F))=\mathcal{V}(x_1+x_1x_2x_3)$.

\begin{code}
-- |
-- >>> let [p1,p2,p3] = map Atom ["p1","p2","p3"]
-- >>> let f = p1 → p2 ∧ p3
-- >>> tr f
-- x1x2x3+x1+1
-- >>> esModeloFormula [p3] f
-- True
-- >>> eval (1+(tr f)) [(var "x1",0),(var "x2",1),(var "x3",0)]
-- 0
\end{code}

\subsection{Proyección polinomial}
 Consideremos ahora la parte derecha de la figura \ref{fig:esquema}. Para
 simplificar la relación entre la semántica de la lógica proposicional y la
 geometría sobre cuerpos finitos se usará el mapa:

 $$\Phi:\mathbb{F}_2[\textbf{x}] \rightarrow \mathbb{F}_2[\textbf{x}]$$
 $$\Phi (\sum\limits_{\alpha \in I} \textbf{x}^{\alpha} ) := \sum\limits_{\alpha
 \in I} \textbf{ x}^{sg(\alpha)} $$

 siendo $sg(\alpha) := (\delta_1 ,\dots,\delta_n)$ donde $\delta_i$ es 0 si
 $\alpha_i = 0$ y 1 en cualquier otro caso. \\

 En la librería \texttt{HaskellForMaths} ya existe una función que calcula el
 representante de un polinomio un el grupo cociente por un ideal. Esta es la
 función \texttt{(\%\%)}. Sin embargo, ya que la búsqueda de la eficiencia es una
 máxima en este trabajo, se aprovechará el hecho de que calcular dicho
 representante equivale a reeplazar cada ocurrencia de $x_i^k$ (con
 $k\in\mathbb{N}$) por $x_i$.\\ 

 La función \texttt{(phi p)} calcula el representante de menor grado del
 polinomio $p$ en el grupo cociente $\mathbb{F}_2[\textbf{x}]/_{\mathbb{I}_2}$,
 siendo $\mathbb{I}_2 = \{x_1+x_1^2,...,x_n+x_n^2\}$ y $n\in \mathbb{N}$ el
 número total de variables. 

\begin{code}
-- | Por ejemplo,
-- >>> let [x1,x2] = [var "x1", var "x2"] :: [PolF2]
-- >>> phi (1+x1+x1^2*x2) 
-- x1x2+x1+1
phi :: PolF2  -> PolF2
phi = linear (\m -> product [ var x | (x,i) <- mindices m])
\end{code}

 Para poder comprobar la propiedad clave que justifica la redefinición de phi,
 es necesaria la función (\texttt{ideal p}) que devuelve el ideal (con menos
 generadores) respecto al cual se calcula el grupo cociente para buscar el
 representante.

\begin{code}
-- | Por ejemplo,
--
-- >>> let [x1,x2] = [var "x1", var "x2"] :: [PolF2]
-- >>> ideal (1+x1+x1^2*x2)
-- [x1^2+x1,x2^2+x2]
ideal :: PolF2 -> [PolF2]
ideal p = [v+v^2| v<-vars p]
\end{code}

 La propiedad implementada queda:

\begin{code}
-- |
-- >>> quickCheck prop_phi
-- +++ OK, passed 100 tests.
prop_phi :: PolF2 -> Bool
prop_phi p = phi p == p %% (ideal p)
\end{code}

 Tal y como se ha descrito anteriormente, $\Phi$ selecciona un representante de
 la clase de equivalencia de $\mathbb{F}_2[\textbf{x}]/_{\mathbb{I}_2}$. Dicho
 representante resulta ser también un polinomio, por lo que cuando se quiere
 asociar un polinomio a una fórmula proposicional basta aplicar la composición
 $\pi := \Phi \circ P$, que se llamará \textit{proyección polinomial}.\\

 Esta proyección es muy útil para manejar los polinomios ya que los simplifica
 en gran medida. Por ejemplo, sea $F=p_1\rightarrow p_1 \wedge p_2$, entonces
 $P(F)=1+x_1+x_1^2x_2$ mientras que $\pi(F)=1+x_1+x_1x_2$. \\

 La función \texttt{proyeccion p} es la implementación de la función $\pi (p)$:

\begin{code}
-- | Por ejemplo,
-- >>> let [p1,p2] = [Atom "p1",Atom "p2"]
-- >>> proyeccion p1
-- x1
-- >>> tr (p1 → p1 ∧ p2)
-- x1^2x2+x1+1
-- >>> proyeccion (p1 → p1 ∧ p2)
-- x1x2+x1+1
proyeccion :: FProp -> PolF2
proyeccion = (phi . tr)
\end{code}

 Conveniene comprobar si se verifica que cualquier fórmula $f$ es
 equivalente a $\theta (\pi (f))$:

\begin{code}
-- |
-- >>> quickCheckWith (stdArgs {maxSize = 50}) prop_theta_proyeccion
-- +++ OK, passed 100 tests.
prop_theta_proyeccion :: FProp -> Bool
prop_theta_proyeccion f = equivalentes (theta (proyeccion f)) f
\end{code}

 Además, como se ha solucionado el problema de los exponentes se puede
 comprobar la propiedad recíproca:

\begin{code}
-- |
-- >>> quickCheck prop_proyeccion_theta
-- +++ OK, passed 100 tests.
prop_proyeccion_theta :: PolF2 -> Bool
prop_proyeccion_theta p = phi p == (proyeccion . theta) p
\end{code}

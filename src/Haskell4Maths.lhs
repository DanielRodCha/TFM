\section{El anillo $\mathbb{F}_2[\textbf{x}]$}

 Para una natural interpretación algebraica de la lógica, el marco de trabajo
 escogido es el anillo $\mathbb{F}_2[\textbf{x}]$. Con la idea de facilitar la
 identificación entre variables proposicionales e incógnitas, se fija la
 notación de forma que a una variable proposicional $p_i$ (ó $p$) le
 corresponde la incógnita $x_i$ (ó $x_p$).\\

 La notación usada en los polinomios es la estándar. Dado $\alpha = (\alpha_1,
 ... , \alpha_n) \in \mathbb{N}^n$, se define $|\alpha| := \text{máx} \{
 \alpha_1,...,\alpha_n \}$ y $x^{\alpha}$ es el monomio
 $x^{\alpha_1}_1...x_n^{\alpha_n}$. \\

 \defn El \textit{grado} de $a(\textbf{x}) \in \mathbb{F}_2[\textbf{x}]$ es
 $$deg_{\infty}(a(\textbf{x})) := \text{máx}\{|\alpha| : \textbf{x}^{\alpha}
 \text{ es un monomio de } a\}$$

 Si $deg(a(x)) \leq 1$, el polinomio $a(\textbf{x})$ se denomina
 \textit{fórmula polinomial}. El grado de $a(x)$ respecto una variable $x_i$ se
 denota por $deg_i (a(\textbf{x}))$.\\

 A continuación se tratará de implementar $\mathbb{F}_2[\textbf{x}]$ en
 Haskell, así como algunas operaciones polinomiales que serán necesarias más
 adelante.

\subsection{Polinomios en Haskell}

 Si se quiere trabajar con polinomios en Haskell, no es necesario ``hacer tabla
 rasa'' y tratar de implementarlo todo desde el principio. Parafraseando a
 Newton,

\begin{center}
\textit{Si he conseguido ver más lejos es porque me he aupado en hombros de
 gigantes}\\
\hspace{10.5cm} Isaac Newton
\end{center}

 \noindent así que conviene apoyarse en la multitud de librerías existentes de
la 
 comunidad Haskell. Aunque, continuando con la metáfora de Newton, no es fácil
 saber qué gigante es el más alto si miramos desde el suelo. Por tanto, es
 necesario un estudio de las distintas librerías, a fin de escoger la que se
 adecúe en mayor medida a las necesidades de este proyecto.\\

 Seguidamente se comentarán los detalles más relevantes de las distintas
 librerías estudiadas, centrando la atención en los detalles prácticos como la 
 empleabilidad y la eficiencia.

 \subsubsection{Cryptol}
 Cryptol es un lenguaje de programación especialmente desarrollado para
 implementar algoritmos criptográficos. Su ventaja es su similitud con el
 lenguaje matemático respecto a un lenguaje de propósito general. Está escrito
 en Haskell, siendo un trabajo muy pulido con un tutarial muy completo.\\

 Sin embargo, no resulta intuitivo aislar la librería de polinomios por lo que
 para realizar las pruebas se ha optado por cargar todo el paquete apoyándonos en
 la documentación.\\

 Esta librería sólo trabaja con polinomios en una única variable. Por
 ejemplo, los polinomios de $\mathbb{F}_2[\textbf{x}]$ con grado
 menor o igual que 7 se codifican mediante un vector de unos y ceros donde se
 almacenan los coeficientes de cada $x^i$ con $i\leq 7$. Debido a este tipo de
 codificación no es trivial extenderlo a más de una variable.

 \subsubsection{The polynomial package}
 El módulo \texttt{MAth.Polynomial} de esta librería implementa la aritmética
 en una única variable, debiendo especificar con qué orden monomial se quiere
 trabajar. Por el contrario, no es necesario dar como entrada el cuerpo en el
 que se defina la $K$-álgebra sino que construye los polinomios directamente de
 una lista ordenada de coeficientes. Por tanto, hereda el tipo de dichos
 elementos de la lista (\texttt{[a]}), formando lo que se denomina como tipo
 polinomio (\texttt{Poly a}).\\

 La librería se centra en definir distintos tipos de polinomios de la
 literatura matemática clásica como los polinomios de Hermite, de Bernouilli,
 las bases de Newton o las bases de Lagrange. Finalmente, destacar que la
 documentación no es escasa por lo que su uso resulta tedioso.

 \subsubsection{ToySolver.Data.Polynomial}
 Este módulo se enmarca en una librería que trata de implementar distintos
 procedimientos y algoritmos para resolver varios problemas de decisión. Debido
 a que su función es únicamente servir como auxiliar para otros módulos el
 código no está comentado, lo que dificulta su uso.\\

 La implementación es muy completa, incluye multitud de operaciones y
 procedimientos de polinomios y $\mathcal{K}$-álgebras. Por ejemplo, permite
 construir polinomios sobre cuerpos finitos. Sin embargo, la estructura de dato
 de los polinomios no es intuitiva para su uso.

 \subsubsection{SBV}
 El parecido a la librería de Cryptol es notable, por lo que se encuentra con
 inconvenientes similares.

 \subsubsection{Gröebner bases in Haskell}
 El objetivo principal de esta librería es, tal y como su nobre indica,
 el cálculo de bases de Gröebner mediante operaciones con ideales.\\

 En lo que respecta al código, al tipo de dato polinomio se le debe especificar
 el Anillo de coeficientes así como el orden monomial. Además, se deben
 declarar desde el principio las variables que se quieren usar.\\

 La documentación está muy detallada aunque el autor comenta que se prioriza la
 claridad del código y el rigor matemático ante la efieciencia.

 \subsubsection{HaskellForMaths}

 El módulo de polinomios es \texttt{Math.CommutativeAlgebra.Polynomial}. Al
 igual que en la librería anterior, se permite escoger el orden monomial entre
 los tres más usuales (lexicográfico, graduado lexicográfico y graduado reverso
 lexicográfico) e incluso definir otros nuevos.\\

 También se debe dar como entrada el cuerpo sobre el que se trabajará. Para
 ello se incorpora un módulo especifico llamado \texttt{MAth.Core.Field} en el
 que están implementados los cuerpos más comunes, como los números racionales o
 los cuerpos finitos.\\

 Destacar que el tipo de dato polinomio tiene estructura vectorial, donde la
 base es cada monomio que exista (combinaciones de todas las variables) y el
 número en la posición $i$-ésima del vector corresponde con el coeficiente del
 monomio $i$-ésimo (según el orden especificado) del polinomio.\\

 Las operaciones básicas de los polinomios están ya implementadas de forma
 eficiente, destacando la multiplicación, desarrollada en un módulo aparte se
 apoya en otra librería de productos tensoriales.\\
 
 Esta librería responde en líneas generales a las necesidades del proyecto ya
 que es modular, el código está documentado y la mayoría de algoritmos son
 eficientes. Por dichas razones se escoge esta librería como auxiliar en el
 proyecto a desarrollar.\\

 \subsection{Introducción a HaskellForMaths}

 Se muestran a continuación diversos ejemplos de funciones de
 \texttt{Haskell4Maths} que aparecerán de forma recurrente en el resto del
 trabajo.

\begin{code}
module Haskell4Maths 
    ( F2
    , Vect(..)
    , linear
    , zerov
    , Lex
    , Glex
    , Grevlex
    , var
    , mindices
    , lm
    , lt
    , eval
    , (%%)
    , vars) where

import Math.Core.Field
import Math.Algebras.VectorSpace
import Math.CommutativeAlgebra.Polynomial
\end{code}

\subsubsection{Math.Core.Field}
 En este módulo se definen el cuerpo $\mathbb{Q}$ de los racionales  y los
 cuerpos finitos o de Galois: $\mathbb{F}_2$, $\mathbb{F}_3$, $\mathbb{F}_4$,
 $\mathbb{F}_5$, $\mathbb{F}_7$, $\mathbb{F}_8$, $\mathbb{F}_9$,
 $\mathbb{F}_{11}$, $\mathbb{F}_{13}$, $\mathbb{F}_{16}$, $\mathbb{F}_{17}$,
 $\mathbb{F}_{19}$, $\mathbb{F}_{23}$, $\mathbb{F}_{25}$.\\

 Veamos unos ejemplos de cómo se trabaja con los números racionales:

\begin{code}
-- |
-- >>> (7/14 :: Q)
-- 1/2
-- >>> (0.6 :: Q)
-- 3/5
-- >>> (2.3 + 1/5 * 4/7) :: Q
-- 169/70
\end{code}

 Para este trabajo, el cuerpo que nos interesa es $\mathbb{F}_2$, cuyos
 elementos pertenecen a la lista \texttt{f2}:

\begin{code}
-- |
-- >>> f2
-- [0,1]
\end{code}

 Y cuyas operaciones aritméticas se definen de forma natural:
\begin{code}
-- |
-- >>> (2 :: F2)
-- 0
-- >>> (1 :: F2) + (3 :: F2)
-- 0
-- >>> (7 :: F2) * (1 :: F2)
-- 1
\end{code}
 Además, cuenta con la función auxiliar \texttt{fromInteger} para transformar
 números de tipo \texttt{Integer} en el tipo \texttt{Fp} dónde \texttt{p} es
 número de elementos del cuerpo:
\begin{code}
-- |
-- >>> (fromInteger (12345 :: Integer)) :: F2
-- 1
\end{code}

\subsubsection{Math.Algebras.VectorSpace}
 En este módulo se define el tipo y las operaciones de los espacios de
 $k$-vectores libres sobre una base $b$, con $k$ un cuerpo, de la siguiente
 manera:
$$\texttt{newtype Vect k b = V [(b,k)]}$$

 Intuitivamente, un vector es una lista de pares donde la primera coordenada es
 un elemento de la base y la segunda coordenada el coeficiente de dicho
 elemento. Notar que el coeficiente pertenece al cuerpo $k$, que se debe
 especificar en el tipo.\\

 También destacar que este nuevo tipo tiene las instancias \texttt{Eq},
 \texttt{Ord} y \texttt{Show} además de estar definida la suma y la
 multiplicación de vectores (en función de la base y los coeficientes).\\

 La función \texttt{(zerov)} representa al vector cero independientemente del
 cuerpo $k$ y la base $b$. Por ejemplo,
\begin{code}
-- |
-- >>> zerov :: (Vect Q [a])
-- 0
-- >>> zerov :: (Vect F2 F3)
-- 0
\end{code}

 Una función que conviene destacar es la función \texttt{(linear f v)}, que es
 un mapeo lineal entre dos espacios vectoriales ($A = \texttt{Vect k a}$ y $B =
 \texttt{Vect k b}$). La función \texttt{f :: a -> Vect k b} va de los
 elementos de la base de $A$ a $B$. Por lo que \texttt{(linear)} es muy útil si
 se necesita transformar vectores de forma interna.

 \subsubsection{Math.ConmutativeAlgebra.Polynomial}

 En el siguiente módulo se define el álgebra conmutativa de los polinomios
 sobre el cuerpo $jk$. Los polinomios se representan como el espacio de
 $k$-vectores libres con los monomios como su base. \\

 Para poder trabajar con los polinomios es necesario especificar un orden
 monomial. En este módulo están implementados los tres más comunes: el
 lexicográfico (\texttt{Lex}), el graduado lexicográfico (\texttt{Glex}) y el
 graduado reverso lexicográfico (\texttt{Grevlex}). Asimismo, es posible añadir
 otros nuevos en caso de que fuera necesario.

 La función \texttt{(var v)} crea una variable en espacio vectorial de
 polinomios. Por ejemplo, si se quiere trabajar en $\mathbb{Q}[x,y,z]$,
 debemos definir:

\begin{code}
-- |
-- >>> [x,y,z] = map var ["x","y","z"] :: [GlexPoly Q String]
\end{code}

 Destacar que, en general, es necesario proporcionar los tipos de datos de
 forma que el compilador sepa qué cuerpo y qué orden monomial usar. A
 continuación se mostrarán diversos ejemplos de operaciones entre polinomios,
 variando el orden monomial y el cuerpo.

\begin{code}
-- |
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly Q String]
-- >>> x^2+x*y+x*z+x+y^2+y*z+y+z^2+z+1
-- x^2+xy+xz+x+y^2+yz+y+z^2+z+1
-- >>> [x,y,z] = map var ["x","y","z"] :: [GlexPoly Q String]
-- >>> x^2+x*y+x*z+x+y^2+y*z+y+z^2+z+1
-- x^2+xy+xz+y^2+yz+z^2+x+y+z+1
-- >>> [x,y,z] = map var ["x","y","z"] :: [GrevlexPoly Q String]
-- >>> x^2+x*y+x*z+x+y^2+y*z+y+z^2+z+1
-- x^2+xy+y^2+xz+yz+z^2+x+y+z+1
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly Q String]
-- >>> (x+y+z)^2
-- x^2+2xy+2xz+y^2+2yz+z^2
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly F2 String]
-- >>> (x+y+z)^2
-- x^2+y^2+z^2
\end{code}
 
 Como se mencionó anteriormente la base del espacio vectorial que es un
 polinomio, está formada por monomios. El tipo de dato monomio está formado por
 un coeficiente $i$ y una lista de pares. En el caso de los polinomios, un
 ejemplo de monomio es:

\begin{code}
-- |
-- >>> monomio
-- x^2y
monomio :: MonImpl [Char]
monomio = (M 1 [("x",2),("y",1)])
\end{code}
 
 Dichos pares se obtienen mediante la función \texttt{(mindices m)} y se pueden
 entender como los elementos canónicos que forman cada monomio de la base, así
 como su exponente:

\begin{code}
-- |
-- >>> mindices monomio
-- [("x",2),("y",1)]
\end{code}

 En este módulo también se implementan tres funciones auxiliares que resultarán
 de gran utilidad más adelante. La función auxiliar que resulta más natural
 implementar cuando se trabaja con polinomios y que además goza de una gran
 importancia es \texttt{(vars p)}. Ésta devuelve la lista de variables que
 aparecen en el polinomio $p$.

\begin{code}
-- |Por ejemplo,
--
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly F2 String]
-- >>> vars (x*z*y+y*x^2+z^4)
-- [x,y,z]
\end{code}

 La segunda función auxiliar es \texttt{(lt m)}
 (término líder) que devuelve un par \texttt{(m,i)} donde $m$ es el monomio
 líder e $i$ su coeficiente ($i\in k$). 

\begin{code}
-- |
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly F2 String]
-- >>> lt (x*z*y+y*x^2+z^4)
-- (x^2y,1)
\end{code}

 La tercera es la función \texttt{(lm p)} que devuelve el monomio líder del
 polinomio $p$: 

\begin{code}
-- |
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly F2 String]
-- >>> lm (x*z*y+y*x^2+z^4)
-- x^2y
\end{code}

 Otra función natural es \texttt{(eval p vs)}, que evalúa el polinomio
 \texttt{p} en el punto descrito por \texttt{vs}, siendo ésta una lista de
 pares variable-valor.

\begin{code}
-- |
-- >>> [x,y] = map var ["x","y"] :: [LexPoly F2 String]
-- >>> eval (x^2+y^2) [(x,1),(y,0)]
-- 1
\end{code}

 Por último, destacar las función \texttt{(p \%\% xs)} que calcula la reducción
 del polinomio $p$ respecto de los polinomios de la lista $xs$.

\begin{code}
-- |
-- >>> [x,y,z] = map var ["x","y","z"] :: [LexPoly F2 String]
-- >>> (x^2+y^2) %% [x^2+1]
-- y^2+1
\end{code}

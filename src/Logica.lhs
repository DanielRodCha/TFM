\section{Lógica proposicional}

En esta sección se introducirán brevemente los principales conceptos de la
lógica proposicional, además de fijar la notación que se usará durante todo el
trabajo. Para su implementación en Haskell se define el módulo \texttt{Lógica}:

\begin{code}
module Logica where 
\end{code}

 Para conseguir este objetivo se utilizarán las siguientes librerías
 auxiliares:

\begin{code}
import Control.Monad ( liftM
                     , liftM2)
import Data.List     ( union
                     , subsequences)
import Test.QuickCheck
import qualified Data.Set as S
\end{code}

Antes de describir el lenguaje de la lógica proposicional es importante recordar las
definiciones formales de alfabeto y lenguaje:

\defn Un \textit{alfabeto} es un conjunto finito de símbolos.

\defn Un \textit{lenguaje} es un conjunto de cadenas sobre un alfabeto.\\

Especificando, un lenguaje formal es un lenguaje cuyos símbolos primitivos y
 reglas para unir esos símbolos están formalmente especificados. Al conjunto
 de las reglas se le denomina gramática formal o sintaxis. A las cadenas de
 símbolos que siguen las idicaciones de la gramática se les conoce como
 fórmulas bien formadas o simplemente fórmulas. \\

 Para algunos lenguajes formales existe también una semántica formal que puede
 interpretar y dar significado a las fórmulas bien formadas del lenguaje. El
 lenguaje de la lógica proposicional es un caso particular de lenguaje formal
 con semántica.

\subsection{Alfabeto y sintaxis}
El alfabeto de la lógica proposicional está formado por tres tipos de
elementos: las variables proposicionales, las conectivas lógicas y los
símbolos auxiliares. \\

\defn  Las \textit{variables proposicionales} son un conjunto
 finito de símbolos proposicionales que, tal y como su propio nombre indica, 
 representan proposiciones. Dichas proposiciones son sentencias que pueden ser
 declaradas como verdaderas o falsas, es por esto que se dice que las variables
 proposicionales toman valores discretos (True o False). Es comúnmente aceptado
 (y así será en este trabajo) llamar al conjunto finito de las variables ($\mathcal{L} =
 \{p_1,...,p_n\}$) lenguaje proposicional. A la hora de implementar las
 variables proposicionales se representarán mediante cadenas:

\index{\texttt{VarProp}}
\begin{code}
type VarProp = String
\end{code}

 El conjunto de las fórmulas $Form(\mathcal{L})$ se construye usando las
 conectivas lógicas estándar:
\begin{itemize}
\item Monarias:

\begin{tabular}{ll}
$-$ Negación ($\neg$) & $-$ Constante \textit{true} ($\top$) \\
$-$ Constante \textit{false} ($\bot = \neg \top$) &
\end{tabular}

\item Binarias:

\begin{tabular}{ll}
$-$ Conjunción ($\wedge$) & $-$ Condicional o implicación ($\rightarrow$) \\
$-$ Disyunción ($\vee$) & $-$ Bicondicional ($\leftrightarrow$)
\end{tabular}
\end{itemize}

 Los símbolos auxiliares con los que se trabajará serán los paréntesis,
 que se utilizan para indicar precedencia y ya vienen implementados en
 Haskell. \\

\defn Una fórmula proposicional es una cadena sobre el alfabeto de la lógica
 proposicional descrito anteriormente (variables proposicionales, conectivas
 lógicas y símbolos auxiliares). Destacar que se construyen de forma recursiva,
 esto es, las variables se combinan mediante conectivas para formar fórmulas y
 éstas, a su vez, se combinan dando lugar a nuevas fórmulas.

 Con todo ello se define el tipo de dato de las fórmulas proposicionales
 (\texttt{FProp}) usando constructores de tipo, es decir, una fórmula es
 $\top$, $\bot$, una variable proposicional o una combinación mediante una
 conectiva de dos fórmulas. En Haskell:

\index{\texttt{FProp}}
\begin{code}
data FProp = T
           | F
           | Atom VarProp
           | Neg FProp 
           | Conj FProp FProp 
           | Disj FProp FProp 
           | Impl FProp FProp 
           | Equi FProp FProp 
  deriving (Eq,Ord)
\end{code}

 Por razones estéticas, además de facilitar el uso de este tipo de dato,
 se declara el procedimiento de escritura de las fórmulas:

\index{\texttt{FProp}}
\begin{code}
instance Show FProp where
    show (T)        = "⊤"
    show (F)        = "⊥"
    show (Atom x)   = x
    show (Neg x)    = "¬" ++ show x
    show (Conj x y) = "(" ++ show x ++ " ∧ " ++ show y ++ ")"
    show (Disj x y) = "(" ++ show x ++ " ∨ " ++ show y ++ ")"
    show (Impl x y) = "(" ++ show x ++ " → " ++ show y ++ ")"
    show (Equi x y) = "(" ++ show x ++ " ↔ " ++ show y ++ ")"
\end{code}

 Las fórmulas atómicas carecen de una estructura formal más profunda; es decir,
 son aquellas fórmulas que no contienen conectivas lógicas. En la lógica
 proposicional, las únicas fómulas atómicas que aparecen son las variables
 proposicionales. Por ejemplo: 

\begin{code}
p, q, r :: FProp
p  = Atom "p"
q  = Atom "q"
r  = Atom "r"
\end{code}

 Combinando las fórmulas atómicas mediante el uso de las conectivas lógicas
 anteriormente enumeradas obtenemos lo que se denomina como fórmulas
 compuestas. Aunque estén definidas en el propio tipo de dato, con el objetivo
 de facilitar su uso, implementaremos las conectivas lógicas como
 funciones entre fórmulas:\\

 \texttt{(no f)} es la negación de la fórmula $f$.

\index{\texttt{no}}
\begin{code}
no :: FProp -> FProp
no = Neg
\end{code}

\texttt{(f ∨ g)} es la disyunción de las fórmulas f y g.

\index{\texttt{∨}}
\begin{code}
(∨) :: FProp -> FProp -> FProp
(∨)   = Disj
infixr 5 ∨
\end{code}

\texttt{(f ∧ g)} es la conjunción de las fórmulas f y g.

\index{\texttt{∧}}
\begin{code}
(∧) :: FProp -> FProp -> FProp
(∧)   = Conj
infixr 4 ∧
\end{code}

\texttt{(f → g)} es la implicación de la fórmula f a la fórmula g.

\index{\texttt{→}}
\begin{code}
(→) :: FProp -> FProp -> FProp
(→)  = Impl
infixr 3 →
\end{code}

\texttt{(f ↔ g)} es la equivalencia entre las fórmulas f y g.

\index{\texttt{↔}}
\begin{code}
(↔) :: FProp -> FProp -> FProp
(↔) = Equi
infixr 2 ↔
\end{code}

 Durante el desarrollo del trabajo se definirán distintas propiedades sobre las
 fórmulas proposicionales. Es bien sabido que una ventaja que nos ofrece
 Haskell a la hora de trabajar es poder definir también dichas propiedades y
 comprobarlas. Sin embargo, como las fórmulas proposicionales se han definido
 por el usuario el sistema no es capaz de generarlas automáticamente. Es
 necesario declarar que \texttt{FProp} sea una instancia de \texttt{Arbitrary}
 y definir un generador de objetos del tipo \texttt{FProp} como sigue:

\index{\texttt{FProp}}
\begin{code}
instance Arbitrary FProp where
  arbitrary = sized prop
    where
      prop n  | n <= 0     = atom
              | otherwise  = oneof [ 
                    atom
                    , liftM Neg subform
                    , liftM2 Conj subform  subform
                    , liftM2 Disj subform  subform
                    , liftM2 Impl subform  subform
                    , liftM2 Equi subform' subform' ]
        where
          atom     = oneof [liftM Atom (elements ["p","q","r","s"]),
                            elements [F,T]]
          subform  = prop ( n `div` 2)
          subform' = prop ( n `div` 4)
\end{code}

 Dadas dos fórmulas $F,G$ y $p$ una variable proposicional, se denota por
 $F\{p/G\}$ a la fórmula obtenida al sustituir cada ocurrencia de $p$ en $F$
 por la fórmula $G$. \\

 Se implementa $f\{p/g\}$ mediante la función \texttt{(sustituye f p g)}, donde f es la
 fórmula original, p la variable proposicional a sustituir y g la fórmula
 proposicional por la que se sustituye. Al ser \texttt{FProp} un tipo recursivo
 se hará dicha definición usando patrones:

\index{\texttt{sustituye}}
\begin{code}
-- | Por ejemplo,
-- >>> sustituye (no p) "p" q
-- ¬q
-- >>> sustituye (no (q ∧ no p)) "p" (q ↔ p)
-- ¬(q ∧ ¬(q ↔ p))
sustituye :: FProp -> VarProp -> FProp -> FProp
sustituye T            _ _ = T
sustituye F            _ _ = F
sustituye (Atom f)     p g | f == p = g
                           | otherwise = Atom f
sustituye (Neg f)      p g = Neg (sustituye f p g)
sustituye (Conj f1 f2) p g = Conj (sustituye f1 p g) (sustituye f2 p g)
sustituye (Disj f1 f2) p g = Disj (sustituye f1 p g) (sustituye f2 p g)
sustituye (Impl f1 f2) p g = Impl (sustituye f1 p g) (sustituye f2 p g)
sustituye (Equi f1 f2) p g = Equi (sustituye f1 p g) (sustituye f2 p g)
\end{code}

\subsection{Semántica}
 \defn Una interpretación o valoración es una función $i: \mathcal{L}
 \rightarrow \{0,1\}$. \\

 En Haskell se representará como un conjunto de fórmulas atómicas. Las fórmulas
 que aparecen en dicho conjunto se suponen verdaderas, mientras que las
 restantes fórmulas atómicas se suponen falsas.

\index{\texttt{Interpretacion}}
\begin{code}
type Interpretacion = [FProp]
\end{code}

 El significado de la fórmula $f$ en la interpretación $i$ viene dado
 por la función de verdad en su sentido más clásico, tal y como se detalla en
 el código. \\

 \texttt{(significado f i)} es el significado de la fórmula f en la
 interpretación i:

\index{\texttt{significado}}
\begin{code}
-- | Por ejemplo, 
-- 
-- >>> significado ((p ∨ q) ∧ ((no q) ∨ r)) [r]
-- False
-- >>> significado ((p ∨ q) ∧ ((no q) ∨ r)) [p,r]
-- True
significado :: FProp -> Interpretacion -> Bool
significado T          _ = True
significado F          _ = False
significado (Atom f)   i = (Atom f) `elem` i
significado (Neg f)    i = not (significado f i)
significado (Conj f g) i = (significado f i) && (significado g i)
significado (Disj f g) i = (significado f i) || (significado g i)
significado (Impl f g) i = significado (Disj (Neg f) g) i
significado (Equi f g) i = significado (Conj (Impl f g) (Impl g f)) i
\end{code}

 Una interpretación $i$ es modelo de la fórmula $F\in Form(\mathcal{L})$ si hace
 verdadera la fórmula en el sentido clásico definido
 anteriormente. \texttt{(esModeloFormula i f)} se verifica si la interpretación
 $i$ es un modelo de la fórmula $f$.

\index{\texttt{esModeloFormula}}
\begin{code}
-- | Por ejemplo,
--
-- >>> esModeloFormula [r]   ((p ∨ q) ∧ ((no q) ∨ r))
-- False
-- >>> esModeloFormula [p,r] ((p ∨ q) ∧ ((no q) ∨ r))
-- True
esModeloFormula :: Interpretacion -> FProp -> Bool
esModeloFormula i f = significado f i
\end{code}

 Se denota por $Mod(F)$ al conjunto de modelos de $F$. La idea de la
 implementación en Haskell es la siguiente: En primer lugar, extraer los
 símbolos de $F$; posteriormente, calcular el conjunto potencia de los
 símbolos, que corresponde a las interpretaciones. Finalmente, devolver las
 interpretaciones que sean modelo de $F$.

 \texttt{(simbolosPropForm f)} es el conjunto formado por todos los símbolos
 proposicionales que aparecen en la fórmula f.

\index{\texttt{simbolosPropForm}}
\begin{code}
-- | Por ejemplo, 
-- 
-- >>> simbolosPropForm (p ∧ q → p)
-- [p,q]
simbolosPropForm :: FProp -> [FProp]
simbolosPropForm T          = []
simbolosPropForm F          = []
simbolosPropForm (Atom f)   = [(Atom f)]
simbolosPropForm (Neg f)    = simbolosPropForm f
simbolosPropForm (Conj f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Disj f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Impl f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Equi f g) = simbolosPropForm f `union` simbolosPropForm g
\end{code}

 \texttt{(interpretacionesForm f)} es la lista de todas las interpretaciones de
 la fórmula f.

\index{\texttt{interpretacionesForm}}
\begin{code}
-- |  Por ejemplo,
--
-- >>> interpretacionesForm (p ∧ q → p)
-- [[],[p],[q],[p,q]]
interpretacionesForm :: FProp -> [Interpretacion]
interpretacionesForm = subsequences . simbolosPropForm
\end{code}

 \texttt{(modelosFormula f)} es la lista de todas las interpretaciones de la
 fórmula f que son modelo de la misma.

\index{\texttt{modelosFormula}}
\begin{code}
-- | Por ejemplo,
--
-- >>> modelosFormula ((p ∨ q) ∧ ((no q) ∨ r)) 
-- [[p],[p,r],[q,r],[p,q,r]]
modelosFormula :: FProp -> [Interpretacion]
modelosFormula f = [i | i <- interpretacionesForm f, esModeloFormula i f]
\end{code}

\subsection{Validez, satisfacibilidad e insatisfacibilidad}

 \defn Una fórmula $F$ se dice válida si toda interpretación $i$ de $F$ es
 modelo de la fórmula. \texttt{(esValida f)} se verifica si la fórmula f es
 válida.

\index{\texttt{esValida}}
\begin{code}
-- | Por ejemplo,
--
-- >>> esValida (p → p)
-- True
-- >>> esValida (p → q)
-- False
-- >>> esValida ((p → q) ∨ (q → p))
-- True
esValida :: FProp -> Bool
esValida f = modelosFormula f == interpretacionesForm f
\end{code}

\defn Una fórmula $F$ se dice insatisfacible si no existe ninguna
 interpretación $i$ de $F$ que sea modelo de la fórmula. La función
 \texttt{(esInsatisfacible f)} se verifica si la fórmula f es insatisfacible.

\index{\texttt{esInsatisfacible}}
\begin{code}
-- | Por ejemplo,
--
-- >>> esInsatisfacible (p ∧ (no p))
-- True
-- >>> esInsatisfacible ((p → q) ∧ (q → r))
-- False
esInsatisfacible :: FProp -> Bool
esInsatisfacible = null . modelosFormula
\end{code}

\defn \label{def:sat} Una fórmula $F$ se dice satisfacible si existe al menos una
 interpretación $i$ de $F$ que sea modelo de la fórmula. La función
 \texttt{(esSatisfacible f)} se verifica si la fórmula f es satisfacible.

\index{\texttt{esSatisfacible}}
\begin{code}
-- | Por ejemplo,
--
-- >>> esSatisfacible (p ∧ (no p))
-- False
-- >>> esSatisfacible ((p → q) ∧ (q → r))
-- True
esSatisfacible :: FProp -> Bool
esSatisfacible = not . null . modelosFormula
\end{code}

\subsection{Bases de conococimiento}

 \defn Una \textit{base de conocimiento} o \textit{Knowledge Basis} ($KB$) es un conjunto
 finito de fórmulas proposicionales. Para la implementación, se importa de
 forma cualificada la librería \texttt{Data.Set} como \texttt{S}. Esta es una
 práctica muy común con esta librería y lo único que implica es que las
 funciones de dicha librería deben ir precedidas por \texttt{S.}. Por lo que se
 define el tipo de dato \texttt{KB} como:

\index{\texttt{KB}}
\begin{code}
type KB = S.Set FProp
\end{code}

 Destacar que se denotará al lenguaje proposicional de $K$ como
 $\mathcal{L}(K)$.

 Antes de extender las definiciones anteriores a más de una fórmula,
 se implementarán dos funciones auxiliares. El objetivo de dichas funciones es
 obtener toda la casuística de interpretaciones posibles de un conjunto de
 fórmulas o $KB$.

 (simbolosPropKB k) es el conjunto de los símbolos proposicionales de la base
 de conocimiento k.

\index{\texttt{simbolosPropKB}}
\begin{code}
-- | Por ejemplo,
--
-- >>> simbolosPropKB (S.fromList [p ∧ q → r, p → r])
-- [p,r,q]
simbolosPropKB :: KB -> [FProp]
simbolosPropKB = foldl (\acc f -> union acc (simbolosPropForm f)) []
\end{code}

 (interpretacionesKB k) es la lista de las interpretaciones de la base de
 conocimiento k.

\index{\texttt{interpretacionesKB}}
\begin{code}
-- |  Por ejemplo,
--
-- >>> interpretacionesKB (S.fromList [p → q, q → r])
-- [[],[p],[q],[p,q],[r],[p,r],[q,r],[p,q,r]]
interpretacionesKB :: KB -> [Interpretacion]
interpretacionesKB = subsequences . simbolosPropKB
\end{code}

 \defn Análogamente al caso de una única fórmula, se dice que $i$ es \textit{modelo} de
 $K$ ($i \vDash K$) si lo es de cada una de las fórmulas de
 $K$. \texttt{(esModeloKB i k)} se verifica si la interpretación $i$ es un 
 modelo de todas las fórmulas de la base de conocimiento $k$.

\index{\texttt{esModeloKB}}
\begin{code}
-- | Por ejemplo, 
--
-- >>> esModeloKB [r] (S.fromList [q,no p ,r])
-- False
-- >>> esModeloKB [q,r] (S.fromList [q,no p ,r])
-- True
esModeloKB :: Interpretacion -> KB -> Bool
esModeloKB i = all (esModeloFormula i)
\end{code}

 Al conjunto de modelos de $K$ se le denota por $Mod(K)$. En Haskell,
 \texttt{(modelosKB k)} es la lista de modelos de la base de conocimiento k.

\index{\texttt{modelosKB}}
\begin{code}
-- | Por ejemplo,
--
-- >>> modelosKB $ S.fromList [(p ∨ q) ∧ ((no q) ∨ r), q → r]
-- [[p],[p,r],[q,r],[p,q,r]]
-- >>> modelosKB $ S.fromList [(p ∨ q) ∧ ((no q) ∨ r), r → q]
-- [[p],[q,r],[p,q,r]]
modelosKB :: KB -> [Interpretacion]
modelosKB s = [i | i <- interpretacionesKB s, esModeloKB i s]
\end{code}

\subsection{Consistencia e inconsistencia}

 La consistencia es una propiedad de las bases de conocimiento que se puede
 definir de dos maneras distintas:

 \defn Un conjunto de fórmulas se dice \textit{consistente} si y sólo si tiene
 al menos un modelo.\\

 La función \texttt{(esConsistente k)} se verifica si la base de conocimiento
 $k$ es consistente.

\index{\texttt{esConsistente}}
\begin{code}
-- |Por ejemplo,
--
-- >>> esConsistente $ S.fromList [(p ∨ q) ∧ ((no q) ∨ r), p → r]
-- True
-- >>> esConsistente $ S.fromList [(p ∨ q) ∧ ((no q) ∨ r), p → r, no r]
-- False
esConsistente :: KB -> Bool
esConsistente = not . null . modelosKB
\end{code}

 \defn Un conjunto de fórmulas se dice \textit{inconsistente} si y sólo si no
 tiene ningún modelo.\\

 La función \texttt{(esInconsistente k)} se verifica si la base de conocimiento
 $k$ es inconsistente.

\index{\texttt{esInconsistente}}
\begin{code}
-- |Por ejemplo,
--
-- >>> esInconsistente $ S.fromList [(p ∨ q) ∧ ((no q) ∨ r), p → r]        
-- False
-- >>> esInconsistente $ S.fromList [(p ∨ q) ∧ ((no q) ∨ r), p → r, no r]  
-- True
esInconsistente :: KB -> Bool
esInconsistente = null . modelosKB
\end{code}

\subsection{Consecuencia lógica}

 La consecuencia lógica es la relación entre las premisas y la conclusión de lo
 que se conoce como un argumento deductivamente válido. Esta relación es un
 concepto fundamental en la lógica y aparecerá con asiduidad en el desarrollo
 del trabajo. \\

 \defn Se dice que $F$ es \textit{consecuencia lógica} de $K$ ($K \vDash F$) si
 todo modelo de $K$ lo es a su vez de $F$, es decir, $Mod(K) \subseteq
 Mod(F)$. Equivalentemente, $K \vDash F$ si no es posible que las premisas sean
 verdaderas y la conclusión falsa.\\

 La función \texttt{(esConsecuencia k f)} se verifica si la fórmula proposicional
 f es consecuencia lógica de la base de conocimiento o conjunto de fórmulas k.

\index{\texttt{esConsecuencia}}
\begin{code}
-- |Por ejemplo,
--
-- >>> esConsecuencia (S.fromList [p → q, q → r]) (p → r)
-- True
-- >>> esConsecuencia (S.fromList [p]) (p ∧ q)
-- False
esConsecuencia :: KB -> FProp -> Bool
esConsecuencia k f =
  null [i | i <- interpretacionesKB (S.insert f k)
          , esModeloKB i k
          , not (esModeloFormula i f)]
\end{code}

 Con el objetivo de hacer más robusto el sistema se implementarán dos
 propiedades de la relación de \textit{ser consecuencia} en lógica
 proposicional. Dichas propiedades se comprobarán con la librería \texttt{QuickCheck}
 propia del lenguaje Haskell. Es importante saber que estas evaluaciones de
 propiedades con quickCheck son sólo comprobaciones de que la
 propiedad se cumple para una batería de ejemplos. En ningún caso se puede
 confiar en que dicha propiedad se cumple el 100% de los casos; para ello sería
 necesaria una verificación formal, un problema más costoso y en ningún caso
 trivial.

 \prop Una fórmula $f$ es válida si y sólo si es consecuencia del conjunto vacío.

\begin{code}
-- |
-- >>> quickCheck prop_esValida
-- +++ OK, passed 100 tests.
prop_esValida :: FProp -> Bool
prop_esValida f =
   esValida f == esConsecuencia S.empty f
\end{code}

 \prop Una fórmula $f$ es consecuencia de un conjunto de fórmulas $k$ si y sólo
 si dicho el conjunto formado por $k$ y $\neg f$ es inconsistente.

\begin{code}
-- |
-- >>> quickCheck prop_esConsecuencia
-- +++ OK, passed 100 tests.
prop_esConsecuencia :: KB -> FProp -> Bool
prop_esConsecuencia k f =
   esConsecuencia k f == esInconsistente (S.insert (Neg f) k)
   
\end{code}

 De manera natural se extiende la definición de \textit{ser consecuencia} a
 bases de conocimiento en lugar de fórmulas, preservando la misma notación. La
 función \texttt{(esConsecuenciaKB k k')} se verifica si todas las fórmulas del
 conjunto k' son consecuencia de las del conjunto k.

\index{\texttt{esConsecuenciaKB}}
\begin{code}
-- |Por ejemplo,
--
-- >>> esConsecuenciaKB (S.fromList [p → q, q → r]) (S.fromList [p → q, p → r])
-- True
-- >>> esConsecuenciaKB (S.fromList [p]) (S.fromList [p ∧ q])
-- False
esConsecuenciaKB :: KB -> KB -> Bool
esConsecuenciaKB k = all (esConsecuencia k)
\end{code}

\subsection{Equivalencia}

 \defn Sean $F$ y $G$ dos fórmulas proposicionales, se dice que son
 equivalentes ($F \equiv G$) si tienen el mismo significado lógico, es decir,
 si  tienen el mismo valor de verdad en todas sus interpretaciones.

 La función \texttt{(equivalentes f g)} se verifica si las fórmulas
 proposicionales son equivalentes.

\index{\texttt{equivalentes}}
\begin{code}
-- |Por ejemplo,
--
-- >>> equivalentes (p → q) (no p ∨ q)
-- True
-- >>> equivalentes (p) (no (no p))
-- True
equivalentes :: FProp -> FProp -> Bool
equivalentes f g = esValida (f ↔ g)
\end{code}

 \defn Dadas $K$ y $K'$ dos bases de conocimiento, se dice que son equivalentes
 ($K \equiv K'$) si $K \vDash K'$ y $K' \vDash K$.

 La función \texttt{(equivalentesKB k k')} se verifica si las bases de
 conocimiento k y k' son equivalentes.

\index{\texttt{equivalentesKB}}
\begin{code}
-- |Por ejemplo,
--
-- >>> equivalentesKB (S.fromList [p → q,r ∨ q]) (S.fromList [no p ∨ q, q ∨ r])
-- True
-- >>> equivalentesKB (S.fromList [p ∧ q]) (S.fromList [q,p])
-- True
equivalentesKB :: KB -> KB -> Bool
equivalentesKB k k' = esConsecuenciaKB k k' && esConsecuenciaKB k' k
\end{code}

 La siguiente propiedad comprueba si las definiciones implementadas
 anteriormente son iguales en el caso de una única fórmula en la base de
 conocimiento.

 \prop Sean $F$ y $g$ dos fórmulas proposicionales, son equivalentes como
 fórmulas si y sólo si lo son como bases de conocimiento.

\begin{code}
-- |
-- >>> quickCheck prop_equivalentes
-- +++ OK, passed 100 tests.
prop_equivalentes :: FProp -> FProp -> Bool
prop_equivalentes f g =
  equivalentes f g == equivalentesKB (S.singleton f) (S.singleton g)
\end{code}

\subsection{Retracción conservativa}

 Dada una base de conocimiento resulta interesante estudiar qué fórmulas se
 pueden deducir de la misma o incluso buscar si existe otra manera de expresar
 el conocimiento, en definitiva otras fórmulas, de las que se deduzca
 exactamente la misma información. A esta relación entre bases de conocimiento
 se le conoce con el nombre de extensión:
 
 \defn Sean $K$ y $K'$ bases de conocimiento, se dice que $K$ es una
 \textit{extensión} de $K'$ si $\mathcal{L}(K') \subseteq \mathcal{L}(K)$ y
 $$\forall F \in Form (\mathcal{L} (K')) \;\; [K' \vDash F \Rightarrow K \vDash
 F]$$

% Si nos restringimos a las fórmulas consecuencia de una base de conocimiento en
% el lenguaje de la otra:

 \defn  Sean $K$ y $K'$ bases de conocimiento, se dice que $K$ es una
 \textit{extensión conservativa} de $K'$ si es una extensión tal que toda
 consecuencia lógica de $K$ expresada en el lenguaje $\mathcal{L} (K')$, es
 también consecuencia de $K'$,
 $$\forall F \in Form (\mathcal{L} (K')) \;\; [K \vDash F \Rightarrow K' \vDash
 F]$$
 es decir, $K$ extiende a $K'$ pero no se añade nueva información expresada en
 términos de $\mathcal{L}(K')$.

 \defn $K'$ es una \textit{retracción conservativa} de $K$ si y sólo si $K$ es
 una extensión conservativa de $K'$.

 Dado $\mathcal{L}' \subseteq \mathcal{L}(K)$, siempre existe una retracción
 conservativa de $K$ al lenguaje $\mathcal{L}'$. La \textit{retracción
 conservativa canónica} de $K$ a $\mathcal{L}'$ se define como:
$$[K,\mathcal{L}']=\{F\in Form(\mathcal{L}'): K \vDash F \}$$

 Esto es, $[K,\mathcal{L}']$ es el conjunto de $\mathcal{L}'$-fórmulas que son
 consecuencia de $K$. De hecho, cualquier retración conservativa sobre
 $\mathcal{L}'$ es equivalente a $[K,\mathcal{L}']$.

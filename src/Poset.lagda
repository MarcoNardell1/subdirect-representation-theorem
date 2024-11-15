\begin{code}

module Poset where

-- Standard library imports
open import Relation.Binary         using (Rel ; IsPartialOrder; Poset)
open import Level                   using (Level ; _⊔_ ; suc)
open import Relation.Unary          using (Pred)
open import Relation.Nullary        using (¬_)
open import Data.Product            using (_×_ ; ∃; ∃-syntax; proj₁ ; proj₂ ; Σ ; _,_)
open import Data.Unit.Polymorphic   using (⊤)
open import Data.Sum                using (_⊎_) 
open import Function                using (flip)

\end{code}

\subsection{Cotas, supremo e ínfimo para subconjuntos}
Primero presnetaremos la nocion de subconjuntos en agda.
Diremos que dado un conjunto A, definimos el subconjunto de A asociado a un predicado P como
∀ (x: A) → P x.

Utilizando Esto podemos definir tanto la cota superior e inferior asociada a un subconjunto de A,
dada una relacion binaria _≤_ y un elemento de A.
Notemos que asumimos que la relacion binaria que solicitamos es un orden parcial sobre A.
Luego en las siguientes secciones nos aseguraremos que efectivamente _≤_ sea un orden parcial sobre A.
Con esto tambien podemos definir tambien el supremo de un subconjunto de A.

Para la definicion del infimo, si invertimos la relacion binaria utilizada, es decir,
dada la relacion _≤_, utilizamos _≥_ y tomamos el supremo,
esto nos dara como resultado el infimo del subconjunto asociado al predicado dado.


\begin{code}
IsUpperBound : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsUpperBound _≤_ P x = ∀ y → P y → y ≤ x

IsLowerBound : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsLowerBound _≤_ P x = ∀ y → P y → x ≤ y

IsSupremum : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsSupremum _≤_ P x = IsUpperBound _≤_ P x × (∀ y → IsUpperBound _≤_ P y → x ≤ y)

IsInfimum : ∀ {a ℓ ℓ₁} {A : Set a} → Rel A ℓ → Pred A ℓ₁ → Pred A _
IsInfimum _≤_ = IsSupremum (flip _≤_) 

\end{code}

\subsection{Reticulados completos}

A continuacion definimos una operacion arbitraria asociada a subconjuntos.
Esto nos sera util para luego poder definir tanto el supremo y el infimo como operacion asociada a un reticulado completo.
\begin{code}
Op : ∀ {ℓ₁} → Set ℓ₁ → ∀ {ℓ} → Set (suc ℓ ⊔ ℓ₁)
Op A {ℓ} = Pred A ℓ → A 
\end{code}

Con lo anterior visto, ahora daremos el tipo de los reticulados completos.
Para ello, primero definiremos un \textit{record type} que nos asegure que dada,
una relacion de equivalencia _≈_ , un orden parcial _≤_ y dos operaciones arbitrarias, ⋀_, ⋁_, satisfacen las condiciones para decir que ⟨A, _≤_⟩
es un reticulado completo. Esto es que _≤_ sea un orden parcial (utilizando _≈_), que ⋀_ sea la operacion de infimo para cualquier subconjunto de A
y ⋁_ sea la operacion de supremo tambien para todo subconjunto de A. 
\begin{code}
-- Complete Lattices
{-
  A complete lattice is a partial ordered set in which all subsets have both supremum and infimum.
  𝐏 = ⟨ P , ≤ ⟩, ∀ X ⊆ P exists ⋁ X and ⋀ X.  
-}
\end{code}
\begin{code}
record IsCompleteLattice {a ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set a}
                 (_≈_ : Rel A ℓ₁) -- The underlying equality.
                 (_≤_ : Rel A ℓ₂) -- The partial order.
                 (⋁_ : Op A {ℓ₃})     -- The join operation.
                 (⋀_ : Op A {ℓ₄})     -- The meet operation.
                 : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃ ⊔ suc ℓ₄) where
    field
      isPartialOrder : IsPartialOrder _≈_ _≤_
      isSupremum : ∀ (P : Pred A ℓ₃) → IsSupremum _≤_ P (⋁ P)     
      isInfimum :  ∀ (P : Pred A ℓ₄) → IsInfimum _≤_ P (⋀ P)
    module PO = IsPartialOrder isPartialOrder
    open PO public
open IsCompleteLattice public
\end{code}

El proximo tipo es de reticulados completos en si, sus campos son el conjunto Carrier del reticulado,
y tanto las relaciones binarias y operaciones que queremos que satisfagan las condiciones antes mencionadas.
Sumamos tambien algunas propiedades sobre reticulados completos que nos seran utiles a futuro.
Estas propiedades son:
\begin{itemize}
  \item Para todo X ⊆ Carrier, entonces el infimo de X es el menor elemento de X.
  \item Renombre por derecha de la negacion sobre _≈_, si ¬ (x ≈ y) e (y ≈ z), entonces ¬ (x ≈ z).
  \item Renombre por izquierda de la negacion sobre el primer elemento en _≈_, es decir, dado ¬ (x ≈ y) y (x ≈ z), entonces ¬ (z ≈ y). 
  \item Para todo X ⊆ Carrier, El infimo de X es la mayor cota inferior de X.
  \item Propiedad de renombre, si (a ≤ b) y (b ≈ c), entonnces a ≤ c.
\end{itemize}

\begin{code}
record CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃ ⊔ suc ℓ₄)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ₁
    _≤_ : Rel Carrier ℓ₂
    ⋁_ : Op Carrier {ℓ₃}
    ⋀_ : Op Carrier {ℓ₄}
    isCompleteLattice : IsCompleteLattice _≈_ _≤_ ⋁_ ⋀_
  module CL = IsCompleteLattice isCompleteLattice
  meetL : ∀ X x → X x → (⋀ X) ≤ x
  meetL X x p =  proj₁ (CL.isInfimum X) x p  

  ¬≈-trans : ∀ {x y z} → ¬ (x ≈ y) → y ≈ z → ¬ (x ≈ z)
  ¬≈-trans ¬x≈y y≈z x≈z = ¬x≈y (CL.Eq.trans x≈z (CL.Eq.sym y≈z))

  ¬≈-transˡ : ∀ {x y z} → ¬ (x ≈ y) → x ≈ z → ¬ (z ≈ y)
  ¬≈-transˡ ¬x≈y x≈z z≈y = ¬x≈y (CL.Eq.trans x≈z z≈y)
  
  LB≤⋀ : ∀ X x → IsLowerBound _≤_ X x → x ≤ (⋀ X)
  LB≤⋀ X x LB = proj₂ (CL.isInfimum X) x LB

  ≤-eq : ∀ {x y z} → x ≤ y → y ≈ z → x ≤ z
  ≤-eq {x} {y} {z} x≤y y≈z = CL.trans x≤y (y≤z y≈z) 
    where
      y≤z : y ≈ z → y ≤ z
      y≤z y≈z = proj₁ CL.≤-resp-≈ y≈z CL.refl
 
  ≤-eqˡ : ∀ {x y z} → x ≤ y → x ≈ z → z ≤ y
  ≤-eqˡ {x} {y} {z} x≤y x≈z = CL.trans (z≤x x≈z) x≤y
    where
      z≤x : x ≈ z → z ≤ x 
      z≤x x≈z = proj₂ CL.≤-resp-≈ x≈z CL.refl

\end{code}

Con el tipo de los reticulados completos definido, ahora queremos comprobar que efectivamente un reticulado completo es tambien un Poset.
\begin{code}
CompleteLatticeIsPoset : ∀ {c ℓ₁ ℓ₂} (CL : CompleteLattice c ℓ₁ ℓ₂ ℓ₁ ℓ₁) → Poset c ℓ₁ ℓ₂
CompleteLatticeIsPoset CL = record {isPartialOrder = isPartialOrder isCompleteLattice}
  where
  open CompleteLattice CL
\end{code}

Si tomamos un conjunto A, podemos definir el predicado que nos describe el subconjunto X = A como
el predicado que puede ser satisfecho por cualquier elemento de A.

Tomando este predicado definimos el maximo y el minimo de un reticulado CL.
Para el maximo, llamado 1L lo definimos como el supremo del predicado anteriormente mencionado.
El minimo, lo llamamos 0L, y su definicion es analoga. 
\begin{code}
1L : ∀ {c ℓ₁ ℓ₂ ℓ₃ ℓ₄} (CL : CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄) → CompleteLattice.Carrier CL   
1L CL = ⋁ λ x → ⊤
  where
  open CompleteLattice CL

0L : ∀ {c ℓ₁ ℓ₂ ℓ₃ ℓ₄} (CL : CompleteLattice c ℓ₁ ℓ₂ ℓ₃ ℓ₄) → CompleteLattice.Carrier CL
0L CL = ⋀ λ x → ⊤ 
  where
  open CompleteLattice CL
\end{code}

\begin{code}
-- Requisites for Zorn's Lemma
--- Notion of Chain 
{-
  A Poset 𝐏 is called linear or chain, if it satisfies:
    (∀ x, y ∈ P) → x ≤ y ⊎ y ≤ x
-}
\end{code}
\subsection{Cadenas}
En el capitulo 1 definimos tambien que es una cadena.
A continuacion definimos los \textit{record types} para poder describir cadenas.
Primero, dado un conjunto A, un subconjunto P de A y dos relaciones binarias,
_≈_ y _≤_. Entonces, queremos asegurarnos que (A, ≤) sea un poset. Sumado a esto,
nos aseguramos que P sea una cadena.


El siguiente tipo define el poset que es una cadena, es decir que todos los subconjuntos
cerrados por las relacion de orden satisfagan que cada uno sea una cadena.
\begin{code}
record IsChain {a ℓ₁ ℓ₂ ℓ₃} {A : Set a} (P : Pred A ℓ₃) (_≈_ : Rel A ℓ₁)
               (_≤_ : Rel A ℓ₂) : Set (suc (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isChain : ∀ {x y : A} → P x → P y → x ≤ y ⊎ y ≤ x
open IsChain
  
record Chain c ℓ₁ ℓ₂ ℓ₃ (C : Set c) : Set (suc(c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  infix 4 _≈_ _≤_
  field
    isSubPoset : Pred C ℓ₃ 
    _≈_ : Rel C ℓ₁
    _≤_ : Rel C ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_
    isChain : IsChain isSubPoset _≈_ _≤_
open Chain
\end{code}

Similarmente a como lo mostramos anteriormente, tambien podemos demostrar que un poset de cadena es un poset.
\begin{code}
ChainIsPoset : ∀ {c ℓ₁ ℓ₂ ℓ₃} {Cr : Set c} → Chain c ℓ₁ ℓ₂ ℓ₃ Cr → Poset c ℓ₁ ℓ₂
ChainIsPoset C = record { isPartialOrder = isPartialOrder C }
\end{code}
\begin{code}[hide]
-- maximal elements
{-
  Let 𝐏 be a Poset, An element x is maximal in 𝐏, if ¬ ∃ y ∈ A → x ≤ y. 
-}
\end{code}

\subsection{Lema de Zorn}
En esta seccion veremos tanto los requisitos como la formalizacion del Lema de Zorn.
Ahora definimos la nocion de que un elemento es maximal. Dada dos relaciones binarias _≈_ y _≤_,
asumiendo que _≤_ es un orden parcial y _≈_ es una relacion de equivalencia,
entonces x ∈ A es maximal si no se da que ∃ y tal que (x ≤ y) y ¬ (x ≈ y).  
\begin{code}
IsMaximal : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → A → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
IsMaximal _≈_ _≤_ x = ¬ (∃[ y ] (x ≤ y ×  ¬(x ≈ y)))
\end{code}

\begin{code}
-- Zorn's Lemma
{-
  Let 𝐏 be a nonempty Poset, Suppose that every chain in P has an upper bound.
  Then 𝐏 has a maximal element
-}

-- Assuming Zorn's Lemma as an axiom
\end{code}

Utilizaremos las construcciones anteriores para enunciar el \textit{Lema de Zorn}.
Asumiermos este lema como un axioma y lo tomamos sin prueba.  Definimos de la siguiente manera este lema:
\begin{code}
ZornsLemma : ∀ {c ℓ₁ ℓ₂ ℓ₃} (P : Poset c ℓ₁ ℓ₂) → Set _
ZornsLemma {c} {ℓ₁} {ℓ₂} {ℓ₃} P = (∀ (C : Chain c ℓ₁ ℓ₂ ℓ₃ A)
                 → ∃[ x ] (IsUpperBound (_≤_ C) (isSubPoset C) x))
             → ∃[ y ] (IsMaximal  _≈p_
                                  _≤p_ y)
  where
  open Poset P renaming ( _≤_ to _≤p_
                        ; _≈_ to _≈p_
                        ; Carrier to A
                          ) 
\end{code}

Definimos ahora la nocion de Intervalo de un Poset. Para un poset $\mathbf{P}$, dos elementos $a , b \in P$ y una prueba de $a \leq b$ definimos el predicado I[_ , _ ] _ de la siguiente forma.
\begin{code}
{-
  Let 𝐏 a poset, a, b ∈ P. We define the interval 𝐈[ a , b ] as the subset of P such that {x ∈ P : a ≤ x ≤ b}
-}

module _ {c ℓ₁ ℓ₂}  (𝐏 : Poset c ℓ₁ ℓ₂) where
  open Poset 𝐏 renaming (Carrier to P ; _≤_ to _≤p_ ; isPartialOrder to PO)
  open IsPartialOrder PO
  𝐈[_][_,_] : ∀ (a b : P) → Pred P ℓ₂ 
  𝐈[_][_,_] a b x = (a ≤p x) × (x ≤p b)

\end{code}

Ahora mostraremos la proposicion 2.14 sobre como definir reticulados completos. A partir de un Poset P definimos un predicado para todo subconjunto de P, escribimos reticulados completos de la siguiente manera.

\begin{code}
{-
  Let 𝐏 a Poset in which inf X exists for each X ⊆ P. Then 𝐏 is a complete lattice.
-}
module _ {c ℓ₁ ℓ₂} (𝐏 : Poset c ℓ₁ ℓ₂) where
  open Poset 𝐏 renaming (Carrier to P ; _≤_ to _≤p_ ; isPartialOrder to PO)
  open IsPartialOrder PO

  postulate
    compLatticeDef : ∀ {ℓ} (X : Pred P ℓ) (⋀_ : Op P)
                   → IsInfimum _≤p_ X (⋀ X)
                   → CompleteLattice c ℓ₁ ℓ₂ ℓ₂ ℓ₂

\end{code}

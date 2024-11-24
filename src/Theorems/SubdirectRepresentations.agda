open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Theorems.SubdirectRepresentations {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (Setoid ; IsEquivalence ; _⇔_)
open import Function using (Func)

open import Relation.Binary.PropositionalEquality as ≡ using ()
import Relation.Binary.Reasoning.Setoid           as SReasoning  using ( begin_ ; step-≈˘; step-≈; _∎)


open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Relations using (0rel ; fker)

open import Prod.SubdirIrreducible {𝑆 = 𝑆}
open import Prod.NatMapProps {𝑆 = 𝑆}
open import Prod.Subdirect {𝑆 = 𝑆}
open import Prod.Subembedding {𝑆 = 𝑆}
open import Structures.Algebras {𝑆 = 𝑆}
open import Structures.CompLattices {𝑆 = 𝑆}
open import Isomorphisms.Isomorphisms {𝑆 = 𝑆}
open import Lattice
open import Poset
open import Utils.Axioms
open import Utils.Definitions

private variable α ρᵅ i : Level
open Func renaming (f to <$>)
open MeetIrreducible 
{-
 Theorem :
 An algebra 𝐀 is subdirectly irreducible iff 0_A is completely meet irreducible in Con 𝐀.
 More generally, if θ is a congruence on an algebra 𝐀, then 𝐀／θ is subdirectly irreducible
 iff θ is completely meet irreducible in Con 𝐀. 

-}

{- Tomemos un conjunto de indices, un algebra no trivial 𝐀 y una familia de algebras del mismo tipo de 𝐀,
esta familia sera la que formara la representacion de 𝐀
-}

{- 𝓐 deberia ser la familia de todas las algebras cocientes -} 
module _ {I : Set i} (𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) (𝓐 : I → Algebra α ρᵅ) where

  Alg : Algebra α ρᵅ
  Alg = proj₁ 𝐀
  
  open Algebra Alg renaming ( Domain to A
                            ; Interp to AInterp
                            )
  open Algebra (⨅ 𝓐) renaming (Domain to ⨅A)
  open Setoid ⨅A renaming (_≈_ to _≈b_)

  -- Lattice of congruences of 𝐀 
  CongsOf𝐀 : CompleteLattice (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ)) (α ⊔ (ov ρᵅ))
  CongsOf𝐀 =  congCompLattice Alg

  open CompleteLattice CongsOf𝐀 renaming (Carrier to Cg)
-- Aca debemos ver que efectivamente la congruencia dada por 0_A pertenece al universo del reticulado de congruencias
{-
  No se si nos podemos asegurar porque no sabemos la forma del reticulado de congruencias todavia.
-}
  0rel∈Cg : Cg
  0rel∈Cg = {!0relCong!}
{-
  We are going to split the theorem above in two propositions for each of the statements,
  the particular for 𝐀 and the general for each 𝐀／θ.
-} 


-- first we are going to particular case for 𝐀 to be subdirectly irreducible
{- for this we need to divide this into two cases
 1. A is subdir irreducible implies 0_A is CMI in Con 𝐀
 2. 0_A is CMI in Con 𝐀 implies A is subdir irreducible
-}

{-
  bundles → records types
  structures → sigma types

  Un problema dado por bundles es que el heredar propiedades no se ve posible, dado que los records son estructuras de mas alto nivel, a su vez agregan mas complejidad, la misma puede ser resuelta con renombres y otras tacticas. A priori el pasar las congruencias tiene que ir por otro lado.
  como no podemos asegurar que el carrier sean las congruencias podemos:
    - Escribir una funcion que dado un set y una prueba de que es un reticulado completo,
    construir un par donde el primer elemento es un bundle y el segundo un record. 
-}

-- Proving that 0 is a congruence relation over 𝐀
module _ (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) where
  open Algebra (proj₁ n𝐀) renaming ( Domain to A
                                   ; Interp to AInterp
                                   )
  open Setoid A renaming ( _≈_ to _≈ₐ_
                         ; refl to arefl
                         ; sym to asym
                         ; trans to atrans
                         )
  
  0relCong : Con (proj₁ n𝐀) {ρᵅ}
  0relCong = 0rel {𝐴 = A} {𝐵 = A} {ℓ = ρᵅ} , isCong
    where
      0isEquiv : IsEquivalence (0rel {𝐴 = A} {𝐵 = A} {ℓ = ρᵅ})
      0isEquiv = record { refl = lift arefl
                        ; sym = λ x0y → lift (asym (lower x0y))
                        ; trans = λ x0y y0z → lift (atrans (lower x0y) (lower y0z))
                        }

      open IsEquivalence 0isEquiv renaming (refl to 0refl ; sym to 0sym ; trans to 0trans)
      0comp : (proj₁ n𝐀) ∣≈ 0rel {𝐴 = A} {𝐵 = A} {ℓ = ρᵅ}
      0comp 𝑓 {x} {y} x0y = lift
        (begin
        <$> AInterp (𝑓 , λ a → (x a)) ≈⟨ cong AInterp (≡.refl , λ a → lower (x0y a)) ⟩
        <$> AInterp (𝑓 , λ a → (y a))
        ∎)
        where
          open SReasoning A

      isCong : IsCongruence (proj₁ n𝐀) (0rel {𝐴 = A} {𝐵 = A} {ℓ = ρᵅ})
      isCong = record { reflexive = λ x=y → lift x=y
                      ; is-equivalence = 0isEquiv
                      ; is-compatible =  0comp
                      }

module _ (𝐀si : SubdirectlyIrreducible {i = α ⊔ (ov ρᵅ)} {α} {ρᵅ}) where
  open SubdirectlyIrreducible 𝐀si renaming ( base to n𝐀
                                         ; isSubIrr to sb
                                         )
  𝐁 : Algebra α ρᵅ
  𝐁 = proj₁ n𝐀

  open Algebra 𝐁 renaming (Domain to B)
  open Setoid B renaming (_≈_ to _≈b_)
{-
  conRCL : CompleteLattice {!!} {!!} {!!} {!!} {!!}
  conRCL = congCompLattice 𝐁 
-}
  ⇔-closed : ∀ (P : Pred (Con 𝐁 {ρᵅ}) (α ⊔ (ov ρᵅ))) → Set (α ⊔ (ov ρᵅ))
  ⇔-closed P = ∀ x y → P x → (proj₁ x) ⇔ (proj₁ y) → P y
  
  IsCongCMI : ∀ (C : Con 𝐁 {ρᵅ}) → Set (suc (α ⊔ (ov ρᵅ)))
  IsCongCMI C = (¬ (∀ x y → (proj₁ C) x y)) × (∀ P → ⇔-closed P  → proj₁ (⋀c 𝐁 P) ⇔ (proj₁ C) → P C)
  
  0CMI : IsCongCMI (0relCong n𝐀) 
  0CMI = {!!} , 0=⋀P→θ=0
    where
      0=⋀P→θ=0 : (P : Pred (Con 𝐁 {ρᵅ}) (α ⊔ (ov ρᵅ)))
               → ⇔-closed P
               → proj₁ (⋀c 𝐁 P) ⇔ proj₁ (0relCong n𝐀)
               → P (0relCong n𝐀)
      0=⋀P→θ=0 P Pclosed ⋀P=0 = {!!}
        where
          {- defining index set as the congruences on P-}
          ix : Set (α ⊔ (ov ρᵅ))
          ix = Σ[ x ∈ Con 𝐁 {ρᵅ}] P x

          {- so we can define the family of congruences as all the congruences that satisfies P -}
          CongIx : ix → Con 𝐁 {ρᵅ}
          CongIx j = proj₁ j

          {- defining the family of algebras as the quotients of P-}
          quotAlgs : ix → Algebra α ρᵅ
          quotAlgs j = 𝐁 ╱ (proj₁ j)

          {- proving that infimum operator is equal to arbitrary intersection -}
          ⋀P=∩P : ⋂ᵣ {s = ρᵅ} ix (familyOfRels 𝐁 CongIx CongIx) ⇔ proj₁ (0relCong n𝐀)
          ⋀P=∩P = (λ x∈∩P → proj₁ ⋀P=0 λ R R∈P → lower (x∈∩P (R , R∈P)))
                , λ x0y (R , R∈P)→ lift (proj₂ ⋀P=0 x0y R R∈P)

          {- with the previous results we can use the first part of Proposition 3.17 to
          define a subdirect embedding using the natural map of an algebra to the product of
          its quotient algebras, in this case ⨅ quotAlgs. -}
          natMap : IsSubEmb 𝐁 quotAlgs (NatMap 𝐁 CongIx) 
          natMap = NatMapIsSubEmb 𝐁 CongIx ⋀P=∩P

          subemb : SubdirectEmbedding 𝐁 quotAlgs
          subemb = NatMap 𝐁 CongIx , natMap

          {- because of 𝐀 is a subdirectly irreducible algebra, we have an isomorphism of pᵢ ∘ h,
            for all subdirect embedding h. -}

          projIsIso : IsIso 𝐁 (⨅ quotAlgs) (proj₁ subemb) 
          projIsIso = {!!}
{-

TODO:
1. Modularizar mejor
2. Avanzar con la prueba de 0CMI, tener en contexto que el algebra sea subdirectly irreducible
3. Ver la vuelta

-}

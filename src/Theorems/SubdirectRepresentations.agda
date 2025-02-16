open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Theorems.SubdirectRepresentations {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary using (Setoid ; IsEquivalence ; _⇔_ ; Rel)
open import Function using (Func ; id)
open import Function.Construct.Composition using (function)

open import Relation.Binary.PropositionalEquality as ≡ using ()
import Relation.Binary.Reasoning.Setoid           as SReasoning  using ( begin_ ; step-≈˘; step-≈; _∎)


open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Homomorphisms using (hom ; IsHom ; IsMon)
open import Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆}
open import Setoid.Relations using (0rel ; fker)
open import Setoid.Functions using (IsInjective ; IsSurjective ; eq)

open import Prod.SubdirIrreducible {𝑆 = 𝑆} using ( SubdirectlyIrreducible ; IsSubIrreducible )
open import Prod.NatMapProps {𝑆 = 𝑆} using ( familyOfRels
                                           ; NatMapIsSubEmb
                                           ; NatMap
                                           ; subemb→quot≅Bᵢ
                                           ; famOfCong
                                           ; ∩=0
                                           )
open import Prod.Subdirect {𝑆 = 𝑆} using ( ⨅-fun )
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
  
-- Defining that a congruence is not 1_A
module _ (𝐀 : Algebra α ρᵅ) where
  θisNot1 : (θ : Con 𝐀 {ρᵅ}) → Set (α ⊔ ρᵅ)
  θisNot1 θ = Σ[ x ∈ 𝕌[ 𝐀 ] ]
              Σ[ y ∈ 𝕌[ 𝐀 ] ]
              ¬ (proj₁ θ) x y

-- Redifining an element is completelyMeetIrreducible
{- Using this avoids the use of CongCompleteLattice -}
module _ (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) where
  base : Algebra α ρᵅ
  base = proj₁ n𝐀

  ⇔-closed : ∀ (P : Pred (Con base {ρᵅ}) (α ⊔ (ov ρᵅ)))
            → Set (α ⊔ (ov ρᵅ))
  ⇔-closed P = ∀ x y → P x → (proj₁ x) ⇔ (proj₁ y) → P y
  
  IsCongCMI : ∀ (C : Con base {ρᵅ}) → Set (suc (α ⊔ (ov ρᵅ)))
  IsCongCMI C =
    θisNot1 base C ×
    (∀ P → ⇔-closed P  → proj₁ (⋀c base P) ⇔ (proj₁ C) → P C)

-- 𝐀 is subdirectly irreducible implies 0_A is CMI in Con 𝐀
module _ (𝐀si : SubdirectlyIrreducible {i = α ⊔ (ov ρᵅ)} {α} {ρᵅ}) where
  open SubdirectlyIrreducible 𝐀si renaming ( base to n𝐀
                                           ; isSubIrr to sb
                                           )
  𝐁 : Algebra α ρᵅ
  𝐁 = proj₁ n𝐀

  𝐁isNonTriv : IsNonTrivialAlgebra 𝐁
  𝐁isNonTriv = proj₂ n𝐀

  x : 𝕌[ 𝐁 ]
  x = proj₁ 𝐁isNonTriv

  y : 𝕌[ 𝐁 ]
  y = proj₁ (proj₂ 𝐁isNonTriv)
  
  open Algebra 𝐁 renaming (Domain to B)
  open Setoid B renaming (_≈_ to _≈b_)

  x≠y : ¬ (x ≈b y)
  x≠y = proj₂ (proj₂ 𝐁isNonTriv)
  
  0CMI : IsCongCMI n𝐀 (0relCong n𝐀) 
  0CMI = 0isNot1 , 0=⋀P→θ=0
    where
      x≠y→¬x0y : ∀ {x y : 𝕌[ 𝐁 ]}
               → ¬ (x ≈b y)
               → ¬ (proj₁ (0relCong n𝐀) x y)
      x≠y→¬x0y ¬x=y (lift x0y) = ¬x=y x0y

      0isNot1 : Σ[ x ∈ 𝕌[ 𝐁 ] ]
                Σ[ y ∈ 𝕌[ 𝐁 ] ]
                ¬ (proj₁ (0relCong n𝐀)) x y
      0isNot1 = x , y , x≠y→¬x0y x≠y
      
      0=⋀P→θ=0 : (P : Pred (Con 𝐁 {ρᵅ}) (α ⊔ (ov ρᵅ)))
               → ⇔-closed n𝐀 P
               → proj₁ (⋀c 𝐁 P) ⇔ proj₁ (0relCong n𝐀)
               → P (0relCong n𝐀)
      0=⋀P→θ=0 P Pclosed ⋀P=0 = 0∈P
        where
          {- defining index set as the congruences on P-}
          ix : Set (α ⊔ (ov ρᵅ))
          ix = Σ[ θ ∈ Con 𝐁 {ρᵅ}] P θ

          {- so we can define the family of congruences as all the congruences that satisfies P -}
          CongIx : ix → Con 𝐁 {ρᵅ}
          CongIx j = proj₁ j

          {- defining the family of algebras as the quotients of P-}
          quotAlgs : ix → Algebra α ρᵅ
          quotAlgs j = 𝐁 ╱ (CongIx j)

          {- proving that infimum operator is equal to arbitrary intersection -}
          ⋀P=∩P : ⋂ᵣ {s = ρᵅ} ix (familyOfRels 𝐁 CongIx) ⇔ proj₁ (0relCong n𝐀)
          ⋀P=∩P = (λ x∩Py → proj₁ ⋀P=0 λ θ θ∈P → lower (x∩Py (θ , θ∈P)))
                , λ x0y (θ , θ∈P) → lift (proj₂ ⋀P=0 x0y θ θ∈P)

          {- with the previous results we can use the first part of Proposition 3.17 to
          define a subdirect embedding using the natural map of an algebra to the product of
          its quotient algebras, in this case ⨅ quotAlgs. -}
          natMapIsSubEmb : IsSubEmb 𝐁 quotAlgs (NatMap 𝐁 CongIx) 
          natMapIsSubEmb = NatMapIsSubEmb 𝐁 CongIx ⋀P=∩P

          subemb : SubdirectEmbedding 𝐁 quotAlgs
          subemb = NatMap 𝐁 CongIx , natMapIsSubEmb

          {- because of 𝐀 is a subdirectly irreducible algebra,for some i ∈ I we have an isomorphism of pᵢ ∘ h,
            for all subdirect embedding h. Now we have to check that pᵢ is an iso.-}

          projIsIso : Σ[ j ∈ ix ]
                    (IsIso 𝐁 (quotAlgs j)
                    (function (proj₁ subemb) (⨅-fun quotAlgs j)))
          projIsIso = sb quotAlgs subemb

          indexOfProj : ix
          indexOfProj = proj₁ projIsIso


          open IsIso (proj₂ projIsIso) renaming ( Hom to h ; IsBij to bj)
          open Algebra (quotAlgs (proj₁ projIsIso)) renaming (Domain to A/θj) 
          pᵢ∘g : Func B A/θj
          pᵢ∘g = function (proj₁ subemb) (⨅-fun quotAlgs indexOfProj)
          {- Now we have to prove that 0_A = ker (pᵢ ∘ NatMap) = θᵢ.
          We are going to split this in three checks
            1. 0_A = ker (pᵢ ∘ NatMap)
            2. ker (pᵢ ∘ NatMap) = θᵢ
            3. 0_A = θᵢ
          -}
          0=kerProj : proj₁ (0relCong n𝐀) ⇔ (fker pᵢ∘g)
          0=kerProj =
            (λ x0y → cong pᵢ∘g (lower x0y))
            , λ xy∈ker → lift (proj₁ bj xy∈ker)
          
          kerProj=θᵢ : fker pᵢ∘g ⇔ proj₁ (proj₁ indexOfProj)
          kerProj=θᵢ = id , id

          0=θᵢ : proj₁ (0relCong n𝐀) ⇔ proj₁ (proj₁ indexOfProj)
          0=θᵢ = ⇔hetTrans 0=kerProj kerProj=θᵢ

          {- Because 0=θᵢ then 0 ∈ P, so 0 is completely meet irreducible -}
          0∈P : P (0relCong n𝐀)
          0∈P = Pclosed (proj₁ indexOfProj)
                        (0relCong n𝐀)
                        (proj₂ indexOfProj)
                        (⇔hetSym 0=θᵢ) 

-- 0_A CMI → 𝐀 is subdirectlyIrreducible
module _ (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) (0cmi : IsCongCMI n𝐀 (0relCong n𝐀)) where
  open Algebra (proj₁ n𝐀) renaming (Domain to A)
  open Setoid A renaming (Carrier to Car ; _≈_ to _≈a_)
  open IsEquivalence (⇔isEq {ℓ = ρᵅ} {A = Car}) renaming ( trans to rtrans
                                                          ; sym to rsym
                                                          )
    
  0→𝐀isSubIrr : IsSubIrreducible n𝐀 {i = ov ρᵅ}
  0→𝐀isSubIrr {I = ix} 𝓑 g =
    proj₁ 0∈P
   , record { Hom = record { compatible = comp (proj₁ 0∈P) }
            ; IsBij = pi∘gInj , pi∘gSurj
            }

    where
      open IsSubEmb (proj₂ g) renaming (isMon to mono ; isSubdirProd to subp)
      open IsMon mono renaming (isHom to gHom ; isInjective to inj)
      open IsHom gHom renaming (compatible to comp)
      
      congs : ∀ (j : ix) → Con (proj₁ n𝐀) {ρᵅ}
      congs j = (famOfCong (proj₁ n𝐀) 𝓑 g j)

      rels : ∀ (j : ix) → Rel Car ρᵅ
      rels j = proj₁ (congs j)

      0isInf : ⋂ᵣ {s = α ⊔ (ov ρᵅ) } ix rels ⇔ (proj₁ (0relCong n𝐀))
      0isInf = ∩=0 (proj₁ n𝐀) 𝓑 g

      P : Pred (Con (proj₁ n𝐀) {ρᵅ}) (α ⊔ (ov ρᵅ))
      P x = Σ[ j ∈ ix ] proj₁ x ⇔ rels j

      Pisclosed : ⇔-closed n𝐀 P
      Pisclosed _ _ (j , x=θⱼ) x=y = j , (rtrans (rsym x=y) x=θⱼ) 
        
      ∩⇔⋀ : ⋂ᵣ {s = α ⊔ (ov ρᵅ) } ix rels ⇔ proj₁ (⋀c (proj₁ n𝐀) P)
      ∩⇔⋀ = (λ {xy∈∩ R (j , R=xj) → proj₂ R=xj (lower (xy∈∩ j))})
            , λ xy∈⋀ i → lift (xy∈⋀ (congs i) (i , id , id))

      0⇔⋀ : proj₁ (⋀c (proj₁ n𝐀) P) ⇔ proj₁ (0relCong n𝐀) 
      0⇔⋀ = ⇔hetTrans (⇔hetSym ∩⇔⋀) 0isInf 
        
      0∈P : P (0relCong n𝐀)
      0∈P = proj₂ 0cmi P Pisclosed 0⇔⋀

      open Algebra (𝓑 (proj₁ 0∈P)) renaming (Domain to Bi)
      open Setoid Bi renaming (_≈_ to _≈b ; isEquivalence to equiv)
      open IsEquivalence equiv renaming (sym to bisym ; trans to bitrans)
      
      pᵢ∘g : Func A Bi
      pᵢ∘g = function (proj₁ g) (⨅-fun 𝓑 (proj₁ 0∈P))
      
      iso : (j : ix) → ((proj₁ n𝐀) ╱ (congs j)) ≅ (𝓑 j)
      iso j = proj₂ (subemb→quot≅Bᵢ (proj₁ n𝐀) 𝓑 g j)

      open _≅_ (iso (proj₁ 0∈P)) renaming (to to h)

      pi∘gInj : IsInjective pᵢ∘g
      pi∘gInj fx=fy = lower (proj₂ (proj₂ 0∈P) fx=fy)

      pi∘gSurj : IsSurjective pᵢ∘g
      pi∘gSurj {y} with subp (proj₁ 0∈P) {y}
      ... | eq (bi , a , bi=ga) y=gt =
        eq a (bitrans y=gt (bisym (bi=ga (proj₁ 0∈P))))

  SubIrr : SubdirectlyIrreducible {i = ov ρᵅ} {α} {ρᵅ}
  SubIrr = record { base = n𝐀 ; isSubIrr = 0→𝐀isSubIrr }

{- General case of 3.23 -}
{- Here the congruence θ can't be 1_A because 1_A is not completely meet irreducible on Con 𝐀.
Also, 𝐀/1_A is a trivial algebra because there is only one equivalence class on 𝐀.
-}

-- prerequisites
module _ (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) where
  𝐀 : Algebra α ρᵅ
  𝐀 = proj₁ n𝐀

-- No trivial congruences 
  non1Cong : Set (ov ρᵅ ⊔ α)
  non1Cong = Σ[ θ ∈ (Con 𝐀 {ρᵅ}) ] θisNot1 𝐀 θ

-- With a non trivial congruence, the quotient algebra is not rivial
  quotIsNonTrivial : (θ : non1Cong) 
                   → IsNonTrivialAlgebra (𝐀 ╱ (proj₁ θ))
  quotIsNonTrivial (θ , θ≠1) = θ≠1
    
  quotNonTrivial : (θ : non1Cong)
                 →  NonTrivialAlgebra {β = α} {ρ = ρᵅ}
  quotNonTrivial θ = (𝐀 ╱ (proj₁ θ)) , quotIsNonTrivial θ

-- Then postulating the general case
module _ (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) where
  postulate
    𝐀/θisSubIrr→θCMI : ∀ (θ : non1Cong n𝐀)
                      → IsSubIrreducible (quotNonTrivial n𝐀 θ) {i = i}
                      → IsCongCMI n𝐀 (proj₁ θ)
    θCMI→𝐀/θisSubIrr : ∀ (θ : non1Cong n𝐀)
                      → IsCongCMI n𝐀 (proj₁ θ)
                      → IsSubIrreducible (quotNonTrivial n𝐀 θ) {i = i}




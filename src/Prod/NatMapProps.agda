open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.NatMapProps {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid ; _⇒_ ; Reflexive ; IsEquivalence ; _⇔_) renaming (Rel to BinRel)
open import Relation.Nullary using (¬_)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Homomorphisms {𝑆 = 𝑆}
open import Setoid.Functions  using (IsInjective ; IsSurjective ; ⊙-IsSurjective)
open import Setoid.Relations using (0rel ; fker)

open import Prod.Subembedding
open import Prod.Subdirect using (⨅-fun)
open import Lattice using (absurd)

private variable α β ρᵅ ρᵝ i : Level

open Func renaming (f to <$>) 

-- postulating axioms of negation and quantifiers
postulate
  ¬∀→∃¬ : ∀ {a b} {A : Set a} {B : A → Set b} → ¬ (∀ (x : A) → (B x)) → Σ[ x ∈ A ] ¬ (B x) 
  ¬∃→∀¬ : ∀ {a b} {A : Set a} {B : A → Set b} → ¬ (Σ[ x ∈ A ]  (B x)) → ∀ (x : A) → ¬ (B x)

-- arbitray intersection

⋂ᵣ : ∀ {i ρ s a} {A : Set a} (I : Set i) → (I → BinRel A ρ) → BinRel A (ρ ⊔ i ⊔ s)
⋂ᵣ {j} {ρ} {s} I R = λ x y → (i : I) → Lift (ρ ⊔ j ⊔ s) (R i x y)

-- family of homomorphisms
module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) where
  record FamOfHoms : Set (ov (i ⊔ α ⊔ β ⊔ ρᵅ ⊔ ρᵝ)) where
    field
      family : ∀ (j : I) → hom 𝐁 (𝓐 j)

-- separate points
module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) where
  open Algebra 𝐁 renaming (Domain to B)
  open Setoid B 
  famSeparatePoints : (h : FamOfHoms 𝐁 𝓐) → Set (i ⊔ β ⊔ ρᵝ ⊔ ρᵅ)
  famSeparatePoints h = (x  y : 𝕌[ 𝐁 ]) → ¬ (x ≈ y) → Σ[ j ∈ I ] (pred j x y) 
    where
      open FamOfHoms h
      pred : (j : I) (x y : 𝕌[ 𝐁 ]) → Set ρᵅ
      -- usar la igualdad de 𝓐 j
      pred j x y = ¬ (<$> (proj₁ (family j)) x) ≈aj (<$> (proj₁ (family j)) y)   
        where
          open Algebra (𝓐 j) renaming (Domain to Aj)
          open Setoid Aj renaming (_≈_ to _≈aj_)

-- proposition 3.14
{-
  Let hᵢ be a homomorphism from 𝐁 to 𝐀ᵢ, for each i ∈ I, and let h = ⊓_{i ∈ I} hᵢ.
  Then ker (h) = ⋂ᵣ I ker(hᵢ). Furthermore the following are equivalent:
  (a) The family ⟨ hᵢ : i ∈ I ⟩ separate points
  (b) h is injective
  (c) ⋂ᵣ I ker(hᵢ) = 0_B
-}


module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) (h : FamOfHoms 𝐁 𝓐) where

  open Algebra 𝐁 renaming (Domain to B)
  open Setoid B renaming (Carrier to Car)
  open Algebra (⨅ 𝓐) renaming (Domain to ⨅A)
  open Setoid ⨅A renaming (_≈_ to _≈A_)
  open FamOfHoms h

  kerOfFam : I → BinRel 𝕌[ 𝐁 ] ρᵅ
  kerOfFam j = fker (proj₁ (family j))


  kerOfFamIsRefl : (j : I) → Reflexive (kerOfFam j)
  kerOfFamIsRefl j = Ajrefl
    where
      open Algebra (𝓐 j) renaming (Domain to Aj)
      open Setoid Aj renaming (_≈_ to _≈aj_ ; isEquivalence to eq)
      open IsEquivalence eq renaming (refl to Ajrefl)

  {- A prod of homomorphisms h = ⨅ hᵢ, where ⟨ hᵢ : hom 𝐁 (𝓐 i) ⟩ is a family of homomorphisms,
  is such that h(b)(i) = hᵢ(b)
  -} 
  IsProdOfHoms : hom 𝐁 (⨅ 𝓐)
  IsProdOfHoms  = F , record { compatible = λ j → IsHom.compatible (proj₂ (family j))}
    where
      F : Func (𝔻[ 𝐁 ]) (𝔻[ (⨅ 𝓐) ])
      F = record { f = λ b i  → <$> (proj₁ (family i)) b  ; cong = λ {x} {y} x=y j → cong (proj₁ (family j)) x=y }


  kerOfProd→⋂kers : ∀ (a b : 𝕌[ 𝐁 ]) → (fker ((proj₁ IsProdOfHoms))) a b → (⋂ᵣ {s = i ⊔ α} I kerOfFam) a b
  kerOfProd→⋂kers a b  a≈ₖb i = lift (a≈ₖb i)

  ⋂kers→kerOfProd : ∀ (a b : 𝕌[ 𝐁 ]) → (⋂ᵣ {s = i ⊔ α} I kerOfFam) a b → (fker ((proj₁ IsProdOfHoms))) a b
  ⋂kers→kerOfProd a b a≈⋂b = λ j → eq j (a≈⋂b j)
    where
      eqType : (j : I)  → Set ρᵅ
      eqType j  = <$> (proj₁ IsProdOfHoms) a j ≈aj <$> (proj₁ IsProdOfHoms) b j
        where 
          open Algebra (𝓐 j) renaming (Domain to Aj)
          open Setoid Aj renaming (_≈_ to _≈aj_)

      eq : (j : I) →  Lift (α ⊔ i ⊔ ρᵅ) (kerOfFam j a b) → eqType j 
      eq j (lift p) = p

 -- proving ⟨hᵢ : i ∈ I⟩ separates points implies h is injective 
  firstEquiv : famSeparatePoints 𝐁 𝓐 h → IsInjective (proj₁ IsProdOfHoms)
  firstEquiv sp {x} {y} = λ inj → absurd (x ≈ y) λ ¬x≈y → proj₂ (sp x y ¬x≈y) (inj (proj₁ (sp x y ¬x≈y)))
 
  -- proving h is injective implies ∩ ker hᵢ = 0B
  {-
  First, we separate the statment in:
  1. ∩ ker hᵢ ⊆ 0B
  2. 0B ⊆ ∩ ker hᵢ
 -}
  
  0⊆∩ : 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} ⇒ ⋂ᵣ {s = i ⊔ α} I kerOfFam
  0⊆∩ {x = x} {y = y} (lift xθy) j = lift (cong (proj₁ (family j)) xθy)
  
  secondEquiv₁ : IsInjective (proj₁ IsProdOfHoms) → ⋂ᵣ {s = i ⊔ α} I kerOfFam ⇒ 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ}
  secondEquiv₁ inj {x} {y} = λ eq → lift (inj (⋂kers→kerOfProd x y eq))

  secondEquiv₂ : IsInjective (proj₁ IsProdOfHoms) → 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} ⇒ ⋂ᵣ {s = i ⊔ α} I kerOfFam
  secondEquiv₂ inj {x} {y} = 0⊆∩

  thirdEquiv : ⋂ᵣ {s = i ⊔ α} I kerOfFam ⇔ 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} → famSeparatePoints 𝐁 𝓐 h
  thirdEquiv (∩→0 , 0→∩) = λ x y ¬x≈y → proj₁ (¬x≈y→¬kerhᵢ ¬x≈y) , proj₂ (¬x≈y→¬kerhᵢ ¬x≈y)
    where
      unLiftEq : {x y : Car} → Lift ρᵅ (x ≈ y) → x ≈ y
      unLiftEq (lift p) = p
      
      ¬x≈y→¬0 : {x y : Car} → ¬ (x ≈ y) → ¬ (0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} x y)
      ¬x≈y→¬0 ¬x≈y = λ x≈y∈0 → ¬x≈y (unLiftEq x≈y∈0)

      ¬0→¬∩ker : {x y : Car} → ¬ (0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} x y) → ¬ (⋂ᵣ {s = i ⊔ α} I kerOfFam x y)
      ¬0→¬∩ker  ¬0 = λ x≈y∈∩ker → ¬0 (∩→0 x≈y∈∩ker)

      ¬∩ker→¬kerhᵢ : {x y : Car} → ¬ (⋂ᵣ {s = i ⊔ α} I kerOfFam x y) → Σ[ j ∈ I ] ¬(kerOfFam j x y)
      ¬∩ker→¬kerhᵢ {x} {y} ¬∩ = ¬∀→∃¬ λ x≈ajy → ¬∩ (kerOfProd→⋂kers x y x≈ajy)

      ¬x≈y→¬kerhᵢ : {x y : Car} → ¬ (x ≈ y) → Σ[ j ∈ I ] ¬(kerOfFam j x y)
      ¬x≈y→¬kerhᵢ ¬x≈y = (¬∩ker→¬kerhᵢ (¬0→¬∩ker (¬x≈y→¬0 ¬x≈y)))

  ∩⇔0→Inj : ⋂ᵣ {s = i ⊔ α} I kerOfFam ⇔ 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} → IsInjective (proj₁ IsProdOfHoms)
  ∩⇔0→Inj ∩=0 = firstEquiv (thirdEquiv ∩=0)
            
{-
Proposition: Let 𝐀 an algebra and let θᵢ a congruence on 𝐀 for every i ∈ I.
If ⋂_{i ∈ I} θᵢ = 0_A then the natrual map 𝐀 → ⨅_{i∈ I} 𝐀/θᵢ is a subdirect embedding.
Conversely,  if g → 𝐀 ⨅ 𝐁ᵢ is a subdirect embedding then θᵢ = ker(pᵢ ∘ g), we have ∩θᵢ = 0_A and 𝐀/θᵢ ⋍ 𝐁ᵢ.
-}

prodQuot : ∀ {ℓ} {I : Set i} (𝐀 : Algebra α ρᵅ) (θ : I → Con 𝐀 {ℓ = ℓ}) → Algebra (α ⊔ i) (i ⊔ ℓ)
prodQuot {α = α} {ℓ = ℓ} {I = I} 𝐀 θ = ⨅ family
  where
    family : I → Algebra α ℓ 
    family  i = 𝐀 ╱ (θ i)

module _ {I : Set i} (𝐀 : Algebra α ρᵅ) (θ : I → Con 𝐀 {ρᵅ}) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car)

  -- A family of quotient algebras for the family of congruences ⟨θᵢ : i ∈ I ⟩
  famOfCons : I → Algebra α ρᵅ
  famOfCons i = 𝐀 ╱ (θ i)

  -- defining the Algebra of direct product of the family of quotient algebras
  prodOfQuot : Algebra (α ⊔ i) (i ⊔ ρᵅ)
  prodOfQuot = prodQuot {I = I} 𝐀 θ

  open Algebra prodOfQuot renaming (Domain to ⨅A/θ)
  open Setoid ⨅A/θ renaming (Carrier to pCar)

  -- defining the function natural map 𝐀 → ⨅ 𝐀／(θ i) 
  NatMap : Func A ⨅A/θ
  NatMap = record { f = λ x j → x ; cong = λ x=y j → IsCongruence.reflexive (proj₂ (θ j)) x=y }

  -- Given a family of congruences we take the binary relation of each congruence
  familyOfRels : (I → Con 𝐀 {ρᵅ}) → I → BinRel Car ρᵅ
  familyOfRels θ = λ i → proj₁ (θ i) 

  -- defining the family of homomorphisms ⟨hᵢ : 𝐀 → 𝐀／(θ i), ∀ i  ∈ I ⟩ 
  natHomMap : FamOfHoms 𝐀 famOfCons
  natHomMap = record { family = λ j → (fam j) , isHomFam j }
    where
      fam : (j : I) → Func A (𝔻[ famOfCons j ])
      fam j = record { f = λ x → x ; cong = crefl}
        where
          open IsCongruence (proj₂ (θ j)) renaming (reflexive to crefl)

      isHomFam : (j : I) → IsHom 𝐀 (famOfCons j) (fam j) 
      isHomFam j = record { compatible = λ {f} {a} → comp f λ x → congrefl}
        where
          open IsCongruence (proj₂ (θ j)) renaming ( is-compatible to comp
                                                   ; is-equivalence to equiv
                                                   )
          open IsEquivalence equiv renaming (refl to congrefl)

  open FamOfHoms natHomMap

  -- defining the product of the family of natural map homomorphisms
  prodOfNatHomMap : hom 𝐀 prodOfQuot
  prodOfNatHomMap = NatMap , record { compatible = λ j → IsHom.compatible (proj₂ (family j))}

  -- note that hᵢ : 𝐀 → 𝐀／θᵢ is surjective for each i ∈ I 
  hᵢIsSurj : ∀ (j : I) → IsSurjective (proj₁ (family j))
  hᵢIsSurj j {y} = Setoid.Functions.eq y congrefl
    where
      open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equiv)
      open IsEquivalence equiv renaming (refl to congrefl)

  -- Let pᵢ : ⨅ 𝐀／θⱼ → 𝐀 ／ θᵢ the projection of the natural map.
  -- now we want to prove that pᵢ ∘ h = hᵢ so pᵢ is surjective.
  projOfProd : ( j : I ) → Func 𝔻[ 𝐀 ] 𝔻[ famOfCons j ]
  projOfProd j = function  (proj₁ prodOfNatHomMap) (⨅-fun famOfCons j) 

  pᵢ∘h≈hᵢ : (j : I) (x : 𝕌[ 𝐀 ]) → Set ρᵅ
  pᵢ∘h≈hᵢ j x = (<$> (projOfProd j) x) ≈j (<$> (proj₁ (family j)) x)
    where
      open Algebra (famOfCons j) renaming (Domain to 𝓐j)
      open Setoid 𝓐j renaming (_≈_ to _≈j_)  
  
  -- Since hᵢ is surjective then pᵢ is surjective
  pᵢIsSurj : ∀ (j : I) → IsSurjective (⨅-fun famOfCons j)
  pᵢIsSurj j {y} = Setoid.Functions.eq (λ j → y) reflj
    where
      open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equivj)
      open IsEquivalence equivj renaming (refl to reflj)
  
  eqOfIndexes : ∀ (j : I) (x : 𝕌[ 𝐀 ]) → pᵢ∘h≈hᵢ j x
  eqOfIndexes j x = reflj
    where
      open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equivj)
      open IsEquivalence equivj renaming (refl to reflj)
  

  -- First statement of proposition 
  NatMapIsSubEmb : (⋂ᵣ {s = α ⊔ i} I (familyOfRels θ)) ⇔  0rel {𝐴 = A} {𝐵 = ⨅A/θ} {ℓ = ρᵅ} 
                 → IsSubEmb 𝐀 famOfCons  NatMap
  NatMapIsSubEmb (∩θ⇒0A , 0A⇒∩θ) = record { Mon = monOfProd
                                            ; genAlg≤Prod = ( F , record { compatible = λ j →
                                                                                      IsHom.compatible
                                                                                        (proj₂ (family j))
                                                                         }
                                                            )
                                                           , λ x j → x j
                                            ; IsSubdirProd = λ j → ⊙-IsSurjective (FisSurj j) (pᵢIsSurj j) 
                                            }
    where
      monOfProd : IsMon 𝐀 (⨅ famOfCons) NatMap
      monOfProd = record { isHom = proj₂ prodOfNatHomMap
                         ; isInjective = ∩⇔0→Inj
                                         𝐀
                                         famOfCons
                                         natHomMap
                                         ((λ xθy → ∩θ⇒0A xθy) , 0⊆∩ 𝐀 famOfCons natHomMap)
                         }


      open IsMon monOfProd 
      open Algebra (genAlgFromMon 𝐀 famOfCons (NatMap , monOfProd)) renaming (Domain to gA)

      F : Func gA ⨅A/θ
      F = record { f = λ x j → (proj₁ x) j ; cong = λ xθjy j → xθjy j }

      FisSurj : (j : I) → IsSurjective F
      FisSurj j {y} = Setoid.Functions.eq ( y
                                          , y j
                                          , λ k → {!!}
                                          )
                                          λ l →
                                            IsEquivalence.refl
                                              ( IsCongruence.is-equivalence
                                                ( proj₂ (θ l) )
                                               )

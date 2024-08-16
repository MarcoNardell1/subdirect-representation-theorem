open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.NatMapProps {𝑆 : Signature 𝓞 𝓥} where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; cong-app) renaming (cong to Scong)
open import Axiom.Extensionality.Propositional
open import Level
open import Data.Product
open import Relation.Binary using (Setoid) renaming (Rel to BinRel)
open import Relation.Nullary using (¬_)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Base.Relations using (0[_] ; ker)
open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Homomorphisms {𝑆 = 𝑆}
open import Setoid.Functions  using (IsInjective)

open import Prod.Subembedding

private variable α β ρᵅ ρᵝ i : Level

open Func renaming (f to <$>) 


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
  famSeparatePoints : (h : FamOfHoms 𝐁 𝓐) → Set (i ⊔ β ⊔ α)
  famSeparatePoints h = (x  y : 𝕌[ 𝐁 ]) → Σ[ j ∈ I ] (pred j x y) 
    where
      open FamOfHoms h
      pred : (j : I) (x y : 𝕌[ 𝐁 ]) → Set α
      pred j x y = ¬ (<$> (proj₁ (family j)) x) ≡ (<$> (proj₁ (family j)) y)   


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
  open FamOfHoms h

  kerOfFam : I → BinRel 𝕌[ 𝐁 ] α
  kerOfFam j = ker (<$> (proj₁ (family j)))

  postulate
    extensionality : Extensionality i α 
  
  {- A prod of homomorphisms h = ⨅ hᵢ, where ⟨ hᵢ : hom 𝐁 (𝓐 i) ⟩ is a family of homomorphisms,
  is such that h(b)(i) = hᵢ(b)
  -} 
  IsProdOfHoms : hom 𝐁 (⨅ 𝓐)
  IsProdOfHoms  = F , record { compatible = λ j → IsHom.compatible (proj₂ (family j))}
    where
      F : Func (𝔻[ 𝐁 ]) (𝔻[ (⨅ 𝓐) ])
      F = record { f = λ b i  → <$> (proj₁ (family i)) b  ; cong = λ {x} {y} x=y j → cong (proj₁ (family j)) x=y }


  kerOfProd→⋂kers : ∀ (a b : 𝕌[ 𝐁 ]) → (ker (<$> (proj₁ IsProdOfHoms))) a b → (⋂ᵣ {s = i ⊔ α} I kerOfFam) a b
  kerOfProd→⋂kers a b  a≈ₖb i = lift (cong-app a≈ₖb i)

  ⋂kers→kerOfProd : ∀ (a b : 𝕌[ 𝐁 ]) → (⋂ᵣ {s = i ⊔ α} I kerOfFam) a b → (ker (<$> (proj₁ IsProdOfHoms))) a b
  ⋂kers→kerOfProd a b a≈⋂b = extensionality {A = I} {B = λ j → 𝕌[ 𝓐 j ]} λ j → eq j (a≈⋂b j)
    where
      eq : (j : I) →  Lift (α ⊔ i ⊔ (i ⊔ α)) (kerOfFam j a b) → <$> (proj₁ IsProdOfHoms) a j ≡ <$> (proj₁ IsProdOfHoms) b j
      eq j (lift p) = p

  postulate
    firstEquiv : famSeparatePoints 𝐁 𝓐 h → IsInjective (proj₁ IsProdOfHoms)
    secondEquiv : IsInjective (proj₁ IsProdOfHoms) → ⋂ᵣ {s = i ⊔ β} I kerOfFam ≡ 0[ Car ] {ρ = i ⊔ α ⊔ β}
    thirdEquiv : ⋂ᵣ {s = i ⊔ β} I kerOfFam ≡ 0[ Car ] {ρ = i ⊔ α ⊔ β} → famSeparatePoints 𝐁 𝓐 h
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

module _ {ℓ} {I : Set i} (𝐀 : Algebra α ρᵅ) (θ : I → Con 𝐀 {ℓ}) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car)

  famOfCons : I → Algebra α ℓ
  famOfCons i = 𝐀 ╱ (θ i)
  
  prodOfQuot : Algebra (α ⊔ i) (i ⊔ ℓ)
  prodOfQuot = prodQuot {I = I} 𝐀 θ

  open Algebra prodOfQuot renaming (Domain to ⨅A/θ)
  open Setoid ⨅A/θ renaming (Carrier to pCar)

  NatMap : Func A ⨅A/θ
  NatMap = record { f = λ x j → x ; cong = λ x=y j → IsCongruence.reflexive (proj₂ (θ j)) x=y }

  familyOfRels : (I → Con 𝐀 {ℓ}) → I → BinRel Car ℓ
  familyOfRels θ = λ i → proj₁ (θ i) 

  -- First statement of proposition
  NatMapIsSubEmb : (⋂ᵣ {s = α ⊔ ρᵅ ⊔ ℓ} I (familyOfRels θ)) ≡ 0[ Car ] {ρ = ℓ ⊔ ρᵅ ⊔ i}
                 → IsSubEmb 𝐀 famOfCons  NatMap
  NatMapIsSubEmb p = record { Mon = {!!} ; genAlg≤Prod = {!!} ; IsSubdirProd = {!!} }

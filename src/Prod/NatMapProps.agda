open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.NatMapProps {𝑆 : Signature 𝓞 𝓥} where
open import Agda.Builtin.Equality using (_≡_)
open import Level
open import Data.Product
open import Relation.Binary using (Setoid) renaming (Rel to BinRel)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Base.Relations using (0[_])
open import Setoid.Algebras  {𝑆 = 𝑆}

open import Prod.Subembedding

private variable α β ρᵅ ρᵝ i : Level

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

  ⋂ᵣ : ∀ {i ρ s} (I : Set i) → (I → BinRel Car ρ) → BinRel Car (ρ ⊔ i ⊔ s)
  ⋂ᵣ {j} {ρ} {s} I R = λ x y → (i : I) → Lift (ρ ⊔ j ⊔ s) (R i x y)

  -- El goal 1 sale con la formalizacion de la proposicion 3.14
  -- El goal 2 sale inmediatamente del goal 1
  -- El goal 3 sale por el final de la prueba de la prop en papel
  NatMapIsSubEmb : (⋂ᵣ {s = α ⊔ ρᵅ ⊔ ℓ} I (familyOfRels θ)) ≡ 0[ Car ] {ρ = ℓ ⊔ ρᵅ ⊔ i}
                 → IsSubEmb 𝐀 famOfCons  NatMap
  NatMapIsSubEmb p = record { Mon = {!!} ; genAlg≤Prod = {!!} ; IsSubdirProd = {!!} }

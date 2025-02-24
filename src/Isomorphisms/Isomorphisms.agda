open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Isomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality  as ≡           using ()
import Relation.Binary.Reasoning.Setoid            as SReasoning  using ( begin_ ; step-≈˘; step-≈; _∎)

open import Function using (Func)


open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Functions using (IsSurjective ; IsBijective ; BijInv)
open import Setoid.Functions.Inverses using (InvIsInverseʳ)
open import Setoid.Homomorphisms {𝑆 = 𝑆} using (IsHom ; _≅_ ; hom ; mkiso ; compatible-map)


open Func renaming (f to _⟨$⟩_)
private variable α β ρᵅ ρᵝ i : Level

-- Defining Isomorphisms as a bijective homomorphism
module _ (𝐀 : Algebra α ρᵅ) (𝐁 : Algebra β ρᵝ) where
  open Algebra 𝐀 renaming (Domain to A ; Interp to AInterp)
  open Algebra 𝐁 renaming (Domain to B ; Interp to BInterp)
  open Setoid A renaming (Carrier to Acar ; _≈_ to _≈a_)
  open Setoid B renaming (Carrier to Bcar ; _≈_ to _≈b_)

  record IsIso (h : Func A B) : Set (ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ))) where
    field
      Hom : IsHom 𝐀 𝐁 h
      IsBij : IsBijective h
      
  Iso : Set ((ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ)))) 
  Iso = Σ (Func A B) IsIso

  module _ (iso : 𝐀 ≅ 𝐁) where
    open _≅_ iso
    postulate
      ≅→Iso : (h : Func A B) → ((x : Acar) → ((proj₁ to)) ⟨$⟩ x ≈b h ⟨$⟩ x) → IsIso h
      
  Iso→≅ : (h : Iso) → 𝐀 ≅ 𝐁
  Iso→≅ h = mkiso hom→ ←hom eqb eqa
    where
      open IsIso (proj₂ h)
      open IsHom Hom renaming (compatible to hcom)
      open Setoid A renaming (refl to Arefl
                             ; _≈_ to _≈ₐ_
                             ; sym to Asym
                             ; trans to Atrans
                             )
      open Setoid B renaming (refl to Brefl
                             ; sym to Bsym
                             ; trans to Btrans
                             )

      open SReasoning B renaming (begin_ to Bbegin_
                                 ; step-≈˘ to Bstep-≈˘
                                 ; step-≈ to Bstep-≈
                                 ; _∎ to _∎b
                                 )

      h⁻¹ : Func B A
      h⁻¹ = BijInv (proj₁ h) IsBij

      open Func (proj₁ h) renaming (cong to hcong)
      open Func h⁻¹ renaming (cong to invCong)

      hom→ : hom 𝐀 𝐁
      hom→ = (proj₁ h) , Hom

      eqb : ∀ (b : 𝕌[ 𝐁 ]) → (proj₁ h) ⟨$⟩ (h⁻¹ ⟨$⟩ b) ≈b b
      eqb b = InvIsInverseʳ (proj₂ IsBij)

      eqa : ∀ (a : 𝕌[ 𝐀 ]) → h⁻¹ ⟨$⟩ ((proj₁ h) ⟨$⟩ a) ≈ₐ a
      eqa a = proj₁ IsBij (eqb ((proj₁ h) ⟨$⟩ a))

      ←hom : hom 𝐁 𝐀
      ←hom = h⁻¹ , record { compatible = invIsCompatible }
        where
          invIsCompatible : compatible-map 𝐁 𝐀 h⁻¹
          invIsCompatible {f} {a} = Asym final 
            where
            {- Gracias Andres-}
              BAux : (proj₁ h) ⟨$⟩ ((f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x))) ≈b
                           (f ̂ 𝐁) (λ x → a x)
              BAux =  Bbegin
                (proj₁ h) ⟨$⟩ ((f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x))) ≈⟨ hcom ⟩
                (f ̂ 𝐁) (λ x → (proj₁ h) ⟨$⟩ (h⁻¹ ⟨$⟩ (a x))) ≈⟨ cong BInterp (≡.refl , λ i → eqb (a i)) ⟩
                (f ̂ 𝐁) (λ x → a x) ∎b 
              
              invApply : h⁻¹ ⟨$⟩ ((proj₁ h) ⟨$⟩ ((f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x)))) ≈ₐ
                           h⁻¹ ⟨$⟩ ((f ̂ 𝐁) (λ x → a x))
              invApply = invCong BAux

              final : (f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x)) ≈ₐ
                      h⁻¹ ⟨$⟩ ((f ̂ 𝐁) (λ x → a x))
              final = Asym (Atrans (Asym invApply) eqRed)
                where
                  eqRed : h⁻¹ ⟨$⟩ ((proj₁ h) ⟨$⟩ ((f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x)))) ≈ₐ
                        ((f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x)))
                  eqRed = eqa (((f ̂ 𝐀) (λ x → h⁻¹ ⟨$⟩ (a x))))
               

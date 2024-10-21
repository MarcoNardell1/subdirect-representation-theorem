open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Isomorphisms.Isomorphisms {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality  as ≡           using ()

open import Function using (Func)


open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Functions using (IsSurjective ; IsBijective ; BijInv)
open import Setoid.Functions.Inverses using (InvIsInverseʳ)
open import Setoid.Homomorphisms {𝑆 = 𝑆} using (IsHom ; _≅_ ; hom ; mkiso ; compatible-map)


open Func renaming (f to <$>)
private variable α β ρᵅ ρᵝ i : Level

-- Defining Isomorphisms as a bijective homomorphism
module _ (𝐀 : Algebra α ρᵅ) (𝐁 : Algebra β ρᵝ) where
  open Algebra 𝐀 renaming (Domain to A ; Interp to AInterp)
  open Algebra 𝐁 renaming (Domain to B ; Interp to BInterp)
  open Setoid A renaming (Carrier to Acar)
  open Setoid B renaming (Carrier to Bcar)

  record IsIso (h : Func A B) : Set (ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ))) where
    field
      Hom : IsHom 𝐀 𝐁 h
      IsBij : IsBijective h
      
  Iso : Set ((ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ)))) 
  Iso = Σ (Func A B) IsIso

  Iso→≅ : (h : Iso) → 𝐀 ≅ 𝐁
  Iso→≅ h = mkiso hom→ ←hom eqb eqa
    where
      open IsIso (proj₂ h)
      open IsHom Hom renaming (compatible to hcom)
      open Setoid A renaming (refl to refla; _≈_ to _≈ₐ_ ; sym to syma ; trans to transa)
      open Setoid B renaming (refl to reflb; _≈_ to _≈b_ ; sym to symb ; trans to transb)
    
      h⁻¹ : Func B A
      h⁻¹ = BijInv (proj₁ h) IsBij

      open Func (proj₁ h) renaming (cong to hcong)
      open Func h⁻¹ renaming (cong to invCong)

      hom→ : hom 𝐀 𝐁
      hom→ = (proj₁ h) , Hom

      eqb : ∀ (b : 𝕌[ 𝐁 ]) → <$> (proj₁ h) (<$> h⁻¹ b) ≈b b
      eqb b = InvIsInverseʳ (proj₂ IsBij)

      eqa : ∀ (a : 𝕌[ 𝐀 ]) → <$> h⁻¹ (<$> (proj₁ h) a) ≈ₐ a
      eqa a = proj₁ IsBij (eqb (<$> (proj₁ h) a))

      eqATrans : ∀ {x y : 𝕌[ 𝐀 ]}
               → x ≈ₐ y
               → <$> h⁻¹ (<$> (proj₁ h) x) ≈ₐ <$> h⁻¹ (<$> (proj₁ h) y)
      eqATrans {x} {y} xy = transa (eqa x) (transa xy (syma (eqa y)))
      

      eqBTrans : ∀ {x y : 𝕌[ 𝐁 ]}
               → x ≈b y
               → <$> (proj₁ h) (<$> h⁻¹ x) ≈b <$> (proj₁ h) (<$> h⁻¹ y)
      eqBTrans {x} {y} xy = transb (eqb x) (transb xy (symb (eqb y)))
      
      ←hom : hom 𝐁 𝐀
      ←hom = h⁻¹ , record { compatible = invIsCompatible }
        where
          invIsCompatible : compatible-map 𝐁 𝐀 h⁻¹
          invIsCompatible {f} {a} = syma final 
            where
            {- Gracias Andres-}
              firstEquiv : <$> (proj₁ h) ((f ̂ 𝐀) (λ x → <$> h⁻¹ (a x))) ≈b
                           ((f ̂ 𝐁) (λ x → <$> (proj₁ h) (<$> h⁻¹ (a x))))
              firstEquiv = hcom

              secondEquiv : ((f ̂ 𝐁) (λ x → <$> (proj₁ h) (<$> h⁻¹ (a x)))) ≈b
                            (f ̂ 𝐁) (λ x → a x)
              secondEquiv = cong BInterp (≡.refl , λ i → eqb (a i)) 

              thirdEquiv : <$> (proj₁ h) ((f ̂ 𝐀) (λ x → <$> h⁻¹ (a x))) ≈b
                           (f ̂ 𝐁) (λ x → a x)

              thirdEquiv = transb firstEquiv secondEquiv
              
              fourthEquiv : <$> h⁻¹ (<$> (proj₁ h) ((f ̂ 𝐀) (λ x → <$> h⁻¹ (a x)))) ≈ₐ
                           <$> h⁻¹ ((f ̂ 𝐁) (λ x → a x))
              fourthEquiv = invCong thirdEquiv


              final : (f ̂ 𝐀) (λ x → <$> h⁻¹ (a x)) ≈ₐ
                      <$> h⁻¹ ((f ̂ 𝐁) (λ x → a x))
              final = syma (transa (syma fourthEquiv) eqRed)
                where
                  eqRed : <$> h⁻¹ (<$> (proj₁ h) ((f ̂ 𝐀) (λ x → <$> h⁻¹ (a x)))) ≈ₐ
                        ((f ̂ 𝐀) (λ x → <$> h⁻¹ (a x)))
                  eqRed = eqa (((f ̂ 𝐀) (λ x → <$> h⁻¹ (a x))))
               

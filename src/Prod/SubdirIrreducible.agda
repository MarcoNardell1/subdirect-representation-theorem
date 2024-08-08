open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.SubdirIrreducible {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Functions using (IsBijective ; BijInv)
open import Setoid.Homomorphisms {𝑆 = 𝑆} using (IsHom)

open import Prod.Subdirect
open import Prod.Subembedding

private variable α β ρᵅ ρᵝ i : Level

-- Defining Isomorphisms as a bijective homomorphism
module _ (𝐀 : Algebra α ρᵅ) (𝐁 : Algebra β ρᵝ) where
  open Algebra 𝐀 renaming (Domain to A)
  open Algebra 𝐁 renaming (Domain to B)

  record IsIso (h : Func A B) : Set (ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ))) where
    field
      Hom : IsHom 𝐀 𝐁 h
      IsBij : IsBijective h
      
  Iso : Set ((ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ)))) 
  Iso = Σ (Func A B) IsIso
{-
  Iso→≅ : (h : Iso) → 𝐀 ≅ 𝐁
  Iso→≅ h = mkiso hom→ ←hom (λ b → {!!}) {!!}
    where
      open IsIso (proj₂ h)
      open IsHom Hom
      open Setoid A renaming (refl to refla; _≈_ to _≈ₐ_)
      open Setoid B renaming (refl to reflb; _≈_ to _≈b_)

      h⁻¹ : Func B A
      h⁻¹ = BijInv (proj₁ h) IsBij
 
      hom→ : hom 𝐀 𝐁
      hom→ = (proj₁ h) , Hom

      ←hom : hom 𝐁 𝐀
      ←hom = h⁻¹ , record { compatible = λ {f} {a} → {!!} } 
     
      eqb : ∀ (a : 𝕌[ 𝐀 ]) → <$> h⁻¹ (<$> (proj₁ h) a) ≈ₐ a
      eqb a = {!!}
-}

{-
IsIso : (Hom A B) → Set
IsIso h = Σ[ i ∈ Iso A B ] (ext-eq h (from i))
  where ext-eq : (f g : Hom A B) → Set
        ext-eq f g = (∀ a : D[ A ]) → f a ≈ g a
-}
-- Definition of subdirectly irreducible
{-
  A nontrivial algebra 𝐀 is called subdirectly irreducible
  if for every subdirect embedding h : 𝐀 → ⨅_{i∈ I} 𝐀ᵢ,
  there is a j ∈ I such that pⱼ ∘ h : 𝐀 → 𝐀ⱼ is an isomorphism. 
-}

IsSubIrreducible : ∀ {I : Set i} (𝐀 : Algebra α ρᵅ) (𝓐 : I → Algebra α ρᵅ)
                 → ∀ (h : SubdirectEmbedding 𝐀 𝓐)
                 → Set (i ⊔ (ov (α ⊔ ρᵅ)))
IsSubIrreducible {I = I} 𝐀 𝓐 h = Σ[ j ∈ I ] IsIso 𝐀 (𝓐 j) (function (proj₁ h) (⨅-fun 𝓐 j))   

record SubdirectlyIrreducible : Set (ov (i ⊔ α ⊔ ρᵅ)) where
  field
    ix : Set i
    base : Algebra α ρᵅ
    family : ix → Algebra α ρᵅ
    subEmbs : SubdirectEmbedding base family
    isSubIrr : IsSubIrreducible base family subEmbs

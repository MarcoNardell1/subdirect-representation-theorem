open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.Subdirect {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Subalgebras.Subalgebras {𝑆 = 𝑆} 
open import Setoid.Functions using (IsSurjective)

private variable α β ρᵅ ρᵝ i : Level

-- Projections of a product
module _ {I : Set i} (𝓐 : I → Algebra α ρᵅ) where
    ⨅-fun : (j : I) → Func (𝔻[ ⨅ 𝓐 ]) (𝔻[ 𝓐 j ])
    ⨅-fun j = record { f = λ x →  x j ; cong = λ a=b → a=b j }

-- Type of SubdirectProduct
{-
  An algebra 𝐁 is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩ if 𝐁 is
  a subalgebra of ⨅_(i ∈ I) 𝐀ᵢ, and for every j ∈ I, pⱼ|B : 𝐁 → 𝐀ᵢ is surjective. 
-}
IsSubdirectProduct : ∀ {I : Set i}
                   (𝐁 : Algebra β ρᵝ)
                   (𝓐 : I → Algebra α ρᵅ)
                   → 𝐁 ≤ (⨅ 𝓐)
                   → Set (i ⊔ β ⊔ α ⊔ ρᵅ) 
IsSubdirectProduct 𝐁 𝓐 𝐁≤𝓐 = ∀ j →  IsSurjective (g j)
  where
    
    g : ∀ j → Func (𝔻[ 𝐁 ]) (𝔻[ 𝓐 j ])
    g j = function (proj₁ (proj₁ 𝐁≤𝓐)) (⨅-fun 𝓐 j)


record SubdirectProduct : Set (ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ))
  where
  field
      ix : Set i
      family :  ix → Algebra α ρᵅ
      subalg : Algebra β ρᵝ
      isSubAlg : subalg ≤ ⨅ family 
      isSubdirProd : IsSubdirectProduct {I = ix} subalg family isSubAlg 

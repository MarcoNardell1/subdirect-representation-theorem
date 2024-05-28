open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod {𝑆 : Signature 𝓞 𝓥} where 
open import Level
open import Data.Product
open import Function using (_∘_)

open import Base.Algebras  {𝑆 = 𝑆}
open import Base.Subalgebras.Subalgebras {𝑆 = 𝑆} 
open import Base.Functions using (IsSurjective)

private variable α β i : Level


-- Type of SubdirectProduct
{-
  An algebra 𝐁 is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩ if 𝐁 is
  a subalgebra of ⨅_(i ∈ I) 𝐀ᵢ, and for every j ∈ I, pⱼ|B : 𝐁 → 𝐀ᵢ is surjective. 
-}

IsSubdirectProduct : ∀ {I : Set i} (𝐁 : Algebra β) (𝓐 : I → Algebra α) → 𝐁 ≤ (⨅ 𝓐) → Set (i ⊔ β ⊔ α)
IsSubdirectProduct {I = I} 𝐁 𝓐 𝐁≤𝓐 = (j : I) → IsSurjective (f j)
  where
    f : (j : I) → ∣ 𝐁 ∣ → ∣ 𝓐 j ∣
    f j  b = ((proj₁ ( proj₁ 𝐁≤𝓐)) b) j 

record SubdirectProduct : Set (ov (i ⊔ α ⊔ β)) -- Set ( ov (𝓞 ⊔ 𝓥 ⊔ i ⊔ suc α))
  where
  field
      ix : Set i
      alg :  ix → Algebra α
      subalg : Algebra β
      isSubAlg : subalg ≤ ⨅ alg 
      isSubdirProd : IsSubdirectProduct {I = ix} subalg alg isSubAlg 
open SubdirectProduct

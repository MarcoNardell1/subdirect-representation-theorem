open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod {𝑆 : Signature 𝓞 𝓥} where 
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (_∘_ ; Func)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Subalgebras.Subalgebras {𝑆 = 𝑆} 
open import Setoid.Functions using (isSurj)
open import Setoid.Homomorphisms

private variable α β ρᵅ ρᵝ i : Level


-- Type of SubdirectProduct
{-
  An algebra 𝐁 is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩ if 𝐁 is
  a subalgebra of ⨅_(i ∈ I) 𝐀ᵢ, and for every j ∈ I, pⱼ|B : 𝐁 → 𝐀ᵢ is surjective. 
-}

IsSubdirectProduct : ∀ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ)
                   → 𝐁 ≤ (⨅ 𝓐)
                   → Set (i ⊔ β ⊔ ρᵝ ⊔ α ⊔ ρᵅ)
IsSubdirectProduct {I = I} 𝐁 𝓐 𝐁≤𝓐 = (j : I) → isSurj (f j)
  where
    open Func (proj₁ (proj₁ 𝐁≤𝓐)) renaming (f to projⱼ)

    f : (j : I) → 𝕌[ 𝐁 ] → 𝕌[ 𝓐 j ]
    f j  b = projⱼ b j

record SubdirectProduct : Set (ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ))
  where
  field
      ix : Set i
      alg :  ix → Algebra α ρᵅ
      subalg : Algebra β ρᵝ
      isSubAlg : subalg ≤ ⨅ alg 
      isSubdirProd : IsSubdirectProduct {I = ix} subalg alg isSubAlg 
open SubdirectProduct


-- Subdirect embeddings
{-
  An embedding g : 𝐁 → ⨅ 𝐀ᵢ is called subdirect if DirImage(g(𝐁)) is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩.
  g is also called the subdirect representation of 𝐁
-}

record SubdirectEmbedding : Set (ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ))
  where
  field
    ix : Set i
    family : ix → Algebra α ρᵅ
    base : Algebra β ρᵝ
    rep : mon base (⨅ family) -- A monomorphism is a embedding (An injective homomorphism)
{-
  TODO:
  - definir la imagen directa de una funcion, f : A → B
  DirImage(f) : Sb (A) → Sb (B)
  DirImage(f) X = {f(x) : x ∈ X}
  - Lema de imagen directa de un homomorfismo
-}
--    isSubdirProd : IsSubdirectProduct {I = ix} 


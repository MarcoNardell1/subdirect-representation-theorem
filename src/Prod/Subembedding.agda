open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.Subembedding {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (Func)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Subalgebras.Subalgebras {𝑆 = 𝑆} 
open import Setoid.Homomorphisms {𝑆 = 𝑆}

open import Prod.Subdirect

private variable α β ρᵅ ρᵝ i : Level

-- Subdirect embeddings
{-
  An embedding g : 𝐁 → ⨅ 𝐀ᵢ is called subdirect if DirImage(g(𝐁)) is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩.
  g is also called the subdirect representation of 𝐁
-}

module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) where 
   open Algebra 𝐁 renaming (Domain to B)
   open Algebra (⨅ 𝓐) renaming (Domain to A)

   genAlgFromMon : (h : mon 𝐁 (⨅ 𝓐)) → Algebra (β ⊔ (α ⊔ i) ⊔ (ρᵅ ⊔ i)) (ρᵅ ⊔ i)
   genAlgFromMon h = HomImageOf[ mon→hom 𝐁 (⨅ 𝓐) h ]
       
   record IsSubEmb (h : Func B A) : Set (ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ))  where
     field
       Mon : IsMon 𝐁 (⨅ 𝓐) h
       genAlg≤Prod : (genAlgFromMon (h , Mon)) ≤ (⨅ 𝓐) 
       isSubdirProd : IsSubdirectProduct (genAlgFromMon (h , Mon)) 𝓐 genAlg≤Prod
     
   SubdirectEmbedding : Set ((ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ)))
   SubdirectEmbedding = Σ (Func B A) IsSubEmb


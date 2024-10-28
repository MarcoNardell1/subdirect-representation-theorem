open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.Subembedding {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Function using (Func)

open import Setoid.Functions using (IsInjective)
open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Subalgebras.Subalgebras {𝑆 = 𝑆}
open import Setoid.Homomorphisms {𝑆 = 𝑆}

open import Prod.Subdirect

open Func renaming (f to  _<$>_)
private variable α β ρᵅ ρᵝ i : Level

-- Subdirect embeddings
{-
  An embedding g : 𝐁 → ⨅ 𝐀ᵢ is called subdirect if DirImage(g(𝐁)) is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩.
  g is also called the subdirect representation of 𝐁
-}

module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) where 
   open Algebra 𝐁 renaming (Domain to B)
   open Algebra (⨅ 𝓐) renaming (Domain to A)
   open Setoid A renaming (_≈_ to _≈a_ ; refl to arefl)

   genAlgFromMon : (h : mon 𝐁 (⨅ 𝓐)) → Algebra (β ⊔ (α ⊔ i) ⊔ (ρᵅ ⊔ i)) (ρᵅ ⊔ i)
   genAlgFromMon h = HomImageOf[ mon→hom 𝐁 (⨅ 𝓐) h ]

   subAlg : (h : mon 𝐁 (⨅ 𝓐)) → (genAlgFromMon h) ≤ (⨅ 𝓐)
   subAlg h = ( F , homF) , λ x≈y j → x≈y j 
     where
      F : Func 𝔻[ genAlgFromMon h ] A
      F = record { f = λ x j → (proj₁ x) j
                 ; cong = λ xj≈yj j → xj≈yj j
                 }

      open IsHom
      
      homF : IsHom (genAlgFromMon h) (⨅ 𝓐) F
      compatible homF j = ajrefl
        where
          open Algebra (𝓐 j) renaming (Domain to Aj)
          open Setoid Aj renaming (refl to ajrefl)
      
   record IsSubEmb (h : Func B A) : Set (ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ))  where
     field
       Mon : IsMon 𝐁 (⨅ 𝓐) h 
       isSubdirProd : IsSubdirectProduct (genAlgFromMon (h , Mon)) 𝓐 (subAlg (h , Mon))
       
     genAlg≤Prod : (genAlgFromMon (h , Mon)) ≤ (⨅ 𝓐)
     genAlg≤Prod = subAlg (h , Mon)

   SubdirectEmbedding : Set ((ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ)))
   SubdirectEmbedding = Σ (Func B A) IsSubEmb


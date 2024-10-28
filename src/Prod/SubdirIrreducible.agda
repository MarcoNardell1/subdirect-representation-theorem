open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.SubdirIrreducible {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Functions using (IsBijective ; BijInv)
open import Setoid.Homomorphisms {𝑆 = 𝑆} using (IsHom ; _≅_ ; hom ; mkiso)

open import Prod.Subdirect
open import Prod.Subembedding
open import Isomorphisms.Isomorphisms

open Func renaming (f to <$>)
private variable α β ρᵅ ρᵝ i : Level

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

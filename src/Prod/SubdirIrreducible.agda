open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Prod.SubdirIrreducible {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Setoid.Algebras  {𝑆 = 𝑆}

open import Prod.Subdirect
open import Prod.Subembedding
open import Isomorphisms.Isomorphisms
open import Structures.Algebras {𝑆 = 𝑆}

open Func renaming (f to <$>)
private variable α ρᵅ i : Level

-- Definition of subdirectly irreducible
{-
  A nontrivial algebra 𝐀 is called subdirectly irreducible
  if for every subdirect embedding h : 𝐀 → ⨅_{i∈ I} 𝐀ᵢ,
  there is a j ∈ I such that pⱼ ∘ h : 𝐀 → 𝐀ⱼ is an isomorphism. 
-}

module _  (n𝐀 : NonTrivialAlgebra {β = α} {ρ = ρᵅ}) where

  𝐀 : Algebra α ρᵅ
  𝐀 = proj₁ n𝐀
  
  IsSubIrreducible : ∀ {i} → Set (ov (i ⊔ α ⊔ ρᵅ))
  IsSubIrreducible {i} = {I : Set i} (𝓐 : I → Algebra α ρᵅ) → (h : SubdirectEmbedding 𝐀 𝓐)
                    → Σ[ j ∈ I ]  IsIso 𝐀 (𝓐 j) (function (proj₁ h) (⨅-fun 𝓐 j))
      

record SubdirectlyIrreducible : Set (ov (i ⊔ α ⊔ ρᵅ)) where
  field
    base : NonTrivialAlgebra {β = α} {ρ = ρᵅ}
    isSubIrr : IsSubIrreducible base {i}


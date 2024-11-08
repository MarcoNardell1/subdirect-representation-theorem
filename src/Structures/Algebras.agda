open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Structures.Algebras {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred) 
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Setoid.Algebras {𝑆 = 𝑆}

{-
A trivial Algebra 𝐀 is the one who has only one element in its universe.
We assert that a Carrier has only one element if ∀ x y ∈ Car, x ≈ y.
An algebra is nontrivial if it isn't trivial.
-}

IsTrivialAlgebra : ∀ {α ρ} (𝐀 : Algebra α ρ) → Set(α ⊔ ρ)
IsTrivialAlgebra 𝐀 =  (x y : 𝕌[ 𝐀 ]) → x ≈ y
  where
    open Algebra 𝐀 renaming (Domain to A)
    open Setoid A

IsNonTrivialAlgebra : ∀ {α ρ} (𝐀 : Algebra α ρ) → Set (α ⊔ ρ)
IsNonTrivialAlgebra 𝐀 = (x y : 𝕌[ 𝐀 ]) → ¬ (x ≈ y)
  where
    open Algebra 𝐀 renaming (Domain to A)
    open Setoid A

TrivialAlgebra : ∀ {β ρ} → Set (ov (β ⊔ ρ))
TrivialAlgebra {β} {ρ} = Σ (Algebra β ρ) IsTrivialAlgebra

NonTrivialAlgebra : ∀ {β ρ} →  Set (ov (β ⊔ ρ))
NonTrivialAlgebra {β} {ρ} = Σ (Algebra β ρ) IsNonTrivialAlgebra

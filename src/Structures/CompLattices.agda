open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Structures.CompLattices {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Unary using (Pred) 
open import Relation.Binary using (Setoid ; Poset ; Rel ; IsPartialOrder ; _⇔_ ; _⇒_ ; IsPreorder ; IsEquivalence)
open import Function using (Func)

open import Setoid.Algebras  {𝑆 = 𝑆} hiding (mkcon)
open import Setoid.Algebras.Congruences {𝑆 = 𝑆} using (mkcon)

open import Poset

private variable α ρᵅ : Level
{-
In this module we will work on the corollary that defines the complete lattice of congruences ordered by inclusion.
Firstly, we will define the Poset of congruences ordered by inclusion. So this is ⟨Con 𝐀 , ⊆⟩ where given two congruences θ ϕ, θ ⊆ ϕ is, ∀ x y ∈ A, x θ y ⇒ x ϕ y.
For checking that the poset of congruences is a complete lattice, we need to check that the arbitray intersection is the infimum operation for this Poset, after that for 2.14 ⟨Con 𝐀 , ⊆⟩ is a complete lattice.  
-}
module _ (𝐀 : Algebra α ρᵅ) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car)

  _≈c_ : Rel (Con 𝐀 {ρᵅ}) (α ⊔ ρᵅ)
  θᵢ ≈c θⱼ = proj₁ θᵢ ⇔ proj₁ θⱼ

  _⊆c_ : Rel (Con 𝐀 {ρᵅ}) (α ⊔ ρᵅ)
  θᵢ ⊆c θⱼ = proj₁ θᵢ ⇒ proj₁ θⱼ

  ≈-isEquiv : IsEquivalence _≈c_
  ≈-isEquiv = record { refl = (λ xθy → xθy) , λ xθy → xθy
                     ; sym = λ θ=ϕ → proj₂ θ=ϕ , proj₁ θ=ϕ
                     ; trans = λ θ=ϕ ϕ=ψ → ( λ xθy → proj₁ ϕ=ψ (proj₁ θ=ϕ xθy) )
                                            , λ xψy → proj₂ θ=ϕ (proj₂ ϕ=ψ xψy)
                     }

  ⊆-isPreorder : IsPreorder _≈c_ _⊆c_
  ⊆-isPreorder = record { isEquivalence = ≈-isEquiv
                        ; reflexive = λ θ=ϕ xθy → proj₁ θ=ϕ xθy
                        ; trans = λ θ⊆ϕ ϕ⊆ψ xθy → ϕ⊆ψ (θ⊆ϕ xθy)
                        }

  ⊆-isPartialOrder : IsPartialOrder _≈c_ _⊆c_
  ⊆-isPartialOrder = record { isPreorder = ⊆-isPreorder
                            ; antisym = λ θ⊆ϕ ϕ⊆θ → θ⊆ϕ , ϕ⊆θ
                            }
  
  PosetOfCong : Poset (α ⊔ (ov (ρᵅ))) (α ⊔ ρᵅ) (α ⊔ ρᵅ)
  PosetOfCong  = record { Carrier = Con 𝐀 {ρᵅ}
                        ; _≈_ = _≈c_
                        ; _≤_ = _⊆c_
                        ; isPartialOrder = ⊆-isPartialOrder
                        }

  

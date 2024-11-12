open import Overture using ( 𝓞 ; 𝓥 ; Signature)

module Structures.CompLattices {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Unary using (Pred) 
open import Relation.Binary using (Setoid ; Poset ; Rel ; IsPartialOrder ; _⇔_ ; _⇒_ ; IsPreorder ; IsEquivalence)
open import Function using (Func)

open import Setoid.Algebras {𝑆 = 𝑆} hiding (mkcon ; Con ; _∣≈_)
open import Setoid.Algebras.Congruences {𝑆 = 𝑆} using (mkcon ; Con ; _∣≈_)

open import Poset as P
open import Utils.Definitions

private variable α ρᵅ : Level
{-
In this module we will work on the corollary that defines the complete lattice of congruences ordered by inclusion.
Firstly, we will define the Poset of congruences ordered by inclusion. So this is ⟨Con 𝐀 , ⊆⟩ where given two congruences θ ϕ, θ ⊆ ϕ is, ∀ x y ∈ A, x θ y ⇒ x ϕ y.
For checking that the poset of congruences is a complete lattice, we need to check that the arbitray intersection is the infimum operation for this Poset, after that for 2.14 ⟨Con 𝐀 , ⊆⟩ is a complete lattice.  
-}
module _ {i} (I : Set i) (𝐀 : Algebra α ρᵅ) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car ; _≈_ to _≈ₐ_)

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

  open Poset PosetOfCong renaming (_≤_ to _≤c_)
  
  -- The meet operation of the Lattice of Congruences is the arbitrary intersection. 
  ⋀c_ : ∀ {ℓ} → Pred (Con 𝐀 {ℓ}) ℓ → Con 𝐀 {α ⊔ ρᵅ ⊔ (ov ℓ) ⊔ ℓ} -- Op (Con 𝐀 {ρᵅ}) {α ⊔ ρᵅ}
  ⋀c_ {ℓ} X =  _∼_ , ∼Cong
    where
      _∼_ : Rel 𝕌[ 𝐀 ] (α ⊔ ρᵅ ⊔ (ov ℓ))
      x ∼ y = (R : Con 𝐀 {ℓ}) → X R → proj₁ R x y

      x≈y→x∼y : {x y :  𝕌[ 𝐀 ]} → x ≈ₐ y → x ∼ y
      x≈y→x∼y x=y R R∈X = Rreflexive x=y
        where
          open IsCongruence (proj₂ R) renaming (reflexive to Rreflexive) 

      ∼refl : ∀ {x : 𝕌[ 𝐀 ]} → x ∼ x
      ∼refl R R∈X = Rrefl
        where
          open IsCongruence (proj₂ R) renaming (is-equivalence to equiv)
          open IsEquivalence equiv renaming (refl to Rrefl)

      ∼sym : ∀ {x y : 𝕌[ 𝐀 ]} → x ∼ y → y ∼ x
      ∼sym x∼y R R∈X = Rsym (x∼y R R∈X)
        where
          open IsCongruence (proj₂ R) renaming (is-equivalence to equiv)
          open IsEquivalence equiv renaming (sym to Rsym)

      ∼trans : ∀ {x y z : 𝕌[ 𝐀 ]} → x ∼ y → y ∼ z → x ∼ z
      ∼trans x∼y y∼z R R∈X = Rtrans (x∼y R R∈X) (y∼z R R∈X)
        where
          open IsCongruence (proj₂ R) renaming (is-equivalence to equiv)
          open IsEquivalence equiv renaming (trans to Rtrans)


      ∼IsEquiv : IsEquivalence _∼_
      ∼IsEquiv = record { refl = ∼refl
                        ; sym = ∼sym
                        ; trans = ∼trans
                        }

      ∼isCompatible : 𝐀 ∣≈ _∼_
      ∼isCompatible 𝑓 evRel∼ R R∈X = comp 𝑓 (λ i → evRel∼ i R R∈X)
        where
          open IsCongruence (proj₂ R) renaming (is-compatible to comp)
      
      ∼Cong : IsCongruence 𝐀 _∼_
      ∼Cong = record { reflexive = x≈y→x∼y
                     ; is-equivalence = ∼IsEquiv
                     ; is-compatible = ∼isCompatible
                     }

   

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
module _ (𝐀 : Algebra α ρᵅ) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car ; _≈_ to _≈ₐ_)

  _≈c_ : Rel (Con 𝐀 {ρᵅ}) (α ⊔ ρᵅ)
  θᵢ ≈c θⱼ = proj₁ θᵢ ⇔ proj₁ θⱼ

  _⊆c_ : Rel (Con 𝐀 {ρᵅ}) (α ⊔ ρᵅ)
  θᵢ ⊆c θⱼ = proj₁ θᵢ ⇒ proj₁ θⱼ

  ≈-isEquiv : IsEquivalence _≈c_
  ≈-isEquiv = record { refl = ((λ xθy → xθy) , λ xθy → xθy)
                     ; sym = λ θ=ϕ → (proj₂ θ=ϕ , proj₁ θ=ϕ)
                     ; trans = λ θ=ϕ ϕ=ψ → ( ( λ xθy → proj₁ ϕ=ψ (proj₁ θ=ϕ xθy))
                                            , λ xψy → proj₂  θ=ϕ (proj₂ ϕ=ψ xψy)
                                            ) 
                     }

  ⊆-isPreorder : IsPreorder _≈c_ _⊆c_
  ⊆-isPreorder = record { isEquivalence = ≈-isEquiv
                        ; reflexive = λ θ=ϕ → λ xθy → proj₁  θ=ϕ xθy
                        ; trans = λ θ⊆ϕ ϕ⊆ψ → λ xθy → ϕ⊆ψ (θ⊆ϕ xθy)
                        }

  ⊆-isPartialOrder : IsPartialOrder _≈c_ _⊆c_
  ⊆-isPartialOrder = record { isPreorder = ⊆-isPreorder
                            ; antisym = λ θ⊆ϕ ϕ⊆θ → (θ⊆ϕ , ϕ⊆θ)
                            }

  PosetOfCong : Poset (α ⊔ ov (ρᵅ)) (α ⊔ ρᵅ) (α ⊔ ρᵅ)
  PosetOfCong  = record { Carrier = Con 𝐀 {ρᵅ}
                        ; _≈_ = _≈c_
                        ; _≤_ = _⊆c_
                        ; isPartialOrder = ⊆-isPartialOrder
                        }

  open Poset PosetOfCong renaming ( _≤_ to _≤c_
                                  ; Carrier to Cg
                                  )
  
  -- The meet operation of the Lattice of Congruences is the arbitrary intersection. 
  ⋀c : Pred (Con 𝐀 {ρᵅ}) (α ⊔ (ov ρᵅ)) → Con 𝐀 {α ⊔ (ov ρᵅ)}
  ⋀c  Θ = _∩[Θ]_ , ∩ΘCong
    where
      -- Defining the relation of intersection of Congruences
      _∩[Θ]_ : Rel 𝕌[ 𝐀 ] (α ⊔ (ov ρᵅ))
      x ∩[Θ] y = (R : Con 𝐀 {ρᵅ}) → Θ R → proj₁ R x y

      -- Proving that the intersection of congruences is a congruence
      x≈y→x∩Θy : {x y :  𝕌[ 𝐀 ]} → x ≈ₐ y → x ∩[Θ] y
      x≈y→x∩Θy x=y R _ = Rreflexive x=y
        where
          open IsCongruence (proj₂ R) renaming (reflexive to Rreflexive) 

      ∩Θrefl : ∀ {x : 𝕌[ 𝐀 ]} → x ∩[Θ] x
      ∩Θrefl R R∈X = Rrefl
        where
          open IsCongruence (proj₂ R) renaming (is-equivalence to equiv)
          open IsEquivalence equiv renaming (refl to Rrefl)

      ∩Θsym : ∀ {x y : 𝕌[ 𝐀 ]} → x ∩[Θ] y → y ∩[Θ] x
      ∩Θsym x∩Θy R R∈X = Rsym (x∩Θy R R∈X)
        where
          open IsCongruence (proj₂ R) renaming (is-equivalence to equiv)
          open IsEquivalence equiv renaming (sym to Rsym)

      ∩Θtrans : ∀ {x y z : 𝕌[ 𝐀 ]} → x ∩[Θ] y → y ∩[Θ] z → x ∩[Θ] z
      ∩Θtrans x∩Θy y∩Θz R R∈X = Rtrans (x∩Θy R R∈X) (y∩Θz R R∈X)
        where
          open IsCongruence (proj₂ R) renaming (is-equivalence to equiv)
          open IsEquivalence equiv renaming (trans to Rtrans)


      ∩ΘIsEquiv : IsEquivalence _∩[Θ]_
      ∩ΘIsEquiv = record { refl = ∩Θrefl
                        ; sym = ∩Θsym
                        ; trans = ∩Θtrans
                        }

      ∩ΘisCompatible : 𝐀 ∣≈ _∩[Θ]_
      ∩ΘisCompatible 𝑓 evRel∼ R R∈X = comp 𝑓 (λ i → evRel∼ i R R∈X)
        where
          open IsCongruence (proj₂ R) renaming (is-compatible to comp)
      
      ∩ΘCong : IsCongruence 𝐀 _∩[Θ]_
      ∩ΘCong = record { reflexive = x≈y→x∩Θy
                     ; is-equivalence = ∩ΘIsEquiv
                     ; is-compatible = ∩ΘisCompatible
                     }


  -- Postulating the existence of the complete lattice of congruences
{-
  No podemos definir InfExists para todo subconjunto de X dado que X esta en un nivel mas alto que las relaciones binarias.
  Por lo que seria necesario liftear todas las operaciones para poder trabajar con dichos niveles. 
-}
  -- Proving that ⋀c is a lower bound for every subset of congruences
  InfIsLowerBound : (X : Pred (Con 𝐀 { ρᵅ}) (α ⊔ (ov ρᵅ)))
                  → ∀ (R : Con 𝐀 {ρᵅ})
                  → X R
                  → ∀ {x y : Car} → (proj₁ (⋀c X)) x y → (proj₁ R) x y 
  InfIsLowerBound _ R R∈X ∩X = ∩X R R∈X

  InfIsGreatLB : (X : Pred (Con 𝐀 {ρᵅ}) (α ⊔ (ov ρᵅ)))
               → ∀ (ϕ : Con 𝐀 {ρᵅ})
               → IsLowerBound _≤c_ X ϕ
               → ∀ {x y : Car} → (proj₁ ϕ) x y 
               → (proj₁ (⋀c X)) x y    
  InfIsGreatLB X ϕ LB xϕy R R∈X = (LB R R∈X) xϕy

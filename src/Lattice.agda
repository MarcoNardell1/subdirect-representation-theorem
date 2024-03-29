module Lattice where

-- Standard library imports
open import Relation.Binary.Lattice using (Lattice ; Infimum ; Supremum ; IsLattice)
open import Relation.Binary         using (Rel ; IsPartialOrder)
open import Level                   using (Level ; _⊔_ ; suc)
open import Relation.Unary          using (Pred ; _⊆_ ; _∈_)
open import Data.Product
open import Data.Sum
open import Algebra.Core            using (Op₂)

-- Local imports
open import Poset                         

{-
  Lemma: 
  Let 𝐋 be a Complete Lattice , then 𝐋 is a lattice.
  Proof: 
  Let 𝐋 be an arbitrary complete lattice, by assumption for every X ⊆ L exists ⋁ X and ⋀ X.
  Then let X = {x , y} be a subset of L. Since X ⊆ L, ⋁ X = sup X = sup {x, y} = x ∨ y.
  Identically, ⋀ X = inf X = inf {x , y} = x ∧ y.
  ∎ 
-}
 
CompleteLatticeIsLattice : ∀ {c ℓ₁ ℓ₂} → CompleteLattice c ℓ₁ ℓ₂ ℓ₁ ℓ₁ → Lattice c ℓ₁ ℓ₂
CompleteLatticeIsLattice CL = record { Carrier = Carrier
                                       ; _≈_ = _≈_
                                       ; _≤_ = _≤_
                                       ; _∨_ = _∨_
                                       ; _∧_ = _∧_
                                       ; isLattice = isLattice
                                       }

  where
    open CompleteLattice CL
    -- utils
    subsetTwoElems : {x y : Carrier} → Pred (Carrier) _   
    subsetTwoElems {x} {y} z = (x ≈ z) ⊎ (y ≈ z)

    eqReflPoset = (IsPartialOrder.Eq.refl (isPartialOrder isCompleteLattice))
   
    -- binary operations
    _∨_ : Op₂ (Carrier)
    _∨_ = λ x y → ⋁ (subsetTwoElems {x} {y})

    _∧_ : Op₂ (Carrier)
    _∧_ = λ x y → ⋀ (subsetTwoElems {x} {y})

    -- proof of _∨_ is supremum
    supTwoElems : {x y : Carrier} → IsSupremum _≤_ subsetTwoElems (⋁ subsetTwoElems)
    supTwoElems {x} {y} = isSupremum isCompleteLattice (subsetTwoElems {x} {y})
 
    x≤x∨y :{x y : Carrier} →  x ≤ (x ∨ y)
    x≤x∨y {x} {y} =  (proj₁ (supTwoElems {x} {y})) x (inj₁ eqReflPoset)

    y≤x∨y : {x y : Carrier} → y ≤ (x ∨ y)
    y≤x∨y {x} {y} = (proj₁ (supTwoElems {x} {y})) y (inj₂ eqReflPoset)

    lUpperbound : {x y : Carrier} (z : Carrier) → x ≤ z → y ≤ z
                → IsUpperBound _≤_ (subsetTwoElems {x} {y}) z
    lUpperbound {x} {y} z x≤z y≤z _ (inj₁ x₁) = IsPartialOrder.≤-respˡ-≈
                                                (isPartialOrder isCompleteLattice)
                                                x₁
                                                x≤z
    lUpperbound {x} {y} z x≤z y≤z _ (inj₂ y₁) = IsPartialOrder.≤-respˡ-≈
                                                (isPartialOrder isCompleteLattice)
                                                y₁
                                                y≤z
                    
    supIsLeastUpperBound : {x y : Carrier} (z : Carrier)
                         → x ≤ z → y ≤ z → (x ∨ y) ≤ z
    supIsLeastUpperBound {x} {y} z x≤z y≤z = proj₂ (supTwoElems {x} {y})
                                                   z
                                                   (lUpperbound {x} {y} z x≤z y≤z) 

    sup : Supremum (_≤_) _∨_
    sup x y = x≤x∨y {x} {y}  , y≤x∨y {x} {y} , λ z → supIsLeastUpperBound {x} {y} z

    -- proof of _∧_ is infimum
    infTwoElems : {x y : Carrier} → IsInfimum _≤_ subsetTwoElems (⋀ subsetTwoElems)
    infTwoElems {x} {y} = isInfimum isCompleteLattice (subsetTwoElems {x} {y})

    x∧y≤x : {x y : Carrier} → (x ∧ y) ≤ x
    x∧y≤x {x} {y} = proj₁ (infTwoElems {x} {y}) x (inj₁ eqReflPoset)

    x∧y≤y : {x y : Carrier} → (x ∧ y) ≤ y
    x∧y≤y {x} {y} = proj₁ (infTwoElems {x} {y}) y (inj₂ eqReflPoset)

    gUpperbound : {x y : Carrier} (z : Carrier) → z ≤ x → z ≤ y
                → IsLowerBound _≤_ (subsetTwoElems {x} {y}) z
    gUpperbound {x} {y} z z≤x z≤y _ (inj₁ x₁) = IsPartialOrder.≤-respʳ-≈
                                                 (isPartialOrder isCompleteLattice)
                                                 x₁
                                                 z≤x
    gUpperbound {x} {y} z z≤x z≤y _ (inj₂ y₁) = IsPartialOrder.≤-respʳ-≈
                                                (isPartialOrder isCompleteLattice)
                                                y₁
                                                z≤y
    
    infIsGreatestLowerbound : {x y : Carrier} (z : Carrier) → z ≤ x → z ≤ y → z ≤ (x ∧ y)
    infIsGreatestLowerbound {x} {y} z z≤x z≤y = proj₂ (infTwoElems {x} {y})
                                                      z
                                                      (gUpperbound {x} {y} z z≤x z≤y)
    
    inf : Infimum (_≤_) _∧_
    inf x y = x∧y≤x , x∧y≤y , λ z → infIsGreatestLowerbound {x} {y} z  

    isLattice : IsLattice (_≈_) (_≤_) (_∨_) (_∧_)
    isLattice = record { isPartialOrder = isPartialOrder (isCompleteLattice)
                       ; supremum = sup
                       ; infimum = inf
                       } 

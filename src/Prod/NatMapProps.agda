open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.NatMapProps {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid ; _⇒_ ; Reflexive ; IsEquivalence ; _⇔_) renaming (Rel to BinRel)
open import Relation.Nullary using (¬_)
open import Function using (Func)
open import Function.Construct.Composition using (function)

open import Relation.Binary.PropositionalEquality as ≡ using ()
import Relation.Binary.Reasoning.Setoid            as SReasoning  using ( begin_ ; step-≈˘; step-≈; _∎)


open import Setoid.Algebras  {𝑆 = 𝑆} hiding (mkcon)
open import Setoid.Algebras.Congruences {𝑆 = 𝑆} using (mkcon)
open import Setoid.Homomorphisms {𝑆 = 𝑆} hiding (_≅_ ; mkiso)
open import Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆} using (_≅_ ; mkiso)
open import Setoid.Functions  using (IsInjective
                                    ; IsSurjective
                                    ; Image_∋_
                                    ; Dom
                                    )
open import Setoid.Relations using (0rel ; fker)

open import Prod.Subembedding
open import Prod.Subdirect using (⨅-fun ; IsSubdirectProduct)
open import Isomorphisms.Isomorphisms using (Iso ; Iso→≅)
open import Utils.Axioms using (absurd ; ¬∀→∃¬)
open import Utils.Definitions
private variable α β ρᵅ ρᵝ i : Level

open Func renaming (f to <$>) 

-- family of homomorphisms
module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) where
  record FamOfHoms : Set (ov (i ⊔ α ⊔ β ⊔ ρᵅ ⊔ ρᵝ)) where
    field
      family : ∀ (j : I) → hom 𝐁 (𝓐 j)

-- separate points
module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) where
  open Algebra 𝐁 renaming (Domain to B)
  open Setoid B 
  famSeparatePoints : (h : FamOfHoms 𝐁 𝓐) → Set (i ⊔ β ⊔ ρᵝ ⊔ ρᵅ)
  famSeparatePoints h = (x  y : 𝕌[ 𝐁 ])
                      → ¬ (x ≈ y)
                      → Σ[ j ∈ I ] (pred j x y) 
    where
      open FamOfHoms h
      hᵢ : (j : I) → Func B 𝔻[ (𝓐 j) ]
      hᵢ j = (proj₁ (family j))
      
      pred : (j : I) (x y : 𝕌[ 𝐁 ]) → Set ρᵅ
      pred j x y = ¬ (<$> (hᵢ j) x) ≈aj (<$> (hᵢ j) y)   
        where
          open Algebra (𝓐 j) renaming (Domain to Aj)
          open Setoid Aj renaming (_≈_ to _≈aj_)

-- proposition 3.14
{-
  Let hᵢ be a homomorphism from 𝐁 to 𝐀ᵢ, for each i ∈ I, and let h = ⊓_{i ∈ I} hᵢ.
  Then ker (h) = ⋂ᵣ I ker(hᵢ). Furthermore the following are equivalent:
  (a) The family ⟨ hᵢ : i ∈ I ⟩ separate points
  (b) h is injective
  (c) ⋂ᵣ I ker(hᵢ) = 0_B
-}

module _ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ) (h : FamOfHoms 𝐁 𝓐) where

  open Algebra 𝐁 renaming (Domain to B)
  open Setoid B renaming (Carrier to Car)
  open Algebra (⨅ 𝓐) renaming (Domain to ⨅A)
  open Setoid ⨅A renaming (_≈_ to _≈A_)
  open FamOfHoms h

  kerOfFam : I → BinRel 𝕌[ 𝐁 ] ρᵅ
  kerOfFam j = fker (proj₁ (family j))


  kerOfFamIsRefl : (j : I) → Reflexive (kerOfFam j)
  kerOfFamIsRefl j = Ajrefl
    where
      open Algebra (𝓐 j) renaming (Domain to Aj)
      open Setoid Aj renaming (_≈_ to _≈aj_ ; isEquivalence to eq)
      open IsEquivalence eq renaming (refl to Ajrefl)

  {- A prod of homomorphisms h = ⨅ hᵢ, where ⟨ hᵢ : hom 𝐁 (𝓐 i) ⟩ is a family of homomorphisms,
  is such that h(b)(i) = hᵢ(b)
  -} 
  IsProdOfHoms : hom 𝐁 (⨅ 𝓐)
  IsProdOfHoms  = F , record { compatible = comp }
    where
      F : Func (𝔻[ 𝐁 ]) (𝔻[ (⨅ 𝓐) ])
      F = record { f = λ b i  → <$> (proj₁ (family i)) b
                 ; cong = λ {x} {y} x=y j → cong (proj₁ (family j)) x=y
                 }
                 
      comp : compatible-map 𝐁 (⨅ 𝓐) F
      comp j = hjcomp
        where
          open IsHom (proj₂ (family j)) renaming (compatible to hjcomp)


  kerOfProd→⋂kers : ∀ {a b : 𝕌[ 𝐁 ]}
                   → (fker ((proj₁ IsProdOfHoms))) a b
                   → (⋂ᵣ {s = i ⊔ α} I kerOfFam) a b
  kerOfProd→⋂kers a≈ₖb i = lift (a≈ₖb i)

  ⋂kers→kerOfProd : ∀ {a b : 𝕌[ 𝐁 ]}
                   → (⋂ᵣ {s = i ⊔ α} I kerOfFam) a b
                   → (fker ((proj₁ IsProdOfHoms))) a b
  ⋂kers→kerOfProd {a} {b} a≈⋂b = λ j → lower (a≈⋂b j)

 -- proving ⟨hᵢ : i ∈ I⟩ separates points implies h is injective 
  firstEquiv : famSeparatePoints 𝐁 𝓐 h → IsInjective (proj₁ IsProdOfHoms)
  firstEquiv sp {x} {y} inj = absurd (x ≈ y)
                                     λ ¬x≈y → proj₂ (sp x y ¬x≈y)
                                                    (inj (proj₁ (sp x y ¬x≈y)))
 
  -- proving h is injective implies ∩ ker hᵢ = 0B
  {-
  First, we separate the statment in:
  1. ∩ ker hᵢ ⊆ 0B
  2. 0B ⊆ ∩ ker hᵢ
 -}
  
  0⊆∩ : 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} ⇒ ⋂ᵣ {s = i ⊔ α} I kerOfFam
  0⊆∩ {x = x} {y = y} (lift xθy) j = lift (cong (proj₁ (family j)) xθy)
  
  secondEquiv₁ : IsInjective (proj₁ IsProdOfHoms)
               → ⋂ᵣ {s = i ⊔ α} I kerOfFam ⇒ 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ}
  secondEquiv₁ inj {x} {y} = λ eq → lift (inj (⋂kers→kerOfProd eq))

  secondEquiv₂ : IsInjective (proj₁ IsProdOfHoms)
               → 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} ⇒ ⋂ᵣ {s = i ⊔ α} I kerOfFam
  secondEquiv₂ inj {x} {y} = 0⊆∩

  thirdEquiv : ⋂ᵣ {s = i ⊔ α} I kerOfFam ⇔ 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} → famSeparatePoints 𝐁 𝓐 h
  thirdEquiv (∩→0 , 0→∩) = λ x y ¬x≈y → proj₁ (¬x≈y→¬kerhᵢ ¬x≈y) , proj₂ (¬x≈y→¬kerhᵢ ¬x≈y)
    where
      unLiftEq : {x y : Car} → Lift ρᵅ (x ≈ y) → x ≈ y
      unLiftEq (lift p) = p
      
      ¬x≈y→¬0 : {x y : Car} → ¬ (x ≈ y) → ¬ (0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} x y)
      ¬x≈y→¬0 ¬x≈y = λ x≈y∈0 → ¬x≈y (unLiftEq x≈y∈0)

      ¬0→¬∩ker : {x y : Car} → ¬ (0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} x y) → ¬ (⋂ᵣ {s = i ⊔ α} I kerOfFam x y)
      ¬0→¬∩ker  ¬0 = λ x≈y∈∩ker → ¬0 (∩→0 x≈y∈∩ker)

      ¬∩ker→¬kerhᵢ : {x y : Car} → ¬ (⋂ᵣ {s = i ⊔ α} I kerOfFam x y) → Σ[ j ∈ I ] ¬(kerOfFam j x y)
      ¬∩ker→¬kerhᵢ {x} {y} ¬∩ = ¬∀→∃¬ λ x≈ajy → ¬∩ (kerOfProd→⋂kers x≈ajy)

      ¬x≈y→¬kerhᵢ : {x y : Car} → ¬ (x ≈ y) → Σ[ j ∈ I ] ¬(kerOfFam j x y)
      ¬x≈y→¬kerhᵢ ¬x≈y = (¬∩ker→¬kerhᵢ (¬0→¬∩ker (¬x≈y→¬0 ¬x≈y)))

  ∩⇔0→Inj : ⋂ᵣ {s = i ⊔ α} I kerOfFam ⇔ 0rel {𝐴 = B} {𝐵 = ⨅A} {ℓ = ρᵅ} → IsInjective (proj₁ IsProdOfHoms)
  ∩⇔0→Inj ∩=0 = firstEquiv (thirdEquiv ∩=0)
            
{-
Proposition: Let 𝐀 an algebra and let θᵢ a congruence on 𝐀 for every i ∈ I.
If ⋂_{i ∈ I} θᵢ = 0_A then the natrual map 𝐀 → ⨅_{i∈ I} 𝐀/θᵢ is a subdirect embedding.
Conversely,  if g → 𝐀 ⨅ 𝐁ᵢ is a subdirect embedding then θᵢ = ker(pᵢ ∘ g), we have ∩θᵢ = 0_A and 𝐀/θᵢ ⋍ 𝐁ᵢ.
-}

prodQuot : ∀ {ℓ} {I : Set i} (𝐀 : Algebra α ρᵅ) (θ : I → Con 𝐀 {ℓ = ℓ}) → Algebra (α ⊔ i) (i ⊔ ℓ)
prodQuot {α = α} {ℓ = ℓ} {I = I} 𝐀 θ = ⨅ family
  where
    family : I → Algebra α ℓ 
    family  i = 𝐀 ╱ (θ i)

module _ {I : Set i} (𝐀 : Algebra α ρᵅ) (θ : I → Con 𝐀 {ρᵅ}) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car)


  -- A family of quotient algebras for the family of congruences ⟨θᵢ : i ∈ I ⟩
  famOfQuot : I → Algebra α ρᵅ
  famOfQuot i = 𝐀 ╱ (θ i)

  -- defining the Algebra of direct product of the family of quotient algebras
  prodOfQuot : Algebra (α ⊔ i) (i ⊔ ρᵅ)
  prodOfQuot = prodQuot {I = I} 𝐀 θ

  open Algebra prodOfQuot renaming (Domain to ⨅A/θ)
  open Setoid ⨅A/θ renaming (Carrier to pCar)

  -- defining the function natural map 𝐀 → ⨅ 𝐀／(θ i) 
  NatMap : Func A ⨅A/θ
  NatMap = record { f = λ x j → x ; cong = λ x=y j → IsCongruence.reflexive (proj₂ (θ j)) x=y }

  -- Given a family of congruences we take the binary relation of each congruence
  familyOfRels : (I → Con 𝐀 {ρᵅ}) → I → BinRel Car ρᵅ
  familyOfRels θ = λ i → proj₁ (θ i) 

  -- defining the family of homomorphisms ⟨hᵢ : 𝐀 → 𝐀／(θ i), ∀ i  ∈ I ⟩ 
  natHomMap : FamOfHoms 𝐀 famOfQuot
  natHomMap = record { family = λ j → (fam j) , isHomFam j }
    where
      fam : (j : I) → Func A (𝔻[ famOfQuot j ])
      fam j = record { f = λ x → x ; cong = crefl}
        where
          open IsCongruence (proj₂ (θ j)) renaming (reflexive to crefl)

      isHomFam : (j : I) → IsHom 𝐀 (famOfQuot j) (fam j) 
      isHomFam j = record { compatible = λ {f} {a} → comp f λ x → congrefl}
        where
          open IsCongruence (proj₂ (θ j)) renaming ( is-compatible to comp
                                                   ; is-equivalence to equiv
                                                   )
          open IsEquivalence equiv renaming (refl to congrefl)

  open FamOfHoms natHomMap

  -- defining the product of the family of natural map homomorphisms
  prodOfNatHomMap : hom 𝐀 prodOfQuot
  prodOfNatHomMap = NatMap , record { compatible = λ j → IsHom.compatible (proj₂ (family j))}

  -- note that hᵢ : 𝐀 → 𝐀／θᵢ is surjective for each i ∈ I 
  hᵢIsSurj : ∀ (j : I) → IsSurjective (proj₁ (family j))
  hᵢIsSurj j {y} = Setoid.Functions.eq y congrefl
    where
      open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equiv)
      open IsEquivalence equiv renaming (refl to congrefl)

  -- Let pᵢ : ⨅ 𝐀／θⱼ → 𝐀 ／ θᵢ the projection of the natural map.
  -- now we want to prove that pᵢ ∘ h = hᵢ so pᵢ is surjective.
  projOfProd : ( j : I ) → Func 𝔻[ 𝐀 ] 𝔻[ famOfQuot j ]
  projOfProd j = function  (proj₁ prodOfNatHomMap) (⨅-fun famOfQuot j) 

  pᵢ∘h≈hᵢ : (j : I) (x : 𝕌[ 𝐀 ]) → Set ρᵅ
  pᵢ∘h≈hᵢ j x = (<$> (projOfProd j) x) ≈j (<$> (proj₁ (family j)) x)
    where
      open Algebra (famOfQuot j) renaming (Domain to 𝓐j)
      open Setoid 𝓐j renaming (_≈_ to _≈j_)  
  
  -- Since hᵢ is surjective then pᵢ is surjective
  pᵢIsSurj : ∀ (j : I) → IsSurjective (⨅-fun famOfQuot j)
  pᵢIsSurj j {y} = Setoid.Functions.eq (λ j → y) reflj
    where
      open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equivj)
      open IsEquivalence equivj renaming (refl to reflj)
  
  eqOfIndexes : ∀ (j : I) (x : 𝕌[ 𝐀 ]) → pᵢ∘h≈hᵢ j x
  eqOfIndexes j x = reflj
    where
      open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equivj)
      open IsEquivalence equivj renaming (refl to reflj)
  

  -- First statement of proposition 
  NatMapIsSubEmb : (⋂ᵣ {s = α ⊔ i} I (familyOfRels θ)) ⇔  0rel {𝐴 = A} {𝐵 = ⨅A/θ} {ℓ = ρᵅ} 
                 → IsSubEmb 𝐀 famOfQuot  NatMap
  NatMapIsSubEmb (∩θ⇒0A , 0A⇒∩θ) = record { Mon = monOfProd
                                            ; isSubdirProd = DirImageIsSubEmb 
                                            }
    where
      monOfProd : IsMon 𝐀 (⨅ famOfQuot) NatMap
      monOfProd = record { isHom = proj₂ prodOfNatHomMap
                         ; isInjective = ∩⇔0→Inj
                                         𝐀
                                         famOfQuot
                                         natHomMap
                                         ((λ xθy → ∩θ⇒0A xθy) , 0⊆∩ 𝐀 famOfQuot natHomMap)
                         }


      open IsMon monOfProd 
      open Algebra (genAlgFromMon 𝐀 famOfQuot (NatMap , monOfProd)) renaming (Domain to gA)

      open Image_∋_ 
      F : Func gA ⨅A/θ
      F = record { f = λ {(f , p) j →  (<$> NatMap) (f j) j}; cong = λ xθjy j → xθjy j}
      
      DirImageIsSubEmb : IsSubdirectProduct (genAlgFromMon 𝐀 famOfQuot (NatMap , monOfProd))
                                            famOfQuot
                                            (subAlg 𝐀 famOfQuot (NatMap , monOfProd))
      DirImageIsSubEmb j {a} = eq ((λ k → a) , a , θₗRefl ) refl-j
        where
          open IsCongruence (proj₂ (θ j)) renaming (is-equivalence to equivj)
          open IsEquivalence equivj renaming (refl to refl-j)
          
          θₗRefl : (l : I) → proj₁ (θ l) a a
          θₗRefl l = refl-l
            where
              open IsCongruence (proj₂ (θ l)) renaming (is-equivalence to equivl)
              open IsEquivalence equivl renaming (refl to refl-l)
          

-- last statement of proposition
module _ {I : Set i} (𝐀 : Algebra α ρᵅ) (𝓑 : I → Algebra β ρᵝ) (g : SubdirectEmbedding 𝐀 𝓑) where
  open Algebra 𝐀 renaming (Domain to A ; Interp to AInterp)
  open Setoid A renaming (Carrier to Car ; _≈_ to _≈a_ ; isEquivalence to equivA)
  open IsEquivalence equivA renaming (refl to reflA)

  open IsSubEmb (proj₂ g) renaming (isSubdirProd to subp)
  open Func (proj₁ g) renaming (cong to gcong)

  open IsMon Mon renaming (isInjective to injg ; isHom to gHom)
  open IsHom gHom renaming (compatible to gCompatible)
  
  dirProd : Algebra (β ⊔ i) (ρᵝ ⊔ i)
  dirProd = ⨅ 𝓑

  genFromSubEmb : Algebra (α ⊔ (β ⊔ i) ⊔ (ρᵝ ⊔ i)) (ρᵝ ⊔ i)
  genFromSubEmb = genAlgFromMon 𝐀 𝓑 (((proj₁ g) , Mon))

  open Algebra genFromSubEmb renaming (Domain to gA)
  open Setoid gA renaming (Carrier to gACar)
  
  open Algebra dirProd renaming (Domain to ⨅B ; Interp to ⨅BInterp)
  
  θᵢ : (j : I) → BinRel Car ρᵝ
  θᵢ j = fker (function (proj₁ g) (⨅-fun 𝓑 j))

  famOfCong : ∀ (j : I) → Con 𝐀 {ℓ = ρᵝ}
  famOfCong j = θᵢ j , mkcon reflθ equivθ θⱼComp
    where
      open Algebra (𝓑 j) renaming (Domain to Bj ; Interp to BjInterp)
      open Setoid Bj renaming (isEquivalence to equivBj ; _≈_ to _≈bj_)
      open IsEquivalence equivBj renaming (refl to reflBj ; sym to symBj ; trans to transBj)

      reflθ : {a b : Car} → a ≈a b → θᵢ j a b
      reflθ {a} {b} a≈b = gcong {a} {b} a≈b j

      equivθ :  IsEquivalence (θᵢ j)
      equivθ  = record { refl =  reflBj ; sym = symBj ; trans = transBj }

      θⱼComp : 𝐀 ∣≈ θᵢ j
      θⱼComp 𝑓 {x} {y} xθⱼy = begin
        f (<$> AInterp (𝑓 , x)) j ≈⟨ gCompatible j ⟩
        <$> BjInterp (𝑓 , λ a → f (x a) j) ≈⟨ cong BjInterp (≡.refl , xθⱼy) ⟩
        <$> BjInterp (𝑓 , λ a → f (y a) j) ≈⟨ symBj (gCompatible j) ⟩
        f (<$> AInterp (𝑓 , y)) j
        ∎
        where
          open SReasoning Bj              
      
  famOfQuot₂ : ∀ (j : I) → Algebra α ρᵝ
  famOfQuot₂ j = 𝐀 ╱ famOfCong j 

  subemb→quot≅Bᵢ : ∀ (j : I)
                 → (⋂ᵣ {s = α ⊔ i} I θᵢ) ⇔  0rel {𝐴 = A} {𝐵 = ⨅B} {ℓ = ρᵅ}
                   × (famOfQuot₂ j) ≅ (𝓑 j)
  subemb→quot≅Bᵢ j = (∩θᵢ⇒0 , 0⇒∩θᵢ)
                   , Iso→≅ (famOfQuot₂ j) (𝓑 j) quotIso
    where
      open Algebra (𝓑 j) renaming (Domain to Bj)
      open Setoid Bj renaming (_≈_ to _≈bj_ ; sym to bjsym ; trans to bjtrans)

      open Image_∋_

    {- Defined in the original proof but not used in the formalization -}
      pi∘gIsSurjDeprecated : IsSurjective (function (proj₁ g) (⨅-fun 𝓑 j))
      pi∘gIsSurjDeprecated {y} with subp j {y}
      ... | eq (bᵢ , a , bᵢ≈ga) y≈gt = eq a (bjtrans y≈gt (bjsym (bᵢ≈ga j)))

      -- proving that 𝐀／θᵢ ≅ 𝐁ᵢ
      quotIso : Iso (famOfQuot₂ j) (𝓑 j)
      quotIso = F , record { Hom = FIsHom ; IsBij = (λ fx=fy → fx=fy) ,  pᵢ∘gIsSurj }
        where
          {-
            Defining F : 𝐀／θᵢ → 𝓑ᵢ as
                     F(a／θᵢ) = pᵢ (g (a)).

            The composition pᵢ ∘ g is f here.
            Then, F is a homomorphism because pᵢ ∘ g is also a homomorphism.
          -}
          
          F : Func 𝔻[ (famOfQuot₂ j) ] Bj
          F = record { f = λ x → f x j  ; cong = λ x → x }

          FIsHom : IsHom (famOfQuot₂ j) (𝓑 j) F
          FIsHom = record { compatible = λ {h} {a} → gCompatible j }

          pᵢ∘gIsSurj : IsSurjective F
          pᵢ∘gIsSurj {y} with subp j {y}
          ... | eq (bᵢ , a , bᵢ≈ga) y≈gt = eq a ((bjtrans y≈gt (bjsym (bᵢ≈ga j))))
    
      -- Proving that ∩θ = 0A
      kerg≈∩θ : fker (proj₁ g) ⇔  ⋂ᵣ {s = α ⊔ i} I θᵢ
      kerg≈∩θ = (λ x k → lift (x k)) , λ x k → lower (x k)
         
      ∩θᵢ⇒0 : ⋂ᵣ {s = α ⊔ i} I θᵢ ⇒ 0rel {𝐴 = A} {𝐵 = ⨅B} {ℓ = ρᵅ}
      ∩θᵢ⇒0 pᵢgx≈pigy = lift (injg (proj₂ kerg≈∩θ pᵢgx≈pigy)) 

      0⇒∩θᵢ : 0rel {𝐴 = A} {𝐵 = ⨅B} {ℓ = ρᵅ} ⇒ ⋂ᵣ {s = α ⊔ i} I θᵢ
      0⇒∩θᵢ x≈y k = proj₁ kerg≈∩θ (λ l → gcong (lower x≈y) l) k

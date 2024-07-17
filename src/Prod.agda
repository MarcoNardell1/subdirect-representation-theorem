open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod {𝑆 : Signature 𝓞 𝓥} where
open import Agda.Builtin.Equality using (_≡_)
open import Level
open import Data.Product
open import Relation.Binary using (Setoid) renaming (Rel to BinRel)
open import Function using (_∘_ ; Func)
open import Function.Construct.Composition using (function)

open import Base.Relations using (0[_])
open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Subalgebras.Subalgebras {𝑆 = 𝑆} 
open import Setoid.Functions using (IsSurjective ; IsBijective ; BijInv)
open import Setoid.Homomorphisms {𝑆 = 𝑆} hiding (_≅_ ; mkiso)
open import Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆}


open Func renaming (f to <$>) 

private variable α β ρᵅ ρᵝ i : Level


-- Projections of a product
module _ {I : Set i} (𝓐 : I → Algebra α ρᵅ) where
    ⨅-fun : (j : I) → Func (𝔻[ ⨅ 𝓐 ]) (𝔻[ 𝓐 j ])
    ⨅-fun j = record { f = λ x →  x j ; cong = λ {a} {b} a=b → a=b j }


-- Type of SubdirectProduct
{-
  An algebra 𝐁 is a subdirect product of ⟨ 𝐀ᵢ : i ∈ I ⟩ if 𝐁 is
  a subalgebra of ⨅_(i ∈ I) 𝐀ᵢ, and for every j ∈ I, pⱼ|B : 𝐁 → 𝐀ᵢ is surjective. 
-}
IsSubdirectProduct : ∀ {I : Set i} (𝐁 : Algebra β ρᵝ) (𝓐 : I → Algebra α ρᵅ)
                   → 𝐁 ≤ (⨅ 𝓐)
                   → Set (i ⊔ β ⊔ α ⊔ ρᵅ) 
IsSubdirectProduct {I = I} 𝐁 𝓐 𝐁≤𝓐 = (j : I) →  IsSurjective (g j)
  where
    
    g : (j : I) → Func (𝔻[ 𝐁 ]) (𝔻[ 𝓐 j ])
    g j = function (proj₁ (proj₁ 𝐁≤𝓐)) (⨅-fun 𝓐 j)


record SubdirectProduct : Set (ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ))
  where
  field
      ix : Set i
      family :  ix → Algebra α ρᵅ
      subalg : Algebra β ρᵝ
      isSubAlg : subalg ≤ ⨅ family 
      isSubdirProd : IsSubdirectProduct {I = ix} subalg family isSubAlg 


{- Some Homomorphic images properties -} 
module _ {𝐀 : Algebra α ρᵅ} {𝐁 : Algebra β ρᵝ} {f : hom 𝐀 𝐁} where
  open Setoid (𝔻[ 𝐁 ])
  open IsHom (proj₂ f)
  eq : (HomImageOf[ f ]) IsHomImageOf 𝐀
  eq = ( F , record { compatible = λ {g} {a} → compatible }) , λ {y} → Setoid.Functions.eq (proj₁ (proj₂ y))
                                                                                             (sym (proj₂ (proj₂ y)))
    where
      F : Func (𝔻[ 𝐀 ]) (𝔻[ HomImageOf[ f ] ])
      F = record { f = λ x →  <$> (proj₁ f) x , x , refl ; cong = λ {a} {b} a=b → cong (proj₁ f) a=b } 

𝐁≅Homf : ∀ (𝐁 : Algebra β ρᵝ) (𝐀 : Algebra α ρᵅ) → 𝐁 IsHomImageOf 𝐀 → Σ[ f ∈ hom 𝐀 𝐁 ] (𝐁 ≅ HomImageOf[ f ])
𝐁≅Homf 𝐁 𝐀 (f , surjf)  = f , iso
  where
   open IsHom (proj₂ f)
   open Setoid (𝔻[ 𝐁 ]) 
   𝐁→Homf : hom 𝐁 HomImageOf[ f ]
   𝐁→Homf = F , record { compatible = λ {g} {a} → refl}
     where
       aFrom𝐁 : ∀ (b : 𝕌[ 𝐁 ]) → Σ[ a ∈ 𝕌[ 𝐀 ] ] (b ≈ (<$> (proj₁ f) a))
       aFrom𝐁 b with surjf {b}
       ... | Setoid.Functions.eq a x = a , x
       
       F : Func (𝔻[ 𝐁 ]) (𝔻[ HomImageOf[ f ] ])
       F = record { f = λ x → x , proj₁ (aFrom𝐁 x) , sym (proj₂ (aFrom𝐁 x)) ; cong = λ a=b → a=b } 

   Homf→𝐁 : hom HomImageOf[ f ] 𝐁
   Homf→𝐁 = F , record { compatible = λ {g} {a} → refl}
     where 
       F : Func (𝔻[ HomImageOf[ f ] ]) (𝔻[ 𝐁 ])
       F = record { f = λ x → proj₁ x ; cong = λ {a} {b} a=b → a=b} 
   
   iso : 𝐁 ≅ HomImageOf[ f ]
   iso = record { to = 𝐁→Homf ; from = Homf→𝐁 ; to∼from = λ x → refl ; from∼to = λ y → refl}

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
       IsSubdirProd : IsSubdirectProduct (genAlgFromMon (h , Mon)) 𝓐 genAlg≤Prod
     
   SubdirectEmbedding : Set ((ov (i ⊔ α ⊔ ρᵅ ⊔ β ⊔ ρᵝ)))
   SubdirectEmbedding = Σ (Func B A) IsSubEmb

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

module _ {ℓ} {I : Set i} (𝐀 : Algebra α ρᵅ) (θ : I → Con 𝐀 {ℓ}) where
  open Algebra 𝐀 renaming (Domain to A)
  open Setoid A renaming (Carrier to Car)

  famOfCons : I → Algebra α ℓ
  famOfCons i = 𝐀 ╱ (θ i)
  
  prodOfQuot : Algebra (α ⊔ i) (i ⊔ ℓ)
  prodOfQuot = prodQuot {I = I} 𝐀 θ

  open Algebra prodOfQuot renaming (Domain to ⨅A/θ)
  open Setoid ⨅A/θ renaming (Carrier to pCar)

  NatMap : Func A ⨅A/θ
  NatMap = record { f = λ x j → x ; cong = λ x=y j → IsCongruence.reflexive (proj₂ (θ j)) x=y }

  familyOfRels : (I → Con 𝐀 {ℓ}) → I → BinRel Car ℓ
  familyOfRels θ = λ i → proj₁ (θ i) 

  -- First statement of proposition

  ⋂ᵣ : ∀ {i ρ s} (I : Set i) → (I → BinRel Car ρ) → BinRel Car (ρ ⊔ i ⊔ s)
  ⋂ᵣ {j} {ρ} {s} I R = λ x y → (i : I) → Lift (ρ ⊔ j ⊔ s) (R i x y)

  NatMapIsSubEmb : (⋂ᵣ {s = α ⊔ ρᵅ ⊔ ℓ} I (familyOfRels θ)) ≡ 0[ Car ] {ρ = ℓ ⊔ ρᵅ ⊔ i}
                 → IsSubEmb 𝐀 famOfCons  NatMap
  NatMapIsSubEmb p = {!!}

-- Defining Isomorphisms as a bijective homomorphism
module _ (𝐀 : Algebra α ρᵅ) (𝐁 : Algebra β ρᵝ) where
  open Algebra 𝐀 renaming (Domain to A)
  open Algebra 𝐁 renaming (Domain to B)

  record IsIso (h : Func A B) : Set (ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ))) where
    field
      Hom : IsHom 𝐀 𝐁 h
      IsBij : IsBijective h
      
  Iso : Set ((ov((α ⊔ ρᵅ ⊔ β ⊔ ρᵝ ⊔ ρᵝ)))) 
  Iso = Σ (Func A B) IsIso
{-
  Iso→≅ : (h : Iso) → 𝐀 ≅ 𝐁
  Iso→≅ h = mkiso hom→ ←hom (λ b → {!!}) {!!}
    where
      open IsIso (proj₂ h)
      open IsHom Hom
      open Setoid A renaming (refl to refla; _≈_ to _≈ₐ_)
      open Setoid B renaming (refl to reflb; _≈_ to _≈b_)

      h⁻¹ : Func B A
      h⁻¹ = BijInv (proj₁ h) IsBij
 
      hom→ : hom 𝐀 𝐁
      hom→ = (proj₁ h) , Hom

      ←hom : hom 𝐁 𝐀
      ←hom = h⁻¹ , record { compatible = λ {f} {a} → {!!} } 
     
      eqb : ∀ (a : 𝕌[ 𝐀 ]) → <$> h⁻¹ (<$> (proj₁ h) a) ≈ₐ a
      eqb a = {!!}
-}

{-
IsIso : (Hom A B) → Set
IsIso h = Σ[ i ∈ Iso A B ] (ext-eq h (from i))
  where ext-eq : (f g : Hom A B) → Set
        ext-eq f g = (∀ a : D[ A ]) → f a ≈ g a
-}
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



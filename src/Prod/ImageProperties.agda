open import Overture using ( 𝓞 ; 𝓥 ; Signature ; ∣_∣)

module Prod.ImageProperties {𝑆 : Signature 𝓞 𝓥} where
open import Level
open import Data.Product
open import Relation.Binary using (Setoid)
open import Function using (Func)

open import Setoid.Algebras  {𝑆 = 𝑆}
open import Setoid.Subalgebras.Subalgebras {𝑆 = 𝑆} 
open import Setoid.Functions renaming (eq to setEq)
open import Setoid.Homomorphisms {𝑆 = 𝑆} hiding (_≅_)
open import Setoid.Homomorphisms.Isomorphisms {𝑆 = 𝑆}

open Func renaming (f to <$>) 

private variable α β ρᵅ ρᵝ i : Level

{- Some Homomorphic images properties -} 
module _ {𝐀 : Algebra α ρᵅ} {𝐁 : Algebra β ρᵝ} {f : hom 𝐀 𝐁} where
  open Setoid (𝔻[ 𝐁 ])
  open IsHom (proj₂ f)
  eq : (HomImageOf[ f ]) IsHomImageOf 𝐀
  eq = ( F , record { compatible = λ {g} {a} → compatible }) , λ {y} → setEq (proj₁ (proj₂ y)) (sym (proj₂ (proj₂ y)))
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
       ... | setEq a x = a , x
       
       F : Func (𝔻[ 𝐁 ]) (𝔻[ HomImageOf[ f ] ])
       F = record { f = λ x → x , proj₁ (aFrom𝐁 x) , sym (proj₂ (aFrom𝐁 x)) ; cong = λ a=b → a=b } 

   Homf→𝐁 : hom HomImageOf[ f ] 𝐁
   Homf→𝐁 = F , record { compatible = λ {g} {a} → refl}
     where 
       F : Func (𝔻[ HomImageOf[ f ] ]) (𝔻[ 𝐁 ])
       F = record { f = λ x → proj₁ x ; cong = λ {a} {b} a=b → a=b} 
   
   iso : 𝐁 ≅ HomImageOf[ f ]
   iso = record { to = 𝐁→Homf ; from = Homf→𝐁 ; to∼from = λ x → refl ; from∼to = λ y → refl}

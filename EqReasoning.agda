
module EqReasoning where

open import Prelude

infixr 0 _≡⟨_⟩_ _≡⟨_⟩ʳ_
infix  1 _∎

_≡⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ p = p

_≡⟨_⟩ʳ_ : ∀ {a} {A : Set a} (x : A) {y z} → y ≡ x → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ʳ p = p

_∎ : ∀ {a} {A : Set a} (x : A) → x ≡ x
x ∎ = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B → C) {x x′ y y′} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

_≡tr_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ≡tr p = p

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P x → P y
subst P refl px = px
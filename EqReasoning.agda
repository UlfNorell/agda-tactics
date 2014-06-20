
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

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B → C) {x x′ y y′} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_≡tr_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ≡tr p = p
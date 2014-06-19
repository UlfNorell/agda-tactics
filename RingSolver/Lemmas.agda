
module RingSolver.Lemmas where

open import Prelude
open import EqReasoning
open import Ring as R
open import RingSolver.NF
open import RingSolver.Exp

_=>_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl => p = p

map++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
          map f (xs ++ ys) ≡ map f xs ++ map f ys
map++ f [] ys = refl
map++ f (x ∷ xs) ys rewrite map++ f xs ys = refl

module _ {A : Set} {{RingA : Ring A}} where
  open Ring RingA

  #prod++ : ∀ xs ys → #prod (xs ++ ys) ≡ #prod xs ⊛ #prod ys
  #prod++ [] ys = sym (one-id-l _)
  #prod++ (x ∷ xs) ys rewrite #prod++ xs ys = mul-assoc _ _ _

  +#* : ∀ a b (x : A) → (a + b) #* x ≡ a #* x ⊕ b #* x
  +#* zero b x = sym (zero-id-l _)
  +#* (suc a) b x rewrite +#* a b x = plus-assoc _ _ _

  *#* : ∀ a b (x : A) → (a * b) #* x ≡ a #* (b #* x)
  *#* zero    b x = refl
  *#* (suc a) b x rewrite +#* (a * b) b x | *#* a b x = plus-commute _ _

  #*-commute : ∀ a (x y : A) → a #* (x ⊛ y) ≡ x ⊛ a #* y
  #*-commute zero x y = sym (zero-z-r _)
  #*-commute (suc a) x y rewrite #*-commute a x y = sym (mul-distr-l _ _ _)

  #*-assoc : ∀ a (x y : A) → a #* (x ⊛ y) ≡ (a #* x) ⊛ y
  #*-assoc zero x y = sym (zero-z-l _)
  #*-assoc (suc a) x y rewrite #*-assoc a x y = sym (mul-distr-r _ _ _)

  ⟨+⟩-sound : ∀ v₁ v₂ (ρ : Env A) → ⟦ v₁ +nf v₂ ⟧n ρ ≡ ⟦ v₁ ⟧n ρ ⊕ ⟦ v₂ ⟧n ρ
  ⟨+⟩-sound []        v₂        ρ = sym (zero-id-l _)
  ⟨+⟩-sound (t ∷ v₁)  []        ρ = sym (zero-id-r _)
  ⟨+⟩-sound (t₁ ∷ v₁) (t₂ ∷ v₂) ρ with t₁ < t₂
  ⟨+⟩-sound (t₁ ∷ v₁) (t₂ ∷ v₂) ρ | true =
    ⟦ t₁ ⟧t ρ ⊕ ⟦ v₁ +nf (t₂ ∷ v₂) ⟧n ρ
      ≡⟨ cong (_⊕_ (⟦ t₁ ⟧t ρ)) (⟨+⟩-sound v₁ (t₂ ∷ v₂) ρ)  ⟩
    ⟦ t₁ ⟧t ρ ⊕ (⟦ v₁ ⟧n ρ ⊕ ⟦ t₂ ∷ v₂ ⟧n ρ)
      ≡⟨ plus-assoc _ _ _ ⟩
    (⟦ t₁ ⟧t ρ ⊕ ⟦ v₁ ⟧n ρ) ⊕ ⟦ t₂ ∷ v₂ ⟧n ρ ∎
  ⟨+⟩-sound (t₁ ∷ v₁) (t₂ ∷ v₂) ρ | false =
    ⟦ t₂ ⟧t ρ ⊕ ⟦ (t₁ ∷ v₁) +nf v₂ ⟧n ρ
      ≡⟨ cong (_⊕_ (⟦ t₂ ⟧t ρ)) (⟨+⟩-sound (t₁ ∷ v₁) v₂ ρ)  ⟩
    ⟦ t₂ ⟧t ρ ⊕ (⟦ t₁ ∷ v₁ ⟧n ρ ⊕ ⟦ v₂ ⟧n ρ)
      ≡⟨ plus-assoc _ _ _ ⟩
    (⟦ t₂ ⟧t ρ ⊕ ⟦ t₁ ∷ v₁ ⟧n ρ) ⊕ ⟦ v₂ ⟧n ρ
      ≡⟨ cong (flip _⊕_ (⟦ v₂ ⟧n ρ)) (plus-commute _ _)  ⟩
    (⟦ t₁ ∷ v₁ ⟧n ρ ⊕ ⟦ t₂ ⟧t ρ) ⊕ ⟦ v₂ ⟧n ρ
      ≡⟨ plus-assoc _ _ _ ⟩ʳ
    ⟦ t₁ ∷ v₁ ⟧n ρ ⊕ (⟦ t₂ ⟧t ρ ⊕ ⟦ v₂ ⟧n ρ) ∎


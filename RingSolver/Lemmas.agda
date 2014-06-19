
module RingSolver.Lemmas where

open import Prelude
open import EqReasoning
open import RingSolver.NF
open import RingSolver.Exp
open import RingSolver.Bag
open import Data.Nat.Lemmas

_=>_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl => p = p

map++ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) →
          map f (xs ++ ys) ≡ map f xs ++ map f ys
map++ f [] ys = refl
map++ f (x ∷ xs) ys rewrite map++ f xs ys = refl

prod++ : ∀ xs ys → product (xs ++ ys) ≡ product xs * product ys
prod++ [] ys = refl
prod++ (x ∷ xs) ys rewrite prod++ xs ys = mul-assoc x _ _

private
  shuffle₁ : ∀ a b c d → a + ((b + c) + d) ≡ b + c + (a + d)
  shuffle₁ a b c d rewrite add-assoc a (b + c) d
                         | add-commute a (b + c)
                         | add-assoc (b + c) a d
                         = refl

  shuffle₂ : ∀ a b c d → a + b + (c + d) ≡ a + c + (b + d)
  shuffle₂ a b c d rewrite add-assoc (a + b) c d
                         | sym (add-assoc a b c)
                         | add-commute b c
                         | add-assoc a c b
                         | add-assoc (a + c) b d
                         = refl

⟨+⟩-sound : ∀ v₁ v₂ (ρ : Env) → ⟦ v₁ +nf v₂ ⟧n ρ ≡ ⟦ v₁ ⟧n ρ + ⟦ v₂ ⟧n ρ
⟨+⟩-sound [] []               ρ = refl
⟨+⟩-sound [] (_ ∷ _)          ρ = refl
⟨+⟩-sound (t ∷ v₁)  []        ρ = sym (add-0-r _)
⟨+⟩-sound ((i , t₁) ∷ v₁) ((j , t₂) ∷ v₂) ρ with compare t₁ t₂
... | less _ rewrite ⟨+⟩-sound v₁ ((j , t₂) ∷ v₂) ρ
                   = add-assoc (i * product (map ρ t₁)) _ _
... | equal eq rewrite eq | ⟨+⟩-sound v₁ v₂ ρ
                     | mul-distr-r i j (product (map ρ t₂))
                     = shuffle₂ (⟦ i , t₂ ⟧t ρ) (⟦ j , t₂ ⟧t ρ) _ _
... | greater _ rewrite ⟨+⟩-sound ((i , t₁) ∷ v₁) v₂ ρ
                      = shuffle₁ (⟦ j , t₂ ⟧t ρ) (⟦ i , t₁ ⟧t ρ) _ _

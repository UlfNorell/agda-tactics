
module RingSolver where

open import Prelude
open import RingSolver.Exp
open import RingSolver.NF
open import RingSolver.Lemmas
open import Data.Nat.Lemmas

open import EqReasoning

private
  shuffle₁ : ∀ a b c d → (a * b) * (c * d) ≡ (a * c) * (b * d)
  shuffle₁ a b c d rewrite mul-assoc (a * b) c d
                         | sym (mul-assoc a b c)
                         | mul-commute b c
                         | mul-assoc a c b
                         | mul-assoc (a * c) b d = refl

  shuffle₂ : ∀ a b c d → a * (b * c * d) ≡ b * c * (a * d)
  shuffle₂ a b c d rewrite mul-assoc a (b * c) d
                         | mul-commute a (b * c)
                         | mul-assoc (b * c) a d
                         = refl

map-merge : ∀ x y ρ → product (map ρ (merge x y)) ≡ product (map ρ x) * product (map ρ y)
map-merge [] [] ρ = refl
map-merge [] (x ∷ xs) ρ = refl
map-merge (x ∷ xs) [] ρ = sym (mul-1-r _)
map-merge (x ∷ xs) (y ∷ ys) ρ with lessNat x y
... | true  rewrite map-merge xs (y ∷ ys) ρ = mul-assoc (ρ x) _ _
... | false rewrite map-merge (x ∷ xs) ys ρ = shuffle₂ (ρ y) (ρ x) _ _

mulTerm-sound : ∀ t t′ (ρ : Env) →
                ⟦ mulTerm t t′ ⟧t ρ ≡ ⟦ t ⟧t ρ * ⟦ t′ ⟧t ρ
mulTerm-sound (a , x) (b , y) ρ rewrite map-merge x y ρ
                                      = shuffle₁ a b _ _

mulTermDistr : ∀ t v (ρ : Env) → ⟦ map (mulTerm t) v ⟧n ρ ≡ ⟦ t ⟧t ρ * ⟦ v ⟧n ρ
mulTermDistr t [] ρ = sym (mul-0-r (⟦ t ⟧t ρ))
mulTermDistr t (t′ ∷ v) ρ =
  ⟦ mulTerm t t′ ⟧t ρ + ⟦ map (mulTerm t) v ⟧n ρ
    ≡⟨ cong₂ _+_ (mulTerm-sound t t′ ρ) (mulTermDistr t v ρ) ⟩
  ⟦ t ⟧t ρ * ⟦ t′ ⟧t ρ + ⟦ t ⟧t ρ * ⟦ v ⟧n ρ
    ≡⟨ mul-distr-l (⟦ t ⟧t ρ) _ _ ⟩ʳ
  ⟦ t ⟧t ρ * ⟦ t′ ∷ v ⟧n ρ ∎

⟨*⟩-sound : ∀ v₁ v₂ (ρ : Env) → ⟦ v₁ *nf v₂ ⟧n ρ ≡ ⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ
⟨*⟩-sound [] v₂ ρ = refl
⟨*⟩-sound (t ∷ v₁) v₂ ρ =
  ⟦ map (mulTerm t) v₂ +nf (v₁ *nf v₂) ⟧n ρ
    ≡⟨ ⟨+⟩-sound (map (mulTerm t) v₂) (v₁ *nf v₂) ρ ⟩
  ⟦ map (mulTerm t) v₂ ⟧n ρ + ⟦ v₁ *nf v₂ ⟧n ρ
    ≡⟨ cong (_+_ (⟦ map (mulTerm t) v₂ ⟧n ρ)) (⟨*⟩-sound v₁ v₂ ρ) ⟩
  ⟦ map (mulTerm t) v₂ ⟧n ρ + ⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ
    ≡⟨ cong (flip _+_ (⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ)) (mulTermDistr t v₂ ρ) ⟩
  ⟦ t ⟧t ρ * ⟦ v₂ ⟧n ρ + ⟦ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ
    ≡⟨ mul-distr-r (⟦ t ⟧t ρ) _ _ ⟩ʳ
  ⟦ t ∷ v₁ ⟧n ρ * ⟦ v₂ ⟧n ρ ∎

sound : ∀ e (ρ : Env) → ⟦ e ⟧e ρ ≡ ⟦ norm e ⟧n ρ
sound (var x) ρ =
  ρ x     ≡⟨ mul-1-r (ρ x) ⟩ʳ
  ρ x * 1 ≡⟨ add-0-r (ρ x * 1) ⟩ʳ
  (ρ x * 1) + 0 ∎
sound ⟨0⟩ ρ = refl
sound ⟨1⟩ ρ = refl
sound (e ⟨+⟩ e₁) ρ =
  ⟦ e ⟧e ρ + ⟦ e₁ ⟧e ρ
    ≡⟨ cong₂ _+_ (sound e ρ) (sound e₁ ρ) ⟩
  ⟦ norm e ⟧n ρ + ⟦ norm e₁ ⟧n ρ
    ≡⟨ ⟨+⟩-sound (norm e) (norm e₁) ρ ⟩ʳ
  ⟦ norm e +nf norm e₁ ⟧n ρ ∎
sound (e ⟨*⟩ e₁) ρ =
  ⟦ e ⟧e ρ * ⟦ e₁ ⟧e ρ
    ≡⟨ cong₂ _*_ (sound e ρ) (sound e₁ ρ) ⟩
  ⟦ norm e ⟧n ρ * ⟦ norm e₁ ⟧n ρ
    ≡⟨ ⟨*⟩-sound (norm e) (norm e₁) ρ ⟩ʳ
  ⟦ norm e *nf norm e₁ ⟧n ρ ∎

private
  EqNF : Eq NF
  EqNF = EqList {{EqA = EqPair {{EqB = EqList}} }}

proof : ∀ e₁ e₂ ρ → Maybe (⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ)
proof e₁ e₂ ρ with norm e₁ == norm e₂
proof e₁ e₂ ρ    | no  _    = nothing
proof e₁ e₂ ρ    | yes nfeq =
  just $ ⟦ e₁      ⟧e ρ ≡⟨ sound e₁ ρ ⟩
         ⟦ norm e₁ ⟧n ρ ≡⟨ cong (λ n → ⟦ n ⟧n ρ) nfeq ⟩
         ⟦ norm e₂ ⟧n ρ ≡⟨ sound e₂ ρ ⟩ʳ
         ⟦ e₂      ⟧e ρ ∎

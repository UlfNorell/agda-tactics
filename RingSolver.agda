
module RingSolver where

open import Prelude
open import Ring as R
open import RingSolver.Exp
open import RingSolver.NF
open import RingSolver.Lemmas

open import EqReasoning

module _ {A : Set} {{RingA : Ring A}} where
  open Ring RingA

  mulTerm-sound : ∀ t t′ (ρ : Env A) →
                  ⟦ mulTerm t t′ ⟧t ρ ≡ ⟦ t ⟧t ρ ⊛ ⟦ t′ ⟧t ρ
  mulTerm-sound (a , x) (b , y) ρ =
    (a * b) #* #prod (map ρ (x ++ y))
      ≡⟨ cong (_#*_ (a * b)) (cong #prod (map++ ρ x y) => #prod++ (map ρ x) (map ρ y)) ⟩
    (a * b) #* (#prod (map ρ x) ⊛ #prod (map ρ y))
      ≡⟨ *#* a b _ ⟩
    a #* (b #* (#prod (map ρ x) ⊛ #prod (map ρ y)))
      ≡⟨ cong (_#*_ a) (#*-commute b _ _) ⟩
    a #* (#prod (map ρ x) ⊛ b #* #prod (map ρ y))
      ≡⟨ #*-assoc a _ _ ⟩
    a #* #prod (map ρ x) ⊛ b #* #prod (map ρ y) ∎

  mulTermDistr : ∀ t v (ρ : Env A) → ⟦ map (mulTerm t) v ⟧n ρ ≡ ⟦ t ⟧t ρ ⊛ ⟦ v ⟧n ρ
  mulTermDistr t [] ρ = sym (zero-z-r _)
  mulTermDistr t (t′ ∷ v) ρ =
    ⟦ mulTerm t t′ ⟧t ρ ⊕ ⟦ map (mulTerm t) v ⟧n ρ
      ≡⟨ cong₂ _⊕_ (mulTerm-sound t t′ ρ) (mulTermDistr t v ρ) ⟩
    ⟦ t ⟧t ρ ⊛ ⟦ t′ ⟧t ρ ⊕ ⟦ t ⟧t ρ ⊛ ⟦ v ⟧n ρ
      ≡⟨ mul-distr-l _ _ _ ⟩ʳ
    ⟦ t ⟧t ρ ⊛ ⟦ t′ ∷ v ⟧n ρ ∎

  ⟨*⟩-sound : ∀ v₁ v₂ (ρ : Env A) → ⟦ v₁ *nf v₂ ⟧n ρ ≡ ⟦ v₁ ⟧n ρ ⊛ ⟦ v₂ ⟧n ρ
  ⟨*⟩-sound [] v₂ ρ = sym (zero-z-l _)
  ⟨*⟩-sound (t ∷ v₁) v₂ ρ =
    ⟦ map (mulTerm t) v₂ +nf (v₁ *nf v₂) ⟧n ρ
      ≡⟨ ⟨+⟩-sound (map (mulTerm t) v₂) _ ρ ⟩
    ⟦ map (mulTerm t) v₂ ⟧n ρ ⊕ ⟦ v₁ *nf v₂ ⟧n ρ
      ≡⟨ cong (_⊕_ (⟦ map (mulTerm t) v₂ ⟧n ρ)) (⟨*⟩-sound v₁ v₂ ρ) ⟩
    ⟦ map (mulTerm t) v₂ ⟧n ρ ⊕ ⟦ v₁ ⟧n ρ ⊛ ⟦ v₂ ⟧n ρ
      ≡⟨ cong (flip _⊕_ (⟦ v₁ ⟧n ρ ⊛ ⟦ v₂ ⟧n ρ)) (mulTermDistr t v₂ ρ) ⟩
    ⟦ t ⟧t ρ ⊛ ⟦ v₂ ⟧n ρ ⊕ ⟦ v₁ ⟧n ρ ⊛ ⟦ v₂ ⟧n ρ
      ≡⟨ mul-distr-r _ _ _ ⟩ʳ
    ⟦ t ∷ v₁ ⟧n ρ ⊛ ⟦ v₂ ⟧n ρ ∎

  sound : ∀ e (ρ : Env A) → ⟦ e ⟧e ρ ≡ ⟦ norm e ⟧n ρ
  sound (var x) ρ =
    ρ x
      ≡⟨ one-id-r _ ⟩ʳ
    ρ x ⊛ #1
      ≡⟨ zero-id-r _ ⟩ʳ
    (ρ x ⊛ #1) ⊕ #0
      ≡⟨ zero-id-r _ ⟩ʳ
    ((ρ x ⊛ #1) ⊕ #0) ⊕ #0 ∎
  sound ⟨0⟩ ρ = refl
  sound ⟨1⟩ ρ =
    #1        ≡⟨ zero-id-r _ ⟩ʳ
    #1 ⊕ #0  ≡⟨ zero-id-r _ ⟩ʳ
    (#1 ⊕ #0) ⊕ #0 ∎
  sound (e ⟨+⟩ e₁) ρ =
    ⟦ e ⟧e ρ ⊕ ⟦ e₁ ⟧e ρ
      ≡⟨ cong₂ _⊕_ (sound e ρ) (sound e₁ ρ) ⟩
    ⟦ norm e ⟧n ρ ⊕ ⟦ norm e₁ ⟧n ρ
      ≡⟨ ⟨+⟩-sound (norm e) (norm e₁) ρ ⟩ʳ
    ⟦ norm e +nf norm e₁ ⟧n ρ ∎
  sound (e ⟨*⟩ e₁) ρ =
    ⟦ e ⟧e ρ ⊛ ⟦ e₁ ⟧e ρ
      ≡⟨ cong₂ _⊛_ (sound e ρ) (sound e₁ ρ) ⟩
    ⟦ norm e ⟧n ρ ⊛ ⟦ norm e₁ ⟧n ρ
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

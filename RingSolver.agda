
module RingSolver where

open import Prelude
open import RingSolver.Exp
open import RingSolver.NF
open import RingSolver.Lemmas
open import Data.Nat.Lemmas

open import EqReasoning

private
  EqNF : Eq NF
  EqNF = EqList {{EqA = EqPair {{EqB = EqList}} }}

liftNFEq : ∀ e₁ e₂ ρ → ⟦ norm e₁ ⟧n ρ ≡ ⟦ norm e₂ ⟧n ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
liftNFEq e₁ e₂ ρ H =
  ⟦ e₁      ⟧e ρ ≡⟨ sound e₁ ρ ⟩
  ⟦ norm e₁ ⟧n ρ ≡⟨ H ⟩
  ⟦ norm e₂ ⟧n ρ ≡⟨ sound e₂ ρ ⟩ʳ
  ⟦ e₂      ⟧e ρ ∎

simpl : ∀ e₁ e₂ ρ → NFEqS (cancel (norm e₁) (norm e₂)) ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
simpl e₁ e₂ ρ H = liftNFEq e₁ e₂ ρ (cancel-sound (norm e₁) (norm e₂) ρ H)

proof : ∀ e₁ e₂ ρ → Maybe (⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ)
proof e₁ e₂ ρ with norm e₁ == norm e₂
proof e₁ e₂ ρ    | no  _    = nothing
proof e₁ e₂ ρ    | yes nfeq = just (liftNFEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧n ρ) nfeq))

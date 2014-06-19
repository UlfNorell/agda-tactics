
module RingSolver.Exp where

open import Prelude

Var = Nat

Env : Set
Env = Var → Nat

infixl 6 _⟨+⟩_
infixl 7 _⟨*⟩_
data Exp : Set where
  var      : Var → Exp
  ⟨0⟩ ⟨1⟩   : Exp
  _⟨+⟩_ _⟨*⟩_ : Exp → Exp → Exp

⟦_⟧e : Exp → Env → Nat
⟦ var x ⟧e   ρ = ρ x
⟦ ⟨0⟩ ⟧e      ρ = 0
⟦ ⟨1⟩ ⟧e      ρ = 1
⟦ e₁ ⟨+⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ + ⟦ e₂ ⟧e ρ
⟦ e₁ ⟨*⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ * ⟦ e₂ ⟧e ρ


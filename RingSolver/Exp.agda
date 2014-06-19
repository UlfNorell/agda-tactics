
module RingSolver.Exp where

open import Prelude
open import Ring as R

Var = Nat

Env : Set → Set
Env A = Var → A

infixl 6 _⟨+⟩_
infixl 7 _⟨*⟩_
data Exp : Set where
  var      : Var → Exp
  ⟨0⟩ ⟨1⟩   : Exp
  _⟨+⟩_ _⟨*⟩_ : Exp → Exp → Exp

module _ {A : Set} {{RingA : Ring A}} where
  open Ring RingA

  ⟦_⟧e : Exp → Env A → A
  ⟦ var x ⟧e   ρ = ρ x
  ⟦ ⟨0⟩ ⟧e      ρ = #0
  ⟦ ⟨1⟩ ⟧e      ρ = #1
  ⟦ e₁ ⟨+⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ ⊕ ⟦ e₂ ⟧e ρ
  ⟦ e₁ ⟨*⟩ e₂ ⟧e ρ = ⟦ e₁ ⟧e ρ ⊛ ⟦ e₂ ⟧e ρ


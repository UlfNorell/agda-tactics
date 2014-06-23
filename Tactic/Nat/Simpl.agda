
module Tactic.Nat.Simpl where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)
open import Data.Reflect
open import Data.Reflect.Quote

open import Tactic.Nat.Reflect
open import Tactic.Nat.NF hiding (Term)
open import Tactic.Nat.Exp
open import Tactic.Nat.Auto
open import Tactic.Nat.Auto.Lemmas
open import Tactic.Nat.Simpl.Lemmas

ExpEq : Exp × Exp → Env → Set
ExpEq (e₁ , e₂) ρ = ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ

CancelEq : Exp × Exp → Env → Set
CancelEq (e₁ , e₂) ρ = NFEqS (cancel (norm e₁) (norm e₂)) ρ

simplify : ∀ eq ρ → CancelEq eq ρ → ExpEq eq ρ
simplify (e₁ , e₂) ρ H = liftNFEq e₁ e₂ ρ (cancel-sound (norm e₁) (norm e₂) ρ H)


simpl : Term → Term
simpl t =
  case termToExp t of
  λ { nothing →
      def (quote getProof)
        $ vArg (con (quote nothing) [])
        ∷ vArg (def (quote invalidGoal) $ vArg (stripImplicit t) ∷ [])
        ∷ []
    ; (just ((e₁ , e₂) , Γ)) →
      def (quote simplify) ( vArg (con (quote _,_) (vArg (` e₁) ∷ vArg (` e₂) ∷ []))
                           ∷ vArg (quotedEnv Γ)
                           ∷ [])
    }
        ∷ []
    }

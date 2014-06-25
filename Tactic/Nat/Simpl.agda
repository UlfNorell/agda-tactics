
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

postulate
  cancel-complete′ : ∀ a b nf₁ nf₂ ρ →
                     a + ⟦ nf₁ ⟧n ρ ≡ b + ⟦ nf₂ ⟧n ρ →
                     a + ⟦ fst (cancel nf₁ nf₂) ⟧n ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧n ρ
-- cancel-complete′ a b nf₁ nf₂ ρ H = {!!}

cancel-complete : ∀ nf₁ nf₂ ρ → NFEq (nf₁ , nf₂) ρ → NFEqS (cancel nf₁ nf₂) ρ
cancel-complete nf₁ nf₂ ρ H
  rewrite cong (λ p → NFEqS p ρ) (eta (cancel nf₁ nf₂))
        | ns-sound (fst (cancel nf₁ nf₂)) ρ
        | ns-sound (snd (cancel nf₁ nf₂)) ρ
        = cancel-complete′ 0 0 nf₁ nf₂ ρ H


ExpEq : Exp × Exp → Env → Set
ExpEq (e₁ , e₂) ρ = ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ

CancelEq : Exp × Exp → Env → Set
CancelEq (e₁ , e₂) ρ = NFEqS (cancel (norm e₁) (norm e₂)) ρ

⟦_⟧h : List (Exp × Exp) → Env → Set
⟦ [] ⟧h ρ = ⊥
⟦ h ∷ [] ⟧h ρ = ExpEq h ρ
⟦ h ∷ g  ⟧h ρ = ExpEq h ρ → ⟦ g ⟧h ρ

⟦_⟧hs : List (Exp × Exp) → Env → Set
⟦ [] ⟧hs ρ = ⊥
⟦ h ∷ [] ⟧hs ρ = CancelEq h ρ
⟦ h ∷ g  ⟧hs ρ = CancelEq h ρ → ⟦ g ⟧hs ρ

simplify : ∀ eq ρ → CancelEq eq ρ → ExpEq eq ρ
simplify (e₁ , e₂) ρ H = liftNFEq e₁ e₂ ρ (cancel-sound (norm e₁) (norm e₂) ρ H)

complicate : ∀ eq ρ → ExpEq eq ρ → CancelEq eq ρ
complicate (e₁ , e₂) ρ H =
  cancel-complete (norm e₁) (norm e₂) ρ
  (unliftNFEq e₁ e₂ ρ H)

-- simpl : Term → Term
-- simpl t =
--   case termToExp t of
--   λ { nothing →
--       def (quote getProof)
--         $ vArg (con (quote nothing) [])
--         ∷ vArg (def (quote invalidGoal) $ vArg (stripImplicit t) ∷ [])
--         ∷ []
--     ; (just ((e₁ , e₂) , Γ)) →
--       def (quote simplify) ( vArg (con (quote _,_) (vArg (` e₁) ∷ vArg (` e₂) ∷ []))
--                            ∷ vArg (quotedEnv Γ)
--                            ∷ [])
--     }

simplifyH : ∀ goal ρ → ⟦ goal ⟧hs ρ → ⟦ goal ⟧h ρ
simplifyH []            ρ ()
simplifyH (h ∷ [])     ρ H = simplify h ρ H
simplifyH (h ∷ h₂ ∷ g) ρ H = λ H₁ → simplifyH (h₂ ∷ g) ρ $ H (complicate h ρ H₁)

QGoal : Quotable (List (Exp × Exp))
QGoal = QuotableList {{QuotableSigma {{QuotableB = ⋯}}}}

simpl : Term → Term
simpl t =
  case termToHyps t of
  λ { nothing →
      def (quote getProof)
        $ vArg (con (quote nothing) [])
        ∷ vArg (def (quote invalidGoal) $ vArg (stripImplicit t) ∷ [])
        ∷ []
    ; (just (goal , Γ)) →
      def (quote simplifyH) ( vArg (` goal)
                            ∷ vArg (quotedEnv Γ)
                            ∷ [])
    }


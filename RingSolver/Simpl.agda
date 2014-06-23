
module RingSolver.Simpl where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)
open import Data.Reflect
open import Data.Reflect.Quote

open import RingSolver.Reflect
open import RingSolver.NF hiding (Term)
open import RingSolver.Exp
open import RingSolver.Auto
open import RingSolver.Auto.Lemmas
open import RingSolver.Simpl.Lemmas

simpl : ∀ e₁ e₂ ρ → NFEqS (cancel (norm e₁) (norm e₂)) ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
simpl e₁ e₂ ρ H = liftNFEq e₁ e₂ ρ (cancel-sound (norm e₁) (norm e₂) ρ H)

simplify : Term → Term
simplify t =
  case termToExp t of
  λ { nothing →
      def (quote getProof)
        $ vArg (con (quote nothing) [])
        ∷ vArg (def (quote invalidGoal) $ vArg (stripImplicit t) ∷ [])
        ∷ []
    ; (just ((e₁ , e₂) , Γ)) →
      def (quote _∘_)
        $ vArg (def (quote safeEqual) [])
        ∷ vArg (def (quote simpl) ( vArg (` e₁)
                                  ∷ vArg (` e₂)
                                  ∷ vArg (quotedEnv Γ)
                                  ∷ []))
        ∷ []
    }

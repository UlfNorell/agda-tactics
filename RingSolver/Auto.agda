
module RingSolver.Auto where

open import Prelude
open import Prelude.Equality.Unsafe
open import Data.Reflect
open import Data.Reflect.Quote

open import EqReasoning
open import RingSolver.NF hiding (Term)
open import RingSolver.Exp
open import RingSolver.Reflect
open import RingSolver.Auto.Lemmas

private
  EqNF : Eq NF
  EqNF = EqList {{EqA = EqPair {{EqB = EqList}} }}

liftNFEq : ∀ e₁ e₂ ρ → ⟦ norm e₁ ⟧n ρ ≡ ⟦ norm e₂ ⟧n ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
liftNFEq e₁ e₂ ρ H =
  ⟦ e₁      ⟧e ρ ≡⟨ sound e₁ ρ ⟩
  ⟦ norm e₁ ⟧n ρ ≡⟨ H ⟩
  ⟦ norm e₂ ⟧n ρ ≡⟨ sound e₂ ρ ⟩ʳ
  ⟦ e₂      ⟧e ρ ∎

proof : ∀ e₁ e₂ ρ → Maybe (⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ)
proof e₁ e₂ ρ with norm e₁ == norm e₂
proof e₁ e₂ ρ    | no  _    = nothing
proof e₁ e₂ ρ    | yes nfeq = just (liftNFEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧n ρ) nfeq))

prove : Term → Term
prove t =
  case termToExp t of
  λ { nothing →
      def (quote getProof)
        $ vArg (con (quote nothing) [])
        ∷ vArg (def (quote invalidGoal) $ vArg (stripImplicit t) ∷ [])
        ∷ []
    ; (just ((e₁ , e₂) , Γ)) →
      def (quote safeEqual)
        $ vArg (def (quote getProof)
          $ vArg (def (quote proof) ( vArg (` e₁)
                                    ∷ vArg (` e₂)
                                    ∷ vArg (quotedEnv Γ)
                                    ∷ []))
          ∷ vArg (def (quote cantProve) $ vArg (stripImplicit t) ∷ [])
          ∷ [])
        ∷ []
    }

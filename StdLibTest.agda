
open import Data.Nat as Nat
open import Data.Nat.Properties
open SemiringSolver
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ)
import Data.Fin.Properties as Fin
open import Induction.Nat
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

------------------------------------------------------------------------
-- Some boring lemmas

lem₁ : ∀ n → _
lem₁ = solve 1 (λ n → con 1 :+ n  :=  con 1 :+ (n :+ con 0)) refl

lem₂ : ∀ x y → _
lem₂ = solve 2 (λ x y → (x :+ y) :^ 3 := x :^ 3 :+ con 3 :* x :^ 2 :* y :+ con 3 :* x :* y :^ 2 :+ y :^ 3) refl

lem₃ : ∀ x y → _
lem₃ = solve 2 (λ x y → (x :+ y) :^ 9 := (x :+ y) :^ 8 :* (x :+ y)) refl

-- lem₃ : ∀ x y → _
-- lem₃ = solve 2 (λ x y → (x :+ y) :^ 16 := (x :+ y) :^ 15 :* (x :+ y)) refl

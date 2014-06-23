
module Tactic.Nat.Test where

open import Prelude
open import Data.Reflect

open import Tactic.Nat
open import Tactic.Nat.Exp
open import Tactic.Nat.NF hiding (Term)
open import Tactic.Nat.Reflect

infixr 8 _^_
_^_ : Nat → Nat → Nat
x ^ zero  = 1
x ^ suc n = x ^ n * x

normGoal : Term → Maybe (NF × NF)
normGoal v = (norm *** norm) ∘ fst <$> termToExp v

simple : ∀ n → n * n + n ≡ (n + 1) * n
simple n = quoteGoal g in unquote (prove g)

test₁ : ∀ n m → n + 3 * m + (20 + n) * n ≡ m + 21 * n + (m + n * n + m)
test₁ n m = quoteGoal g in unquote (prove g)

test₂ : ∀ x y → (x + y) ^ 3 ≡ x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3
test₂ x y = quoteGoal g in unquote (prove g)

test₃ : ∀ x y → (x + y) ^ 9 ≡ (x + y) * (x + y) ^ 8
test₃ x y = quoteGoal g in unquote (prove g)

-- test₄ : ∀ x y → (x + y) ^ 16 ≡ (x + y) * (x + y) ^ 15
-- test₄ x y = quoteGoal g in unquote (prove g)

-- Need quoted literals to do this really efficiently.
-- test₅ : ∀ x → x * 400 + 2 ≡ 2 * (x * 200 + 1)
-- test₅ x = quoteGoal g in unquote (prove g)

-- foo : (x y : Bool) → x ≡ (y && false)
-- foo x y = quoteGoal g in unquote (prove g)

-- bad : ∀ x y → x + y ≡ x * 2
-- bad x y = quoteGoal g in unquote (prove g)

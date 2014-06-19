
module RingSolver.Test where

open import Prelude
open import Data.Reflect

open import RingSolver
open import RingSolver.Exp
open import RingSolver.NF hiding (Term)
open import RingSolver.Reflect

infixr 8 _^_
_^_ : Nat → Nat → Nat
x ^ zero  = 1
x ^ suc n = x ^ n * x

normGoal : Term → Maybe (NF × NF)
normGoal v = (norm *** norm) ∘ fst <$> termToExp v

simple : 1 ≡ 1
simple = quoteGoal g in unquote (prove g)

test₁ : ∀ n m → n + 3 * m + (20 + n) * n ≡ m + 21 * n + (m + n * n + m)
test₁ n m = quoteGoal g in unquote (prove g)

test₂ : ∀ x y → (x + y) ^ 3 ≡ x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3
test₂ x y = quoteGoal g in unquote (prove g)

test₃ : ∀ x y → (x + y) ^ 6 ≡ (x + y) * (x + y) ^ 5
test₃ x y = quoteGoal g in unquote (prove g)

bad : ∀ x y → x + y ≡ 2 * x
bad x y = quoteGoal g in unquote (prove g)

open import Data.Reflect

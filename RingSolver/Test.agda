
module RingSolver.Test where

open import Prelude
open import Data.Reflect

open import RingSolver
open import RingSolver.Exp
open import RingSolver.NF
open import RingSolver.Reflect
open import Ring as R

infixr 8 _^_
_^_ : Nat → Nat → Nat
x ^ zero  = 1
x ^ suc n = x ^ n * x

test₁ : ∀ n m → n + 3 * m + (20 + n) * n ≡ m + 21 * n + (m + n * n + m)
test₁ n m = quoteGoal g in unquote (prove g)

test₂ : ∀ x y → (x + y) ^ 3 ≡ x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3
test₂ x y = quoteGoal g in {!(norm ***′ norm) ∘ fst <$> termToExp g!}

open import Data.Reflect


module DivMod where

open import Prelude
open import RingSolver
open import EqReasoning

sum : List Nat → Nat
sum = foldr _+_ 0

downFrom : Nat → List Nat
downFrom zero = []
downFrom (suc n) = suc n ∷ downFrom n

sumSquare : Nat → Nat
sumSquare n = sum (map (λ x → x * x) (downFrom n))

open import Data.Reflect

bla : ∀ n → sumSquare n * 6 ≡ (2 * n + 1) * (n + 1) * n
bla zero = refl
bla (suc n) =
  quoteGoal g in unquote (simplify g)
  $ bla n ≡tr quoteGoal g in unquote (prove g)

data DivMod a b : Set where
  divModRes : ∀ q r → LessThan r b → q * b + r ≡ a → DivMod a b

-- modLessAux : ∀ a b → LessThan (modAux 0 b a b

modLess : ∀ a b → LessThan (a mod suc b) (suc b)
modLess a b = {!!}
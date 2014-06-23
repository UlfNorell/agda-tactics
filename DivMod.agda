
module DivMod where

open import Prelude
open import Tactic.Nat
open import EqReasoning

downFrom : Nat → List Nat
downFrom zero = []
downFrom (suc n) = suc n ∷ downFrom n

sumSquare : Nat → Nat
sumSquare n = sum (map (λ x → x * x) (downFrom n))

open import Data.Reflect

bla : ∀ n → sumSquare n * 6 ≡ (2 * n + 1) * (n + 1) * n
bla zero = refl
bla (suc n) =
  quoteGoal g in unquote (simpl g)
  $ bla n ≡tr quoteGoal g in unquote (auto g)

data DivMod a b : Set where
  divModRes : ∀ q r → LessThan r b → q * b + r ≡ a → DivMod a b

-- divAux k m n j = k + div (max 0 $ n + m - j) (m + 1)
-- modAux k m n j | n > j     = mod (n - j - 1) (m + 1)
--                | otherwise = k + n

divAux' : Nat → Nat → Nat → Nat → Nat
divAux' k m  zero    j      = k
divAux' k m (suc n)  zero   = divAux' (suc k) m n m
divAux' k m (suc n) (suc j) = divAux' k m n j

modAux' : Nat → Nat → Nat → Nat → Nat
modAux' k m  zero    j      = k
modAux' k m (suc n)  zero   = modAux' 0 m n m
modAux' k m (suc n) (suc j) = modAux' (suc k) m n j

lemModAux : ∀ k m n j → LessThan m n → k + j ≡ m → modAux k m n j ≡ modAux k m (n - suc m) m
lemModAux k m zero j _ _ = refl
lemModAux k m (suc n) zero (diffP d lt) eq = {!lemModAux 0 m n m!}
lemModAux k m (suc n) (suc j) lt eq = {!lemModAux k m n j!}

-- modLessAux : ∀ k m n j → LessThan (k + j) (suc m) → LessThan (modAux k m n j) (suc m)
-- modLessAux k m zero j (diffP d lt) =
--   diffP (j + d) $ lt ≡tr quoteGoal g in unquote (auto g)
-- modLessAux k m (suc n) zero _ =
--   modLessAux 0 m n m
--   $ diffP 0 $ quoteGoal g in unquote (auto g)
-- modLessAux k m (suc n) (suc j) (diffP d lt) =
--   modLessAux (suc k) m n j
--   $ diffP d $ lt ≡tr quoteGoal g in unquote (auto g)

-- modLess : ∀ a b → LessThan (a mod suc b) (suc b)
-- modLess a b = modLessAux 0 b a b (diffP 0 (quoteGoal g in unquote (auto g)))

-- divmod-spec : ∀ a b′ → let b = suc b′ in
--                 a div b * b + a mod b ≡ a
-- divmod-spec a b = {!!}

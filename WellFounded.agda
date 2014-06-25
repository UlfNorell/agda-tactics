
module WellFounded where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)
open import Tactic.Nat
open import EqReasoning

data Acc {A : Set} {{OrdA : Ord A}} (x : A) : Set where
  acc : (∀ y → LessThan y x → Acc y) → Acc x

accSuc : {y : Nat} → Acc y → Acc (Nat.suc y)
accSuc (acc f) = acc λ { ._ (diff zero) → acc f
                       ; z (diffP (suc j) eq) → f z (diffP j (use eq (tactic assumed)))
                       }

wfNat′ : ∀ n y → LessNat y n → Acc y
wfNat′  n  zero    lt      = acc λ { z (diffP _ ()) }
wfNat′ ._ (suc y) (diff k) =
  accSuc (wfNat′ (k + suc y) y (diffP k (tactic auto))) 

wfNat : (n : Nat) → Acc n
wfNat n = acc (wfNat′ n)

lemCancelMinus : ∀ b → b - b ≡ 0
lemCancelMinus zero    = refl
lemCancelMinus (suc b) = lemCancelMinus b

lemPlusMinus : ∀ a b → a + b - b ≡ a
lemPlusMinus zero b = lemCancelMinus b
lemPlusMinus (suc a) zero = tactic auto
lemPlusMinus (suc a) (suc b) =
  -- Want cong tactic for this!
  let lem : a + suc b - b ≡ suc a + b - b
      lem = cong (λ z → z - b) (tactic auto)
  in lem ≡tr lemPlusMinus (suc a) b

lem : ∀ a b → LessThan a b → b ≡ a + (b - a)
lem a .(suc (k + a)) (diff k) rewrite lemPlusMinus (suc k) a = tactic auto

lemLess : ∀ a b → LessThan (suc a) b → LessThan (b - suc a) b
lemLess a b lt = diffP a $ safeEqual (lem (suc a) b lt)

example′ : (n : Nat) → Acc n → Nat
example′ n (acc wf) =
  case compare n 100 of
  λ { (greater gt) → example′ (n - 100) (wf _ (lemLess _ _ gt))
    ; _ → n }

example : Nat → Nat
example n = example′ n (wfNat n)

-- Benchmark: example 10051
--    12.5s
--    11.0s  better lessThan proof in example
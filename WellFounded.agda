{-# OPTIONS -v profile.interactive:10 #-}
module WellFounded where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual; unsafeEqual)
open import Control.WellFounded
open import Data.List
open import Tactic.Nat
open import EqReasoning

fix : {A : Set} {B : A → Set} {{OrdA : Ord A}} →
      (∀ x → (∀ y → LessThan y x → B y) → B x) →
      ∀ x → Acc LessThan x → B x
fix f x (acc wf) = f x (λ y lt → fix f y (wf y lt))

-- Test case --

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

private
  lem : ∀ a b → LessThan a b → b ≡ a + (b - a)
  lem a .(suc (k + a)) (diff! k) rewrite lemPlusMinus (suc k) a = tactic auto

lemLess : ∀ a b → LessThan (suc a) b → LessThan (b - suc a) b
lemLess a b lt = diff a $ safeEqual (lem (suc a) b lt)

example′ : (n : Nat) → Acc LessThan n → Nat
example′ n (acc wf) =
  case compare n 100 of
  λ { (greater gt) → example′ (n - 100) (wf _ (lemLess _ _ gt))
    ; _ → n }

example : Nat → Nat
example n = example′ n (wfNat n)

example₂ : Nat → Nat
example₂ n =
  fix (λ n ex →
    case compare n 100 of
    λ { (greater gt) → ex (n - 100) (lemLess _ _ gt)
      ; _ → n }) n (wfNat n)

{-# NO_TERMINATION_CHECK #-}
reference : Nat → Nat
reference n =
  case compare n 100 of
  λ { (greater _) → reference (n - 100)
    ; _ -> n }

{-# NO_TERMINATION_CHECK #-}
reference₂ : Nat → Nat
reference₂ n =
  case lessNat 100 n of
  λ { true → reference (n - 100)
    ; _ -> n }

-- Benchmark: example 10,051
--    12.5s
--    11.0s  better lessThan proof in example
--   < 1.0s
--     8.0s  100,051
--     7.3s  got rid of wfNat′
--     4.8s  got rid of accSuc
--     2.4s  cheating the first 10,000,000 iterations (as fast as the reference implementation)

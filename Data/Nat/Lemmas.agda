
module Data.Nat.Lemmas where

open import Prelude

add-0-r : ∀ n → n + 0 ≡ n
add-0-r  0 = refl
add-0-r (suc n) rewrite add-0-r n = refl

postulate
  mul-1-r     : ∀ x → x * 1 ≡ x
  mul-0-r     : ∀ x → x * 0 ≡ 0
  add-commute : ∀ x y → x + y ≡ y + x
  add-assoc   : ∀ x y z → x + (y + z) ≡ x + y + z
  mul-assoc   : ∀ x y z → x * (y * z) ≡ x * y * z
  mul-commute : ∀ x y → x * y ≡ y * x
  mul-distr-r : ∀ x y z → (x + y) * z ≡ x * z + y * z
  mul-distr-l : ∀ x y z → x * (y + z) ≡ x * y + x * z


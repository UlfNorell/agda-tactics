
module Ring where

open import Prelude

record Ring (A : Set) : Set where
  infixl 6 _⊕_
  infixl 7 _⊛_
  field
    #0 : A
    #1 : A
    _⊕_ : A → A → A
    _⊛_ : A → A → A
    zero-id-l : ∀ x → #0 ⊕ x ≡ x
    zero-id-r : ∀ x → x ⊕ #0 ≡ x
    one-id-l : ∀ x → #1 ⊛ x ≡ x
    one-id-r : ∀ x → x ⊛ #1 ≡ x
    zero-z-l : ∀ x → #0 ⊛ x ≡ #0
    zero-z-r : ∀ x → x ⊛ #0 ≡ #0
    plus-commute : ∀ x y → x ⊕ y ≡ y ⊕ x
    plus-assoc : ∀ x y z → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
    mul-assoc : ∀ x y z → x ⊛ (y ⊛ z) ≡ (x ⊛ y) ⊛ z
    mul-distr-l : ∀ x y z → x ⊛ (y ⊕ z) ≡ (x ⊛ y) ⊕ (x ⊛ z)
    mul-distr-r : ∀ x y z → (x ⊕ y) ⊛ z ≡ (x ⊛ z) ⊕ (y ⊛ z)

module _ {A : Set} {{RingA : Ring A}} where

  open Ring RingA

  #sum : List A → A
  #sum = foldr _⊕_ #0

  #prod : List A → A
  #prod = foldr _⊛_ #1

  _#*_ : Nat → A → A
  n #* x = #sum (replicate n x)

-- Nat ring --

n+0=n : ∀ n → n + 0 ≡ n
n+0=n  zero = refl
n+0=n (suc n) rewrite n+0=n n = refl

postulate
  x*1=1 : ∀ x → x * 1 ≡ x
  x*0=0 : ∀ x → x * 0 ≡ 0
  +commute : ∀ x y → x + y ≡ y + x
  +assoc : ∀ x y z → x + (y + z) ≡ x + y + z
  *assoc : ∀ x y z → x * (y * z) ≡ x * y * z
  *distr-r : ∀ x y z → (x + y) * z ≡ x * z + y * z
  *distr-l : ∀ x y z → x * (y + z) ≡ x * y + x * z

RingNat : Ring Nat
RingNat =
  record
    { #0 = 0
    ; #1 = 1
    ; _⊕_ = _+_
    ; _⊛_ = _*_
    ; zero-id-l = λ _ → refl
    ; zero-id-r = n+0=n
    ; one-id-l = λ _ → refl
    ; one-id-r = x*1=1
    ; zero-z-l = λ _ → refl
    ; zero-z-r = x*0=0
    ; plus-commute = +commute
    ; plus-assoc = +assoc
    ; mul-assoc = *assoc
    ; mul-distr-l = *distr-l
    ; mul-distr-r = *distr-r
    }

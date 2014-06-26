
module DivMod where

open import Prelude
open import Prelude.Equality.Unsafe using (safeEqual)
open import Tactic.Nat
open import Tactic.Nat.Reflect
open import Tactic.Nat.Exp
open import EqReasoning
open import WellFounded
open import Data.Nat.Lemmas

lemModAux : ∀ k m n j → LessThan j n → modAux k m n j ≡ modAux 0 m (n - suc j) m
lemModAux k m zero j (diffP _ ())
lemModAux k m (suc n) zero lt = refl
lemModAux k m (suc n) (suc j) (diffP d eq) =
  lemModAux (suc k) m n j
  $ diffP d $ use eq $ tactic assumed

lemDivAux : ∀ k m n j → LessThan j n → divAux k m n j ≡ divAux (suc k) m (n - suc j) m
lemDivAux k m zero j (diffP _ ())
lemDivAux k m (suc n) zero lt = refl
lemDivAux k m (suc n) (suc j) (diffP d eq) =
  lemDivAux k m n j
  $ diffP d $ use eq $ tactic assumed

modLessAux : ∀ k m n j → LessThan (k + j) (suc m) → LessThan (modAux k m n j) (suc m)
modLessAux k m zero j (diffP d lt) =
  diffP (j + d) $ lt ≡tr tactic auto
modLessAux k m (suc n) zero _ =
  modLessAux 0 m n m $ diffP 0 $ tactic auto
modLessAux k m (suc n) (suc j) (diffP d lt) =
  modLessAux (suc k) m n j
  $ diffP d $ use lt tactic assumed

LessThan′ : Nat → Nat → Set
LessThan′ a b = b ≡ b - suc a + suc a

toPrimed : ∀ {a b} → LessThan a b → LessThan′ a b
toPrimed {a = a} (diff k) rewrite lemPlusMinus k a = tactic auto

modLessAux′ : ∀ k m n j → LessThan (k + j) (suc m) → LessThan′ (modAux k m n j) (suc m)
modLessAux′ k m n j lt = toPrimed (modLessAux k m n j lt)

modLess : ∀ a b → LessThan (a mod suc b) (suc b)
modLess a b = diffP (b - a mod suc b) $ safeEqual $
              use (modLessAux′ 0 b a b (diffP 0 tactic auto))
                   tactic assumed

0≠1 : ∀ {a} {A : Set a} → 0 ≡ 1 → A
0≠1 ()

notLess1 : ∀ {a n} {A : Set a} → LessThan (suc n) 1 → A
notLess1 (diffP k eq) = 0≠1 (use eq tactic simpl | λ ())

lessSuc-inj : ∀ {a b} → LessNat (suc a) (suc b) → LessNat a b
lessSuc-inj (diffP j eq) = diffP j (use eq tactic assumed)

divAuxGt : ∀ k a b j → LessNat a (suc j) → divAux k b a j ≡ k
divAuxGt k  zero   b  j      lt = refl
divAuxGt k (suc a) b  zero   lt = notLess1 lt
divAuxGt k (suc a) b (suc j) lt = divAuxGt k a b j (lessSuc-inj lt)

modAuxGt : ∀ k a b j → LessNat a (suc j) → modAux k b a j ≡ k + a
modAuxGt k zero b j lt = tactic auto
modAuxGt k (suc a) b  zero   lt = notLess1 lt
modAuxGt k (suc a) b (suc j) lt = use (modAuxGt (suc k) a b j (lessSuc-inj lt)) tactic assumed

divmodAux : ∀ k a b → Acc a → divAux k b a b * suc b + modAux 0 b a b ≡ k * suc b + a
divmodAux k a b wf with compare b a
... | greater (diffP j p)
      rewrite divAuxGt k a b b (diffP (suc j) (cong suc p))
            | modAuxGt 0 a b b (diffP (suc j) (cong suc p)) = refl
divmodAux k a .a wf | equal refl
      rewrite divAuxGt k a a a (diff 0)
            | modAuxGt 0 a a a (diff 0) = refl
divmodAux k .(suc (j + b)) b (acc wf) | less (diff j)
  rewrite lemDivAux k b (suc (j + b)) b (diff j)
        | lemModAux 0 b (suc (j + b)) b (diff j)
        | lemPlusMinus j b
        = use (divmodAux (suc k) j b (wf j (diffP b (tactic auto))))
              (tactic assumed)

divmod-spec : ∀ a b′ → let b = suc b′ in
                a div b * b + a mod b ≡ a
divmod-spec a b = safeEqual (divmodAux 0 a b (wfNat a))

data DivMod a b : Set where
  qr : ∀ q r → LessThan r b → q * b + r ≡ a → DivMod a b

syntax divMod b a = a divmod b
divMod : ∀ b {_ : NonZero b} a → DivMod a b
divMod zero {} a
divMod (suc b) a = qr (a div suc b) (a mod suc b) (modLess a b) (divmod-spec a b)

data Even n : Set where
  dbl : ∀ k → k * 2 ≡ n → Even n

data Odd n : Set where
  dbl+1 : ∀ k → 1 + k * 2 ≡ n → Odd n

parity : ∀ n → Either (Odd n) (Even n)
parity n with n divmod 2
parity n | qr q 0 lt eq = right $ dbl   q (use eq tactic assumed)
parity n | qr q 1 lt eq = left  $ dbl+1 q (use eq tactic assumed)
parity n | qr q (suc (suc _)) (diffP _ bad) _ = 0≠1 $ use bad tactic simpl | λ ()

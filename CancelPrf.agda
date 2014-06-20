
open import Prelude
open import Data.Reflect
open import RingSolver.Lemmas
open import RingSolver.Exp
open import RingSolver.NF
open import RingSolver.Reflect
open import Data.Nat.Lemmas
open import EqReasoning

foldr-map-fusion : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                     (f : B → C → C) (g : A → B) (z : C) (xs : List A) →
                     foldr f z (map g xs) ≡ foldr (f ∘ g) z xs
foldr-map-fusion f g z [] = refl
foldr-map-fusion f g z (x ∷ xs)
  rewrite foldr-map-fusion f g z xs
        = refl

foldl-map-fusion : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
                     (f : C → B → C) (g : A → B) (z : C) (xs : List A) →
                     foldl f z (map g xs) ≡ foldl (λ x y → f x (g y)) z xs
foldl-map-fusion f g z [] = refl
foldl-map-fusion f g z (x ∷ xs)
  rewrite foldl-map-fusion f g (f z (g x)) xs
        = refl

foldl-assoc : ∀ {a} {A : Set a} (f : A → A → A) →
                (∀ x y z → f x (f y z) ≡ f (f x y) z) →
                ∀ y z xs → foldl f (f y z) xs ≡ f y (foldl f z xs)
foldl-assoc f assoc y z [] = refl
foldl-assoc f assoc y z (x ∷ xs)
  rewrite sym (assoc y z x)
        = foldl-assoc f assoc y (f z x) xs

foldl-foldr : ∀ {a} {A : Set a} (f : A → A → A) (z : A) →
                (∀ x y z → f x (f y z) ≡ f (f x y) z) →
                (∀ x → f z x ≡ x) → (∀ x → f x z ≡ x) →
                ∀ xs → foldl f z xs ≡ foldr f z xs
foldl-foldr f z assoc idl idr [] = refl
foldl-foldr f z assoc idl idr (x ∷ xs)
  rewrite sym (foldl-foldr f z assoc idl idr xs)
        | idl x ≡tr sym (idr x)
        = foldl-assoc f assoc x z xs

product1-sound : ∀ xs → product1 xs ≡ product xs
product1-sound [] = refl
product1-sound (x ∷ xs)
  rewrite sym (cong (λ x → foldl _*_ x xs) (mul-1-r x))
        | foldl-assoc _*_ mul-assoc x 1 xs
        | foldl-foldr _*_ 1 mul-assoc (λ _ → refl) mul-1-r xs
        = refl

ts-sound : ∀ x ρ → ⟦ x ⟧ts ρ ≡ ⟦ x ⟧t ρ
ts-sound (0 , x) ρ = mul-0-r (product1 (map ρ x))
ts-sound (1 , x) ρ = product1-sound (map ρ x)
ts-sound (suc (suc i) , x) ρ
  rewrite sym (product1-sound (map ρ x))
        = quoteGoal g in unquote (prove g)

map-eq : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) →
           (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
map-eq f g f=g [] = refl
map-eq f g f=g (x ∷ xs) rewrite f=g x | map-eq f g f=g xs = refl

private
  et  = flip ⟦_⟧t
  ets = flip ⟦_⟧ts

ns-sound : ∀ nf ρ → ⟦ nf ⟧ns ρ ≡ ⟦ nf ⟧n ρ
ns-sound [] ρ = refl
ns-sound (x ∷ nf) ρ
  rewrite sym (foldl-map-fusion _+_ (ets ρ) (ets ρ x) nf)
        | ts-sound x ρ
        | map-eq (ets ρ) (et ρ) (flip ts-sound ρ) nf
        | sym (foldl-foldr _+_ 0 add-assoc (λ _ → refl) add-0-r (map (et ρ) nf))
        | sym (foldl-assoc _+_ add-assoc (et ρ x) 0 (map (et ρ) nf))
        | add-0-r (et ρ x)
        = refl

fst-*** : ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
            (f : A₁ → B₁) (g : A₂ → B₂) (p : A₁ × A₂) →
            fst ((f *** g) p) ≡ f (fst p)
fst-*** f g (x , y) = refl

snd-*** : ∀ {a b} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
            (f : A₁ → B₁) (g : A₂ → B₂) (p : A₁ × A₂) →
            snd ((f *** g) p) ≡ g (snd p)
snd-*** f g (x , y) = refl

eta : ∀ {a b} {A : Set a} {B : Set b} (p : A × B) → p ≡ (fst p , snd p)
eta (x , y) = refl

shuffle₁ : ∀ a b c → a + (b + c) ≡ b + (a + c)
shuffle₁ a b c = quoteGoal g in unquote (prove g)

cancelsound′ : ∀ a b nf₁ nf₂ ρ → a + ⟦ fst (cancel nf₁ nf₂) ⟧n ρ ≡ b + ⟦ snd (cancel nf₁ nf₂) ⟧n ρ →
                             a + ⟦ nf₁ ⟧n ρ ≡ b + ⟦ nf₂ ⟧n ρ
cancelsound′ a b [] []        ρ H = H
cancelsound′ a b [] (x ∷ nf₂) ρ H = H
cancelsound′ a b (x ∷ nf₁) [] ρ H = H
cancelsound′ a b ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) ρ H
  with compare x y
... | less    _ rewrite fst-*** (List._∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
                      | snd-*** (List._∷_ (i , x)) id (cancel nf₁ ((j , y) ∷ nf₂))
                      | add-assoc a (et ρ (i , x)) (⟦ fst (cancel nf₁ ((j , y) ∷ nf₂)) ⟧n ρ)
                      | add-assoc a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
                      = cancelsound′ (a + et ρ (i , x)) b nf₁ ((j , y) ∷ nf₂) ρ H
... | greater _ rewrite fst-*** id (List._∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
                      | snd-*** id (List._∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
                      | add-assoc b (et ρ (j , y)) (⟦ snd (cancel ((i , x) ∷ nf₁) nf₂) ⟧n ρ)
                      | add-assoc b (et ρ (j , y)) (⟦ nf₂ ⟧n ρ)
                      = cancelsound′ a (b + et ρ (j , y)) ((i , x) ∷ nf₁) nf₂ ρ H
cancelsound′ a b ((i , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl
  with compare i j
cancelsound′ a b ((i , x) ∷ nf₁) ((.(i + suc k) , .x) ∷ nf₂) ρ H | equal refl | less (diff k)
  rewrite fst-*** id (List._∷_ (suc k , x)) (cancel nf₁ nf₂)
        | snd-*** id (List._∷_ (suc k , x)) (cancel nf₁ nf₂)
        | add-assoc b (et ρ (suc k , x)) (⟦ snd (cancel nf₁ nf₂) ⟧n ρ)
        | shuffle₁ a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
        | cancelsound′ a (b + et ρ (suc k , x)) nf₁ nf₂ ρ H
        = quoteGoal g in unquote (prove g)
cancelsound′ a b ((.(j + suc k) , x) ∷ nf₁) ((j , .x) ∷ nf₂) ρ H | equal refl | greater (diff k)
  rewrite fst-*** (List._∷_ (suc k , x)) id (cancel nf₁ nf₂)
        | snd-*** (List._∷_ (suc k , x)) id (cancel nf₁ nf₂)
        | add-assoc a (et ρ (suc k , x)) (⟦ fst (cancel nf₁ nf₂) ⟧n ρ)
        | shuffle₁ b (et ρ (j , x)) (⟦ nf₂ ⟧n ρ)
        | sym (cancelsound′ (a + et ρ (suc k , x)) b nf₁ nf₂ ρ H)
        = quoteGoal g in unquote (prove g)
cancelsound′ a b ((i , x) ∷ nf₁) ((.i , .x) ∷ nf₂) ρ H | equal refl | equal refl
  rewrite shuffle₁ a (et ρ (i , x)) (⟦ nf₁ ⟧n ρ)
        | cancelsound′ a b nf₁ nf₂ ρ H
        = quoteGoal g in unquote (prove g)

cancelsound : ∀ nf₁ nf₂ ρ → NFEqS (cancel nf₁ nf₂) ρ → NFEq (nf₁ , nf₂) ρ
cancelsound nf₁ nf₂ ρ H rewrite cong (λ p → NFEqS p ρ) (eta (cancel nf₁ nf₂))
                              | ns-sound (fst (cancel nf₁ nf₂)) ρ
                              | ns-sound (snd (cancel nf₁ nf₂)) ρ
                              = cancelsound′ 0 0 nf₁ nf₂ ρ H

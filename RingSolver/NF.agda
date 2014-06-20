
module RingSolver.NF where

open import Prelude
open import RingSolver.Exp
open import RingSolver.Bag

Term = List Var
NF   = List (Nat × Term)

OrdTerm : Ord Term
OrdTerm = OrdList

OrdKTerm : Ord (Nat × Term)
OrdKTerm = OrdPair

_+nf_ : NF → NF → NF
_+nf_ a b = union a b

merge : Term → Term → Term
merge x [] = x
merge [] y = y
merge (i ∷ x) (j ∷ y) =
  if lessNat i j then i ∷ merge x (j ∷ y)
                 else j ∷ merge (i ∷ x) y

sort : NF → NF
sort [] = []
sort (x ∷ nf) = union [ x ] (sort nf)

mulTerm : Nat × Term → Nat × Term → Nat × Term
mulTerm (a , x) (b , y) = a * b , merge x y

_*nf_ : NF → NF → NF
[]      *nf b = []
(t ∷ a) *nf b = sort (map (mulTerm t) b) +nf (a *nf b)

norm : Exp → NF
norm (var x) = [ 1 , [ x ] ]
norm (lit 0) = []
norm (lit n) = [ n , [] ]
norm (e ⟨+⟩ e₁) = norm e +nf norm e₁
norm (e ⟨*⟩ e₁) = norm e *nf norm e₁

e₁ = var 0 ⟨*⟩ var 1 ⟨+⟩ var 1 ⟨+⟩ var 1
e₂ = var 1 ⟨*⟩ (lit 2 ⟨+⟩ var 0)

product : List Nat → Nat
product = foldr _*_ 1

sum : List Nat → Nat
sum = foldr _+_ 0

product1 : List Nat → Nat
product1 [] = 1
product1 (x ∷ xs) = foldl (λ n x → n * x) x xs

⟦_⟧t : Nat × Term → Env → Nat
⟦ k , v ⟧t ρ = k * product (map ρ v)

⟦_⟧ts : Nat × Term → Env → Nat
⟦ 1 , v ⟧ts ρ = product1 (map ρ v)
⟦ k , v ⟧ts ρ = product1 (map ρ v) * k

⟦_⟧n : NF → Env → Nat
⟦ nf ⟧n ρ = sum (map (flip ⟦_⟧t ρ) nf)

⟦_⟧ns : NF → Env → Nat
⟦ []     ⟧ns ρ = 0
⟦ t ∷ nf ⟧ns ρ = foldl (λ n t → n + ⟦ t ⟧ts ρ) (⟦ t ⟧ts ρ) nf

cancel : NF → NF → NF × NF
cancel nf₁ [] = nf₁ , []
cancel [] nf₂ = [] , nf₂
cancel ((i , x) ∷ nf₁) ((j , y) ∷ nf₂) with compare x y
... | less    _ = first  (_∷_ (i , x)) (cancel nf₁ ((j , y) ∷ nf₂))
... | greater _ = second (_∷_ (j , y)) (cancel ((i , x) ∷ nf₁) nf₂)
... | equal   _ with compare i j
...                | less    (diffP k _) = second (_∷_ (suc k , y)) (cancel nf₁ nf₂)
...                | greater (diffP k _) = first  (_∷_ (suc k , x)) (cancel nf₁ nf₂)
...                | equal    _ = cancel nf₁ nf₂

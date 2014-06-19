
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

mulTerm : Nat × Term → Nat × Term → Nat × Term
mulTerm (a , x) (b , y) = a * b , merge x y

_*nf_ : NF → NF → NF
[]      *nf b = []
(t ∷ a) *nf b = map (mulTerm t) b +nf (a *nf b)

norm : Exp → NF
norm (var x) = [ 1 , [ x ] ]
norm ⟨0⟩ = []
norm ⟨1⟩ = [ 1 , [] ]
norm (e ⟨+⟩ e₁) = norm e +nf norm e₁
norm (e ⟨*⟩ e₁) = norm e *nf norm e₁

product : List Nat → Nat
product = foldr _*_ 1

sum : List Nat → Nat
sum = foldr _+_ 0

⟦_⟧t : Nat × Term → Env → Nat
⟦ k , v ⟧t ρ = k * product (map ρ v)

⟦_⟧n : NF → Env → Nat
⟦ nf ⟧n ρ = sum (map (flip ⟦_⟧t ρ) nf)

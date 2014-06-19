
module RingSolver.NF where

open import Prelude
open import RingSolver.Exp
open import Ring as R

Term = List Var
NF   = List (Nat × Term)

merge : ∀ {A : Set} {{OrdA : Ord A}} → List A → List A → List A
merge [] ys = ys
merge xs [] = xs
merge (x ∷ xs) (y ∷ ys) =
  if x < y then x ∷ merge xs (y ∷ ys)
           else y ∷ merge (x ∷ xs) ys

OrdTerm : Ord Term
OrdTerm = OrdList

OrdKTerm : Ord (Nat × Term)
OrdKTerm = OrdPair

_+nf_ : NF → NF → NF
_+nf_ a b = merge a b

mulTerm : Nat × Term → Nat × Term → Nat × Term
mulTerm (a , x) (b , y) = a * b , x ++ y

_*nf_ : NF → NF → NF
[]      *nf b = []
(t ∷ a) *nf b = map (mulTerm t) b +nf (a *nf b)

norm : Exp → NF
norm (var x) = [ 1 , [ x ] ]
norm ⟨0⟩ = []
norm ⟨1⟩ = [ 1 , [] ]
norm (e ⟨+⟩ e₁) = norm e +nf norm e₁
norm (e ⟨*⟩ e₁) = norm e *nf norm e₁

module _ {A : Set} {{RingA : Ring A}} where
  open Ring RingA

  ⟦_⟧t : Nat × Term → Env A → A
  ⟦ k , v ⟧t ρ = k #* #prod (map ρ v)

  ⟦_⟧n : NF → Env A → A
  ⟦ nf ⟧n ρ = #sum (map (flip ⟦_⟧t ρ) nf)


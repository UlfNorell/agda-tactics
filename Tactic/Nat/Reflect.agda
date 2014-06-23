
module Tactic.Nat.Reflect where

open import Prelude
open import Prelude.Equality.Unsafe
open import Data.Reflect
open import Data.Reflect.Quote
open import Control.Monad.State

open import Tactic.Nat.Exp

R = StateT (Nat × List (Term × Nat)) Maybe

MonadR : Monad R
MonadR = MonadStateT

ApplicativeR : Applicative R
ApplicativeR = ApplicativeStateT

FunctorR : Functor R
FunctorR = FunctorStateT

fail : ∀ {A} → R A
fail = lift nothing

pattern `Nat = def (quote Nat) []

pattern _`≡_ x y = def (quote _≡_) (_ ∷ arg _ `Nat ∷ arg _ x ∷ arg _ y ∷ [])

pattern _`+_ x y = def (quote _+_) (arg _ x ∷ arg _ y ∷ [])
pattern _`*_ x y = def (quote _*_) (arg _ x ∷ arg _ y ∷ [])
pattern `0       = `zero
pattern `1       = `suc `0

fresh : Term → R Exp
fresh t =
  get >>= uncurry′ λ i Γ →
   var i <$ put (suc i , (t , i) ∷ Γ)

⟨suc⟩ : Exp → Exp
⟨suc⟩ (lit n) = lit (suc n)
⟨suc⟩ (lit n ⟨+⟩ e) = lit (suc n) ⟨+⟩ e
⟨suc⟩ e = lit 1 ⟨+⟩ e

termToExpR : Term → R Exp
termToExpR (a `+ b) = _⟨+⟩_ <$> termToExpR a <*> termToExpR b
termToExpR (a `* b) = _⟨*⟩_ <$> termToExpR a <*> termToExpR b
termToExpR `0       = pure (lit 0)
termToExpR (`suc a) = ⟨suc⟩ <$> termToExpR a
termToExpR unknown  = fail
termToExpR t =
  gets (flip lookup t ∘ snd) >>=
  λ { nothing  → fresh t
    ; (just i) → pure (var i) }

termToExp : Term → Maybe ((Exp × Exp) × List Term)
termToExp (lhs `≡ rhs) =
  second (reverse ∘ map fst ∘ snd) <$>
  runStateT (_,_ <$> termToExpR lhs <*> termToExpR rhs) (0 , [])
termToExp _ = nothing

buildEnv : List Nat → Env
buildEnv [] i = 0
buildEnv (x ∷ xs) zero = x
buildEnv (x ∷ xs) (suc i) = buildEnv xs i

defaultArg : Term → Arg Term
defaultArg = arg (arg-info visible relevant)

data ProofError {a} : Set a → Set (lsuc a) where
  bad-goal : ∀ g → ProofError g

qProofError : Term → Term
qProofError v = con (quote bad-goal) (defaultArg v ∷ [])

implicitArg instanceArg : ∀ {A} → A → Arg A
implicitArg = arg (arg-info hidden relevant)
instanceArg = arg (arg-info instance relevant)

QuotableExp : Quotable Exp
QuotableExp = record { ` = quoteExp }
  where
    quoteExp : Exp → Term
    quoteExp (var x) = con (quote Exp.var) (vArg (` x) ∷ [])
    quoteExp (lit n) = con (quote Exp.lit) (vArg (` n) ∷ [])
    quoteExp (e ⟨+⟩ e₁) = con (quote _⟨+⟩_) $ map defaultArg $ quoteExp e ∷ quoteExp e₁ ∷ []
    quoteExp (e ⟨*⟩ e₁) = con (quote _⟨*⟩_) $ map defaultArg $ quoteExp e ∷ quoteExp e₁ ∷ []

stripImplicitArg : Arg Term → List (Arg Term)
stripImplicitArgs : List (Arg Term) → List (Arg Term)
stripImplicitArgType : Arg Type → Arg Type
stripImplicitType : Type → Type

stripImplicit : Term → Term
stripImplicit (var x args) = var x (stripImplicitArgs args)
stripImplicit (con c args) = con c (stripImplicitArgs args)
stripImplicit (def f args) = def f (stripImplicitArgs args)
stripImplicit (lam v t) = lam v (stripImplicit t)
stripImplicit (pi t₁ t₂) = pi (stripImplicitArgType t₁) (stripImplicitType t₂)
stripImplicit (sort x) = sort x
stripImplicit unknown = unknown

stripImplicitType (el s v) = el s (stripImplicit v)
stripImplicitArgType (arg i a) = arg i (stripImplicitType a)

stripImplicitArgs [] = []
stripImplicitArgs (a ∷ as) = stripImplicitArg a ++ stripImplicitArgs as

stripImplicitArg (arg (arg-info visible r) x) = arg (arg-info visible r) (stripImplicit x) ∷ []
stripImplicitArg (arg (arg-info hidden r) x) = []
stripImplicitArg (arg (arg-info instance r) x) = []

quoteList : List Term → Term
quoteList [] = con (quote List.[]) []
quoteList (t ∷ ts) = con (quote List._∷_) (defaultArg t ∷ defaultArg (quoteList ts) ∷ [])

quotedEnv : List Term → Term
quotedEnv ts = def (quote buildEnv) $ defaultArg (quoteList $ map stripImplicit ts) ∷ []

QED : {A : Set} {x : Maybe A} → Set
QED {x = x} = IsJust x

getProof : {u v : Nat} (prf : Maybe (u ≡ v)) → QED {x = prf} → u ≡ v
getProof (just eq) _ = eq
getProof nothing ()

cantProve : Set → ⊤
cantProve _ = _

invalidGoal : Set → ⊤
invalidGoal _ = _


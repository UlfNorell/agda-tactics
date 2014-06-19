
module RingSolver.Reflect where

open import Prelude
open import Data.Reflect
open import Control.Monad.State

open import RingSolver.Exp
open import RingSolver
open import Ring as R

natToExp : Nat → Exp
natToExp zero    = ⟨0⟩
natToExp (suc n) = ⟨1⟩ ⟨+⟩ natToExp n

R = StateT (Nat × List (Term × Nat)) Maybe

MonadR : Monad R
MonadR = MonadStateT

ApplicativeR : Applicative R
ApplicativeR = ApplicativeStateT

FunctorR : Functor R
FunctorR = FunctorStateT

fail : ∀ {A} → R A
fail = lift nothing

pattern _`≡_ x y = def (quote _≡_) (_ ∷ _ ∷ arg _ x ∷ arg _ y ∷ [])

pattern _`+_ x y = def (quote _+_) (arg _ x ∷ arg _ y ∷ [])
pattern _`*_ x y = def (quote _*_) (arg _ x ∷ arg _ y ∷ [])
pattern `suc n   = con (quote Nat.suc) (arg _ n ∷ [])
pattern `0       = con (quote Nat.zero) []
pattern `1       = `suc `0

fresh : Term → R Exp
fresh t =
  get >>= uncurry′ λ i Γ →
   var i <$ put (suc i , (t , i) ∷ Γ)

termToExpR : Term → R Exp
termToExpR (a `+ b) = _⟨+⟩_ <$> termToExpR a <*> termToExpR b
termToExpR (a `* b) = _⟨*⟩_ <$> termToExpR a <*> termToExpR b
termToExpR `0       = pure ⟨0⟩
termToExpR `1       = pure ⟨1⟩
termToExpR (`suc a) = _⟨+⟩_ ⟨1⟩ <$> termToExpR a
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

buildEnv : List Nat → Env Nat
buildEnv [] i = 0
buildEnv (x ∷ xs) zero = x
buildEnv (x ∷ xs) (suc i) = buildEnv xs i

defaultArg : Term → Arg Term
defaultArg = arg (arg-info visible relevant)

quoteList : List Term → Term
quoteList [] = con (quote List.[]) []
quoteList (t ∷ ts) = con (quote List._∷_) (defaultArg t ∷ defaultArg (quoteList ts) ∷ [])

quotedEnv : List Term → Term
quotedEnv ts = def (quote buildEnv) $ defaultArg (quoteList ts) ∷ []

data ProofError {a} : Set a → Set (lsuc a) where
  bad-goal : ∀ g → ProofError g

qProofError : Term → Term
qProofError v = con (quote bad-goal) (defaultArg v ∷ [])

qNat = quoteTerm Nat
qRingNat = quoteTerm RingNat

implicitArg instanceArg : ∀ {A} → A → Arg A
implicitArg = arg (arg-info hidden relevant)
instanceArg = arg (arg-info instance relevant)

quoteNat : Nat → Term
quoteNat zero    = `0
quoteNat (suc n) = con (quote Nat.suc) (defaultArg (quoteNat n) ∷ [])

quoteExp : Exp → Term
quoteExp (var x) = con (quote Exp.var) (defaultArg (quoteNat x) ∷ [])
quoteExp ⟨0⟩ = con (quote ⟨0⟩) []
quoteExp ⟨1⟩ = con (quote ⟨1⟩) []
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

prove : Term → Term
prove t =
  case termToExp t of
  λ { nothing → qProofError (stripImplicit t)
    ; (just ((e₁ , e₂) , Γ)) →
      def (quote fromJust) $
        defaultArg
          (def (quote proof) ( defaultArg (quoteExp e₁)
                             ∷ defaultArg (quoteExp e₂)
                             ∷ defaultArg (quotedEnv Γ)
                             ∷ []))
        ∷ []
    }
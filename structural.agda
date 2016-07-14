open import Nat
open import Prelude
open import core
open import checks

module structural where
  -- this module contains proofs that the judgements that mention contexts
  -- defined throughout the work have the right structural properties with
  -- respect to those contexts: exchange, weakening, and contraction.

  -- we only argue weakening and contraction here. because of the choice of
  -- representation of contexts, it's not possible for anything that we've
  -- defined to not admit exchange, because functions are inherently not
  -- internally ordered.

  -- contraction
  --
  -- Γ, (x : t), (x : t) ⊢ A
  -- -----------------------
  --     Γ , (x : t) ⊢ A


  -- weakening
  --
  --   Γ ⊢ A      x # Γ
  -- ----------------------
  --    Γ , (x : t) ⊢ A

  ---- well-typedness jugements

  -- extending a context with a new variable doesn't change anything under
  lem-extend : ∀{n x Γ t w} →
               (n == x → ⊥) → Γ n == w → (Γ ,, (x , t)) n == w
  lem-extend {n} {x} neq w with natEQ x n
  lem-extend neq w₁ | Inl refl = abort (neq refl)
  lem-extend neq w₁ | Inr x₁ = w₁

  mutual
    wt-weak-synth : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} →
                    x # Γ →
                    Γ ⊢ e => t →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-weak-synth a wt = {!!}
    -- wt-weak-synth A (SAsc x₁) = SAsc (wt-weak-ana A x₁)
    -- wt-weak-synth {x = x} A (SVar {n = n} x₁) with natEQ n x
    -- wt-weak-synth A (SVar x₁) | Inl refl = abort (somenotnone (! x₁ · A))
    -- ... | Inr qq = SVar (lem-extend qq x₁)
    -- wt-weak-synth A (SAp wt x₁ x₂) = SAp (wt-weak-synth A wt) x₁ (wt-weak-ana A x₂)
    -- wt-weak-synth A SNum = SNum
    -- wt-weak-synth A (SPlus x₁ x₂) = SPlus (wt-weak-ana A x₁) (wt-weak-ana A x₂)
    -- wt-weak-synth A SEHole = SEHole
    -- wt-weak-synth A (SNEHole wt) = SNEHole (wt-weak-synth A wt)

    wt-weak-ana : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} → (x # Γ) →
                    Γ ⊢ e <= t →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-weak-ana A (ASubsume x₁ x₂) = ASubsume (wt-weak-synth A x₁) x₂
    wt-weak-ana A (ALam x₂ x₃ wt) = {!!}

  -- the contraction cases are much easier and don't require induction over
  -- the typing jugement, because the contexts in question are indeed
  -- equal. they agree on all input, so they can be swapped via funext and
  -- a transport.
  lem-contract-eq : (Γ : ·ctx) (x : Nat) (t : τ̇) (y : Nat) →
         ((Γ ,, (x , t)) ,, (x , t)) y == (Γ ,, (x , t)) y
  lem-contract-eq Γ x t y with natEQ x y
  lem-contract-eq Γ x t .x | Inl refl = refl
  ... | Inr qq with natEQ x y
  ... | Inl pp = abort (qq pp)
  ... | Inr pp = refl

  mutual
    wt-contract-synth : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} → (x # Γ) →
                    ((Γ ,, (x , t')) ,, (x , t')) ⊢ e => t →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-contract-synth {Γ} {x} {t} {t'} {e} A wt =
         tr (λ q → q ⊢ e => t) (funext (lem-contract-eq Γ x t')) wt

    wt-contract-ana : (Γ : ·ctx) (x : Nat) (t t' : τ̇) (e : ė) → (x # Γ) →
                    ((Γ ,, (x , t')) ,, (x , t')) ⊢ e <= t →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-contract-ana Γ x t t' e A wt =
         tr (λ q → q ⊢ e <= t) (funext (lem-contract-eq Γ x t')) wt

  ---- action expressions (synth and ana)
  -- act-weak-synth
  -- act-weak-ana

  -- act-contract-synth
  -- act-contract-ana

  -- what about transitivity / cut elimination?

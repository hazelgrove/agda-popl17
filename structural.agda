open import Nat
open import Prelude
open import core
open import judgemental-erase
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
  mutual
    wt-weak-synth : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} →
                    x # Γ →
                    Γ ⊢ e => t →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-weak-synth A (SAsc x₁) = SAsc (wt-weak-ana A x₁)
    wt-weak-synth {x = x} A (SVar {n = n} x₁) with natEQ n x
    wt-weak-synth A (SVar x₁) | Inl refl = abort (somenotnone (! x₁ · A))
    ... | Inr qq = SVar {!!}
    wt-weak-synth A (SAp wt x₁ x₂) = SAp (wt-weak-synth A wt) x₁ {!!}
    wt-weak-synth A SNum = SNum
    wt-weak-synth A (SPlus x₁ x₂) = SPlus (wt-weak-ana A x₁) (wt-weak-ana A x₂)
    wt-weak-synth A SEHole = SEHole
    wt-weak-synth A (SNEHole wt) = SNEHole (wt-weak-synth A wt)

    wt-weak-ana : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} → (x # Γ) →
                    Γ ⊢ e <= t →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-weak-ana A (ASubsume x₁ x₂) = ASubsume (wt-weak-synth A x₁) x₂
    wt-weak-ana A (ALam x₂ x₃ wt) = ALam {!!} x₃ (wt-weak-ana {!!} {!!})

  mutual
    wt-contract-synth : (Γ : ·ctx) (x : Nat) (t t' : τ̇) (e : ė) → (x # Γ) →
                    ((Γ ,, (x , t')) ,, (x , t')) ⊢ e => t →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-contract-synth = {!!}

    wt-contract-ana : (Γ : ·ctx) (x : Nat) (t t' : τ̇) (e : ė) → (x # Γ) →
                    ((Γ ,, (x , t')) ,, (x , t')) ⊢ e <= t →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-contract-ana = {!!}

  ---- action expressions (synth and ana)
  -- act-weak-synth
  -- act-weak-ana

  -- act-contract-synth
  -- act-contract-ana

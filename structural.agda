open import Nat
open import Prelude
open import core
open import checks

module structural where
  -- this module contains proofs that the judgements that mention contexts
  -- defined throughout the work have the right structural properties with
  -- respect to those contexts: exchange, weakening, and contraction.
  --
  -- we only argue weakening and contraction. because of the choice of
  -- representation of contexts as functions, it's not possible for
  -- anything that we've defined to not admit exchange, because functions
  -- are inherently not internally ordered.
  --
  -- contraction
  --
  -- Γ, (x : t), (x : t) ⊢ A
  -- -----------------------
  --     Γ , (x : t) ⊢ A
  --
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

  -- because of our choice to use barendrecht's convention, we need a quite
  -- strong form of apartness for weakening. specifically, we need to know
  -- not just that the variable we're using to extend the context doesn't
  -- appear in the context, as in a standard presentation, it can't appear
  -- anywhere in the term at all; it must be totally fresh. it's possible
  -- to drop this requirement with alpha-renaming to recover the standard
  -- description of these things, so we allow it here for convenience.
  fresh : Nat → ė → Set
  fresh x (e ·: x₁) = fresh x e
  fresh x (X y) with natEQ x y
  ... | Inl eq = ⊥
  ... | Inr neq = ⊤
  fresh x (·λ y e) with natEQ x y
  ... | Inl eq = ⊥
  ... | Inr neq = fresh x e
  fresh x (N n) = ⊤
  fresh x (e1 ·+ e2) = fresh x e1 × fresh x e2
  fresh x <||> = ⊤
  fresh x <| e |> = fresh x e
  fresh x (e1 ∘ e2) = fresh x e1 × fresh x e2

  mutual
    wt-weak-synth : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} →
                    x # Γ →
                    fresh x e →
                    Γ ⊢ e => t →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-weak-synth A F (SAsc x₁) = SAsc (wt-weak-ana A F x₁)
    wt-weak-synth {x = x} A F (SVar {n = n} x₁) with natEQ n x
    wt-weak-synth A F (SVar x₁) | Inl refl = abort (somenotnone (! x₁ · A))
    ... | Inr qq = SVar (lem-extend qq x₁)
    wt-weak-synth A F (SAp wt x₁ x₂) = SAp (wt-weak-synth A (π1 F) wt) x₁ (wt-weak-ana A (π2 F) x₂)
    wt-weak-synth A F SNum = SNum
    wt-weak-synth A F(SPlus x₁ x₂) = SPlus (wt-weak-ana A (π1 F) x₁) (wt-weak-ana A (π2 F) x₂)
    wt-weak-synth A F SEHole = SEHole
    wt-weak-synth A F (SNEHole wt) = SNEHole (wt-weak-synth A F wt)

    wt-weak-ana : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} →
                    x # Γ →
                    fresh x e →
                    Γ ⊢ e <= t →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-weak-ana A F (ASubsume x₁ x₂) = ASubsume (wt-weak-synth A F x₁) x₂
    wt-weak-ana {x = x} A F (ALam {x = x₁} x₂ x₃ wt) with natEQ x x₁
    wt-weak-ana A F (ALam x₂ x₃ wt) | Inl refl = abort F
    wt-weak-ana A F (ALam x₂ x₃ wt) | Inr neq  = {!!} -- ALam (lem-extend {!!} x₂) x₃ (wt-weak-ana {!!} {!!} wt)


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

  -- what about transitivity / cut elimination?

  mutual
    act-contract-synth : ∀{ Γ x t t' t'' e e' α } →
                         ((Γ ,, (x , t'')) ,, (x , t'')) ⊢ e => t ~ α ~> e' => t' →
                         (Γ ,, (x , t'')) ⊢ e => t ~ α ~> e' => t'
    act-contract-synth {Γ} {x} {t} {t'} {t''} {e} {e'} {α} d = tr (λ q → q ⊢ e => t ~ α ~> e' => t') (funext (lem-contract-eq Γ x t'')) d

    act-contract-ana : ∀{ Γ x t t' e e' α } →
                         ((Γ ,, (x , t')) ,, (x , t')) ⊢ e ~ α ~> e' ⇐ t →
                         (Γ ,, (x , t')) ⊢ e ~ α ~> e' ⇐ t
    act-contract-ana {Γ} {x} {t} {t'} {e} {e'} {α} d = tr (λ q → q ⊢ e ~ α ~> e' ⇐ t) (funext (lem-contract-eq Γ x t')) d

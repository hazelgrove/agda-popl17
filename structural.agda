open import Nat
open import Prelude
open import core
open import checks
open import judgemental-erase

module structural where
  -- this module contains proofs that the judgements that mention contexts
  -- defined throughout the work enjoy the standard structural properties
  -- of contexts:
  --
  -- exchange
  --
  -- Γ, (x : t1), (y : t2) ⊢ A
  -- -------------------------
  -- Γ, (y : t2), (x : t1) ⊢ A
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
  --
  -- proofs of the first two are generally easier: viewed as finite
  -- functions, the contexts on the top and bottom of both exchange answer
  -- every question the same, so an appeal to function extensionality is
  -- enough to treat them the same. weakening does not have this property,
  -- and there requires some induction to demonstrate.

  -- because of our choice to use barendrecht's convention, we need a quite
  -- strong form of apartness for weakening. specifically, we need to know
  -- not just that the variable we're using to extend the context doesn't
  -- appear in the context, as in a standard presentation, it can't appear
  -- anywhere in the term at all; it must be totally fresh. it's possible
  -- to drop this requirement with alpha-renaming to recover the standard
  -- description of these things, so we allow it here for convenience.
  fresh : Nat → ė → Set
  fresh x (e ·: t) = fresh x e
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
    fresh-synth : ∀{Γ e t α e' t'} →
                                Nat →
                                (Γ ⊢ e => t ~ α ~> e' => t') →
                                Set
    fresh-synth x (SAMove x₁) = ⊤
    fresh-synth x SADel = ⊤
    fresh-synth x SAConAsc = ⊤
    fresh-synth x₁ (SAConVar {x = x} p) = ⊤ -- maybe ban one
    fresh-synth x₁ (SAConLam {x = x} x₂) = natEQp x₁ x
    fresh-synth x (SAConApArr x₁) = ⊤
    fresh-synth x (SAConApOtw x₁) = ⊤
    fresh-synth x SAConArg = ⊤
    fresh-synth x SAConNumlit = ⊤
    fresh-synth x (SAConPlus1 x₁) = ⊤
    fresh-synth x (SAConPlus2 x₁) = ⊤
    fresh-synth x SAConNEHole = ⊤
    fresh-synth x (SAFinish x₁) = ⊤
    fresh-synth x (SAZipAsc1 x₁) = fresh-ana x x₁
    fresh-synth x (SAZipAsc2 x₁ x₂ x₃ x₄) = ⊤
    fresh-synth x (SAZipApArr x₁ x₂ x₃ d x₄) = fresh-synth x d
    fresh-synth x (SAZipApAna x₁ x₂ x₃) = fresh-ana x x₃
    fresh-synth x (SAZipPlus1 x₁) = fresh-ana x x₁
    fresh-synth x (SAZipPlus2 x₁) = fresh-ana x x₁
    fresh-synth x (SAZipHole x₁ x₂ d) = fresh-synth x d

    fresh-ana : ∀{Γ e t α e'} →
                                Nat →
                                (Γ ⊢ e ~ α ~> e' ⇐ t) →
                                Set
    fresh-ana x (AASubsume x₁ x₂ x₃ x₄) = fresh-synth x x₃
    fresh-ana x (AAMove x₁) = ⊤
    fresh-ana x AADel = ⊤
    fresh-ana x AAConAsc = ⊤
    fresh-ana x₁ (AAConVar {x = x} x₂ p) = {!natEQp x x₁!}
    fresh-ana x₁ (AAConLam1 {x = x} x₂ x₃) = {!!}
    fresh-ana x₁ (AAConLam2 {x = x} x₂ x₃) = {!!}
    fresh-ana x (AAConNumlit x₁) = ⊤
    fresh-ana x (AAFinish x₁) = ⊤
    fresh-ana x₁ (AAZipLam x₂ x₃ d) = {!!}

  ---- lemmas

  --- a contracted context gives all the same responses as the
  --- non-contracted context
  lem-contract : (Γ : ·ctx) (x : Nat) (t : τ̇) (y : Nat) →
         ((Γ ,, (x , t)) ,, (x , t)) y == (Γ ,, (x , t)) y
  lem-contract Γ x t y with natEQ x y
  lem-contract Γ x t .x | Inl refl = refl
  ... | Inr qq with natEQ x y
  ... | Inl pp = abort (qq pp)
  ... | Inr pp = refl

  --- an exchanged context gives all the same responses as the
  --- non-exchanged context
  lem-swap : (Γ : ·ctx) (x y : Nat) (t1 t2 : τ̇) {x≠y : x == y → ⊥}  (z : Nat) →
         ((Γ ,, (x , t1)) ,, (y , t2)) z == ((Γ ,, (y , t2)) ,, (x , t1)) z
  lem-swap Γ x y t1 t2 z with natEQ x z | natEQ y z
  lem-swap Γ x y t1 t2 {x≠y} z | Inl p | Inl q = abort (x≠y (p · ! q))
  lem-swap Γ x y t1 t2 .x | Inl refl | Inr x₂ with natEQ x x
  lem-swap Γ x y t1 t2 .x | Inl refl | Inr x₂ | Inl refl = refl
  lem-swap Γ x y t1 t2 .x | Inl refl | Inr x₂ | Inr x₁ = abort (x₁ refl)
  lem-swap Γ x y t1 t2 .y | Inr x₁ | Inl refl with natEQ y y
  lem-swap Γ x₁ y t1 t2 .y | Inr x₂ | Inl refl | Inl refl = refl
  lem-swap Γ x₁ y t1 t2 .y | Inr x₂ | Inl refl | Inr x = abort (x refl)
  lem-swap Γ x y t1 t2 z | Inr x₁ | Inr x₂ with natEQ x z | natEQ y z
  lem-swap Γ x .x t1 t2 .x | Inr x₂ | Inr x₃ | Inl refl | Inl refl = abort (x₃ refl)
  lem-swap Γ x y t1 t2 .x | Inr x₂ | Inr x₃ | Inl refl | Inr x₁ = abort (x₂ refl)
  lem-swap Γ x y t1 t2 z | Inr x₃ | Inr x₄ | Inr x₁ | Inl x₂ = abort (x₄ x₂)
  lem-swap Γ x y t1 t2 z | Inr x₃ | Inr x₄ | Inr x₁ | Inr x₂ = refl

  -- extending a context with a new variable doesn't change anything under
  lem-extend : ∀{n x Γ t w} →
               (n == x → ⊥) → Γ n == w → (Γ ,, (x , t)) n == w
  lem-extend {n} {x} neq w with natEQ x n
  lem-extend neq w₁ | Inl refl = abort (neq refl)
  lem-extend neq w₁ | Inr x₁ = w₁

  ---- well-typedness jugements
  mutual
    wt-exchange-synth : {Γ : ·ctx} {x y : Nat} {t1 t2 t : τ̇} {e : ė} →
                        {x≠y : x == y → ⊥} →
                        ((Γ ,, (x , t1)) ,, (y , t2)) ⊢ e => t →
                        ((Γ ,, (y , t2)) ,, (x , t1)) ⊢ e => t
    wt-exchange-synth {Γ} {x} {y} {t1} {t2} {t} {e} {x≠y} d =
      tr (λ q → q ⊢ e => t) (funext (lem-swap Γ x y t1 t2 {x≠y = x≠y})) d

    wt-exchange-ana : {Γ : ·ctx} {x y : Nat} {t1 t2 t : τ̇} {e : ė} →
                        {x≠y : x == y → ⊥} →
                        ((Γ ,, (x , t1)) ,, (y , t2)) ⊢ e <= t →
                        ((Γ ,, (y , t2)) ,, (x , t1)) ⊢ e <= t
    wt-exchange-ana {Γ} {x} {y} {t1} {t2} {t} {e} {x≠y} d =
      tr (λ q → q ⊢ e <= t) (funext (lem-swap Γ x y t1 t2 {x≠y = x≠y})) d

  mutual
    wt-contract-synth : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} →
                    ((Γ ,, (x , t')) ,, (x , t')) ⊢ e => t →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-contract-synth {Γ} {x} {t} {t'} {e}  wt =
         tr (λ q → q ⊢ e => t) (funext (lem-contract Γ x t')) wt

    wt-contract-ana : (Γ : ·ctx) (x : Nat) (t t' : τ̇) (e : ė) →
                    ((Γ ,, (x , t')) ,, (x , t')) ⊢ e <= t →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-contract-ana Γ x t t' e wt =
         tr (λ q → q ⊢ e <= t) (funext (lem-contract Γ x t')) wt

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
    wt-weak-ana {x = x} A F (ALam {x = z} x₂ x₃ wt) | Inr neq = ALam (lem-extend (flip neq) x₂) x₃ {!!}

  ---- action semantics judgements
  mutual
    act-exchange-synth : ∀{ Γ x y t1 t2 t t' e e' α } →
                         (x == y → ⊥) →
                         ((Γ ,, (x , t1)) ,, (y , t2)) ⊢ e => t ~ α ~> e' => t' →
                         ((Γ ,, (y , t2)) ,, (x , t1)) ⊢ e => t ~ α ~> e' => t'
    act-exchange-synth {Γ} {x} {y} {t1} {t2} {t} {t'} {e} {e'} {α} x≠y d = tr (λ q → q ⊢ e => t ~ α ~> e' => t') (funext (lem-swap Γ x y t1 t2 {x≠y})) d

    act-exchange-ana :  ∀{ Γ x y t1 t2 t e e' α } →
                         (x == y → ⊥) →
                         ((Γ ,, (x , t1)) ,, (y , t2)) ⊢ e ~ α ~> e' ⇐ t →
                         ((Γ ,, (y , t2)) ,, (x , t1)) ⊢ e ~ α ~> e' ⇐ t
    act-exchange-ana {Γ} {x} {y} {t1} {t2} {t} {e} {e'} {α} x≠y d = tr (λ q → q ⊢ e ~ α ~> e' ⇐ t) (funext (lem-swap Γ x y t1 t2 {x≠y})) d

  mutual
    act-contract-synth : ∀{ Γ x t t' t'' e e' α } →
                         ((Γ ,, (x , t'')) ,, (x , t'')) ⊢ e => t ~ α ~> e' => t' →
                         (Γ ,, (x , t'')) ⊢ e => t ~ α ~> e' => t'
    act-contract-synth {Γ} {x} {t} {t'} {t''} {e} {e'} {α} d = tr (λ q → q ⊢ e => t ~ α ~> e' => t') (funext (lem-contract Γ x t'')) d

    act-contract-ana : ∀{ Γ x t t' e e' α } →
                         ((Γ ,, (x , t')) ,, (x , t')) ⊢ e ~ α ~> e' ⇐ t →
                         (Γ ,, (x , t')) ⊢ e ~ α ~> e' ⇐ t
    act-contract-ana {Γ} {x} {t} {t'} {e} {e'} {α} d = tr (λ q → q ⊢ e ~ α ~> e' ⇐ t) (funext (lem-contract Γ x t')) d

  mutual
    act-weak-synth : ∀{ Γ x t t' t'' e e' α } →
                         x # Γ →
                         (d : Γ ⊢ e => t ~ α ~> e' => t') →
                         fresh-synth x d →
                         (Γ ,, (x , t'')) ⊢ e => t ~ α ~> e' => t'
    act-weak-synth apt (SAMove x₁) _ = SAMove x₁
    act-weak-synth apt SADel _ = SADel
    act-weak-synth apt SAConAsc _ = SAConAsc
    act-weak-synth {x = x} apt  (SAConVar {x = x'} p) _ with natEQ x x'
    act-weak-synth apt (SAConVar p) _ | Inl refl = SAConVar (abort (somenotnone (! p · apt)))
    ... | Inr neq = SAConVar (lem-extend (flip neq) p)
    act-weak-synth {x = x} apt (SAConLam {x = x₁} x₂) F with natEQ x x₁
    act-weak-synth apt (SAConLam x₃) F | Inl refl = abort F
    act-weak-synth apt (SAConLam x₃) F | Inr x₂ = SAConLam {!!}
    act-weak-synth apt (SAConApArr x₁) F = SAConApArr x₁
    act-weak-synth apt (SAConApOtw x₁) F = SAConApOtw x₁
    act-weak-synth apt SAConArg F = SAConArg
    act-weak-synth apt SAConNumlit F = SAConNumlit
    act-weak-synth apt (SAConPlus1 x₁) F = SAConPlus1 x₁
    act-weak-synth apt (SAConPlus2 x₁) F = SAConPlus2 x₁
    act-weak-synth apt SAConNEHole F = SAConNEHole
    act-weak-synth apt (SAFinish x₁) F = SAFinish (wt-weak-synth apt {!!} x₁)
    act-weak-synth apt (SAZipAsc1 x₁) F = SAZipAsc1 (act-weak-ana apt {!!} x₁)
    act-weak-synth apt (SAZipAsc2 x₁ x₂ x₃ x₄) F = SAZipAsc2 x₁ x₂ x₃ (wt-weak-ana apt {!!} x₄)
    ---- act-weak-synth apt (SAZipApArr x₁ x₂ x₃ d x₄) F = SAZipApArr x₁ x₂ (wt-weak-synth apt {!!} {!!}) (act-weak-synth apt d {!!}) (wt-weak-ana apt {!!} x₄)
    act-weak-synth apt (SAZipApArr x₁ x₂ x₃ d x₄) F = {!!}
    act-weak-synth apt (SAZipApAna x₁ x₂ x₃) F = SAZipApAna x₁ (wt-weak-synth apt {!!} x₂) (act-weak-ana apt {!!} x₃)
    act-weak-synth apt (SAZipPlus1 x₁) F = SAZipPlus1 (act-weak-ana apt {!!} x₁)
    act-weak-synth apt (SAZipPlus2 x₁) F = SAZipPlus2 (act-weak-ana apt {!!} x₁)
    act-weak-synth apt (SAZipHole x₁ x₂ d) F = SAZipHole x₁ (wt-weak-synth apt {!!} x₂) (act-weak-synth apt d {!!})

    act-weak-ana : ∀{ Γ x t t' e e' α } →
                         x # Γ →
                         fresh x (e ◆e) →
                         Γ ⊢ e ~ α ~> e' ⇐ t →
                         (Γ ,, (x , t')) ⊢ e ~ α ~> e' ⇐ t
    act-weak-ana apt F (AASubsume x₁ x₂ x₃ x₄) = {!!}
    act-weak-ana apt F (AAMove x₁) = AAMove x₁
    act-weak-ana apt F AADel = AADel
    act-weak-ana apt F AAConAsc = AAConAsc
    act-weak-ana apt F (AAConVar x₂ p) = AAConVar x₂ {!!}
    act-weak-ana apt F (AAConLam1 x₂ x₃) = {!!}
    act-weak-ana apt F (AAConLam2 x₂ x₃) = {!!}
    act-weak-ana apt F (AAConNumlit x₁) = AAConNumlit x₁
    act-weak-ana apt F (AAFinish x₁) = AAFinish (wt-weak-ana apt F x₁)
    act-weak-ana apt F (AAZipLam x₂ x₃ d) = AAZipLam (lem-extend {!!} {!!}) x₃ (act-weak-ana {!!} {!!} d)


  -- what about transitivity / cut elimination?

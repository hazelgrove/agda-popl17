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
  -- strong form of freshness of a variable for weakening. specifically, we
  -- need to know not just that the variable we're using to extend the
  -- context doesn't appear in the context, as in a standard presentation,
  -- it can't appear anywhere in the term at all; it must be totally
  -- fresh. it's possible to drop this requirement with alpha-renaming to
  -- recover the standard description of these things, so we allow it here
  -- for convenience.
  fresh : Nat → ė → Set
  fresh x (e ·: t) = fresh x e
  fresh x (X y) = natEQp x y
  fresh x (·λ y e) = natEQp x y × fresh x e
  fresh x (N n) = ⊤
  fresh x (e1 ·+ e2) = fresh x e1 × fresh x e2
  fresh x ⦇⦈ = ⊤
  fresh x ⦇⌜ e ⌟⦈ = fresh x e
  fresh x (e1 ∘ e2) = fresh x e1 × fresh x e2
  fresh x (inl e) = fresh x e
  fresh x (inr e) = fresh x e
  fresh x (case e y e1 z e2) = natEQp x y × natEQp x z × fresh x e × fresh x e1 × fresh x e2
  fresh x ⟨ e1 , e2 ⟩ = fresh x e1 × fresh x e2
  
  ---- lemmas

  -- freshness interacts with erasure as you'd expect. the proofs below mix
  -- and match between judgmental and functional erasure as usual, so this
  -- is needed enough times to pull it out.
  fresh-er-lem : ∀{ e e◆ x} → erase-e e e◆ → fresh x (e ◆e) → fresh x e◆
  fresh-er-lem er f = tr (λ q → fresh _ q) ( ! (erasee-det er (rel◆ _))) f

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

  ---- structural properties for the well-typedness jugements
  mutual
    wt-exchange-synth : {Γ : ·ctx} {x y : Nat} {t1 t2 t : τ̇} {e : ė} →
                        {x≠y : x == y → ⊥} →
                        ((Γ ,, (x , t1)) ,, (y , t2)) ⊢ e => t →
                        ((Γ ,, (y , t2)) ,, (x , t1)) ⊢ e => t
    wt-exchange-synth {Γ} {x} {y} {t1} {t2} {t} {e} {x≠y} d =
      tr (λ q → q ⊢ e => t) (funext (lem-swap Γ x y t1 t2 {x≠y = x≠y})) d

    wt-exchange-ana : {Γ : ·ctx} {x y : Nat} {t1 t2 t : τ̇} {e : ė} →
                        (x≠y : x == y → ⊥) →
                        ((Γ ,, (x , t1)) ,, (y , t2)) ⊢ e <= t →
                        ((Γ ,, (y , t2)) ,, (x , t1)) ⊢ e <= t
    wt-exchange-ana {Γ} {x} {y} {t1} {t2} {t} {e} x≠y d =
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
                    Γ ⊢ e => t →
                    fresh x e →
                    (Γ ,, (x , t')) ⊢ e => t
    wt-weak-synth apt (SAsc x₁) f = SAsc (wt-weak-ana apt x₁ f)
    wt-weak-synth {x = x} apt (SVar {n = n} x₁) f with natEQ n x
    wt-weak-synth apt (SVar x₂) f | Inl refl = abort (somenotnone (! x₂ · apt))
    wt-weak-synth apt (SVar x₂) f | Inr x₁ = SVar (lem-extend x₁ x₂)
    wt-weak-synth apt (SAp wt x₁ x₂) (f1 , f2) = SAp (wt-weak-synth apt wt f1) x₁ (wt-weak-ana apt x₂ f2)
    wt-weak-synth apt SNum f = SNum
    wt-weak-synth apt (SPlus x₁ x₂) (f1 , f2) = SPlus (wt-weak-ana apt x₁ f1) (wt-weak-ana apt x₂ f2)
    wt-weak-synth apt SEHole f = SEHole
    wt-weak-synth apt (SNEHole wt) f = SNEHole (wt-weak-synth apt wt f)

    wt-weak-ana : {Γ : ·ctx} {x : Nat} {t t' : τ̇} {e : ė} →
                    x # Γ →
                    Γ ⊢ e <= t →
                    fresh x e →
                    (Γ ,, (x , t')) ⊢ e <= t
    wt-weak-ana apt (ASubsume x₁ x₂) f = ASubsume (wt-weak-synth apt x₁ f) x₂
    wt-weak-ana {x = x} apt (ALam {x = x₁} x₂ x₃ wt) f with natEQ x x₁
    wt-weak-ana apt (ALam x₃ x₄ wt) (f1 , _) | Inl refl = abort f1
    wt-weak-ana apt (ALam x₃ m wt) (f1 , f2) | Inr x₂ = ALam (lem-extend (flip x₂) x₃) m (wt-exchange-ana (flip x₂) (wt-weak-ana (lem-extend x₂ apt) wt f2))
    wt-weak-ana apt (AInl a b) f = AInl a (wt-weak-ana apt b f)
    wt-weak-ana apt (AInr a b) f = AInr a (wt-weak-ana apt b f)
    wt-weak-ana {x = x} apt (ACase {x = y} {y = z} a b c d e g) (f1 , f2 , f3 , f4 , f5) with natEQ x z | natEQ x y
    wt-weak-ana apt (ACase a b c d e₁ g) (f1 , f2 , f3 , f4 , f5) | Inl refl | Inl refl = abort f2
    wt-weak-ana apt (ACase a b c d e₁ g) (f1 , f2 , f3 , f4 , f5) | Inl refl | Inr x₃   = abort f2
    wt-weak-ana apt (ACase a b c d e₁ g) (f1 , f2 , f3 , f4 , f5) | Inr x₂   | Inl refl = abort f1
    wt-weak-ana {x = x} apt (ACase {x = y} {y = z}  a b c d e₁ g) (f1 , f2 , f3 , f4 , f5) | Inr x₃ | Inr x₄ = ACase (lem-extend (flip x₄) a)
                                                                                                     (lem-extend (flip x₃) b)
                                                                                                     c
                                                                                                     (wt-weak-synth apt d f3)
                                                                                                     (wt-exchange-ana (flip x₄) (wt-weak-ana (lem-extend x₄ apt) e₁ f4))
                                                                                                     (wt-exchange-ana (flip x₃) (wt-weak-ana (lem-extend x₃ apt) g f5))
    wt-weak-ana apt (AProd a b c) f = AProd a (wt-weak-ana apt b (π1 f)) (wt-weak-ana apt c (π2 f))
    
  ---- structural properties for the action jugements
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
                         fresh x (e ◆e) →
                         fresh x (e' ◆e) →
                         (d : Γ ⊢ e => t ~ α ~> e' => t') →
                         (Γ ,, (x , t'')) ⊢ e => t ~ α ~> e' => t'
    act-weak-synth apt f f' (SAMove x₁) = SAMove x₁
    act-weak-synth apt f f' SADel = SADel
    act-weak-synth apt f f' SAConAsc = SAConAsc
    act-weak-synth {x = x} apt f f' (SAConVar {x = y} p) with natEQ x y
    act-weak-synth apt f f' (SAConVar p) | Inl refl = abort (somenotnone (! p · apt))
    act-weak-synth apt f f' (SAConVar p) | Inr x₂ = SAConVar (lem-extend (flip x₂) p)
    act-weak-synth {x = x} apt f f' (SAConLam {x = y} x₂) with natEQ x y
    act-weak-synth apt f f' (SAConLam x₃) | Inl refl = abort (π1 f')
    act-weak-synth apt f f' (SAConLam x₃) | Inr x₂ = SAConLam (lem-extend (flip x₂) x₃)
    act-weak-synth apt f f' (SAConApArr x₁) = SAConApArr x₁
    act-weak-synth apt f f' (SAConApOtw x₁) = SAConApOtw x₁
    act-weak-synth apt f f' SAConNumlit = SAConNumlit
    act-weak-synth apt f f' (SAConPlus1 x₁) = SAConPlus1 x₁
    act-weak-synth apt f f' (SAConPlus2 x₁) = SAConPlus2 x₁
    act-weak-synth apt f f' SAConNEHole = SAConNEHole
    act-weak-synth apt f f' (SAFinish x₁) = SAFinish (wt-weak-synth apt x₁ f')
    act-weak-synth apt f f' (SAZipAsc1 x₁) = SAZipAsc1 (act-weak-ana apt f f' x₁)
    act-weak-synth apt f f' (SAZipAsc2 x₁ x₂ x₃ x₄) = SAZipAsc2 x₁ x₂ x₃ (wt-weak-ana apt x₄ f')
    act-weak-synth apt f f' (SAZipApArr x₁ x₂ x₃ d x₄) = SAZipApArr x₁ x₂ (wt-weak-synth apt x₃ (fresh-er-lem x₂ (π1 f)))
                                                                          (act-weak-synth apt (π1 f) (π1 f') d)
                                                                          (wt-weak-ana apt x₄ (π2 f'))
    act-weak-synth apt f f' (SAZipApAna x₁ x₂ x₃) = SAZipApAna x₁ (wt-weak-synth apt x₂ (π1 f'))
                                                                  (act-weak-ana apt (π2 f) (π2 f') x₃)
    act-weak-synth apt f f' (SAZipPlus1 x₁) = SAZipPlus1 (act-weak-ana apt (π1 f) (π1 f') x₁)
    act-weak-synth apt f f' (SAZipPlus2 x₁) = SAZipPlus2 (act-weak-ana apt (π2 f) (π2 f') x₁)
    act-weak-synth apt f f' (SAZipHole x₁ x₂ d) = SAZipHole x₁ (wt-weak-synth apt x₂ (fresh-er-lem x₁ f))
                                                               (act-weak-synth apt f f' d)
    act-weak-synth apt f f' SAConInl = SAConInl
    act-weak-synth apt f f' SAConInr = SAConInr
    act-weak-synth {x = x} apt f f' (SAConCase1 {x = y} {y = z} x₂ x₃ x₄) with natEQ x y | natEQ x z
    act-weak-synth apt f f' (SAConCase1 x₄ x₅ x₆) | Inl refl | Inl refl = abort (π1 f')
    act-weak-synth apt f f' (SAConCase1 x₄ x₅ x₆) | Inl refl | Inr x₃ = abort (π1 f')
    act-weak-synth apt f f' (SAConCase1 x₄ x₅ x₆) | Inr x₂ | Inl refl = abort (π1 (π2 f'))
    act-weak-synth apt f f' (SAConCase1 x₄ x₅ x₆) | Inr x₂ | Inr x₃ = SAConCase1 (lem-extend (flip x₂) x₄) (lem-extend (flip x₃) x₅) x₆
    act-weak-synth {x = x} apt f f' (SAConCase2 {x = y} {y = z} x₂ x₃ x₄) with natEQ x y | natEQ x z
    act-weak-synth apt f f' (SAConCase2 x₄ x₅ x₆) | Inl refl | Inl refl = abort (π1 f')
    act-weak-synth apt f f' (SAConCase2 x₄ x₅ x₆) | Inl refl | Inr x₃ = abort (π1 f')
    act-weak-synth apt f f' (SAConCase2 x₄ x₅ x₆) | Inr x₂ | Inl refl = abort (π1 (π2 f'))
    act-weak-synth apt f f' (SAConCase2 x₄ x₅ x₆) | Inr x₂ | Inr x₃ = SAConCase2 (lem-extend (flip x₂) x₄) (lem-extend (flip x₃) x₅) x₆
    act-weak-synth apt f f' SAConProd = SAConProd
    
    act-weak-ana : ∀{ Γ x t t' e e' α } →
                         x # Γ →
                         fresh x (e ◆e) →
                         fresh x (e' ◆e) →
                         (d : Γ ⊢ e ~ α ~> e' ⇐ t) →
                         (Γ ,, (x , t')) ⊢ e ~ α ~> e' ⇐ t
    act-weak-ana apt f f' (AASubsume x₁ x₂ x₃ x₄) = AASubsume x₁ (wt-weak-synth apt x₂ (fresh-er-lem x₁ f)) (act-weak-synth apt f f' x₃) x₄
    act-weak-ana apt f f' (AAMove x₁) = AAMove x₁
    act-weak-ana apt f f' AADel = AADel
    act-weak-ana apt f f' AAConAsc = AAConAsc
    act-weak-ana {x = x} apt f f' (AAConVar {x = y} x₂ p) with natEQ x y
    act-weak-ana apt f f' (AAConVar x₃ p) | Inl refl = abort (somenotnone (! p · apt))
    act-weak-ana apt f f' (AAConVar x₃ p) | Inr x₂ = AAConVar x₃ (lem-extend (flip x₂) p)
    act-weak-ana {x = x} apt f f' (AAConLam1 {x = y} x₂ x₃) with natEQ x y
    act-weak-ana apt f f' (AAConLam1 x₃ x₄) | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAConLam1 x₃ x₄) | Inr x₂ = AAConLam1 (lem-extend (flip x₂) x₃) x₄
    act-weak-ana {x = x} apt f f' (AAConLam2 {x = y} x₂ x₃) with natEQ x y
    act-weak-ana apt f f' (AAConLam2 x₃ x₄) | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAConLam2 x₃ x₄) | Inr x₂ = AAConLam2 (lem-extend (flip x₂) x₃) x₄
    act-weak-ana apt f f' (AAConNumlit x₁) = AAConNumlit x₁
    act-weak-ana apt f f' (AAFinish x₁) = AAFinish (wt-weak-ana apt x₁ f')
    act-weak-ana {x = x} apt f f' (AAZipLam {x = y} x₂ x₃ d) with natEQ x y
    act-weak-ana apt f f' (AAZipLam x₃ x₄ d) | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAZipLam x₃ x₄ d) | Inr x₂ = AAZipLam (lem-extend (flip x₂) x₃) x₄ (act-exchange-ana (flip x₂) (act-weak-ana (lem-extend x₂ apt) (π2 f) (π2 f') d))
    act-weak-ana apt f f' (AAConInl1 x₁) = AAConInl1 x₁
    act-weak-ana apt f f' (AAConInl2 x₁) = AAConInl2 x₁
    act-weak-ana apt f f' (AAConInr1 x₁) = AAConInr1 x₁
    act-weak-ana apt f f' (AAConInr2 x₁) = AAConInr2 x₁
    act-weak-ana {x = x} apt f f' (AAConCase {x = y} {y = z} x₂ x₃) with natEQ x y | natEQ x z
    act-weak-ana apt f f' (AAConCase x₄ x₅) | Inl refl | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAConCase x₄ x₅) | Inl refl | Inr x₃ = abort (π1 f')
    act-weak-ana apt f f' (AAConCase x₄ x₅) | Inr x₂   | Inl refl = abort (π1 (π2 f'))
    act-weak-ana apt f f' (AAConCase x₄ x₅) | Inr x₂   | Inr x₃ = AAConCase (lem-extend (flip x₂) x₄) (lem-extend (flip x₃) x₅)
    act-weak-ana apt f f' (AAZipInl x₁ d) = AAZipInl x₁ (act-weak-ana apt f f' d)
    act-weak-ana apt f f' (AAZipInr x₁ d) = AAZipInr x₁ (act-weak-ana apt f f' d)
    act-weak-ana {x = x} apt f f' (AAZipCase1 {x = y} {y = z} x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) with natEQ x y | natEQ x z
    act-weak-ana apt f f' (AAZipCase1 x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) | Inl refl | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAZipCase1 x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) | Inl refl | Inr x₃ = abort (π1 f')
    act-weak-ana apt f f' (AAZipCase1 x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) | Inr x₂ | Inl refl = abort (π1 (π2 f'))
    act-weak-ana apt f f' (AAZipCase1 x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) | Inr x₂ | Inr x₃ = AAZipCase1 (lem-extend (flip x₂) x₄) (lem-extend (flip x₃) x₅) x₆
                                                                                                (wt-weak-synth apt x₇ (fresh-er-lem x₆ (π1 (π2 (π2 f)))))
                                                                                                (act-weak-synth apt ((π1 (π2 (π2 f)))) (π1 (π2 (π2 f'))) x₈)
                                                                                                x₉
                                                                                                (wt-exchange-ana (flip x₂) (wt-weak-ana (lem-extend x₂ apt) x₁₀ (π1 (π2 (π2 (π2 f'))))))
                                                                                                (wt-exchange-ana (flip x₃) (wt-weak-ana (lem-extend x₃ apt) x₁₁ (π2 (π2 (π2 (π2 f'))))))
    act-weak-ana {x = x} apt f f' (AAZipCase2 {x = y} {y = z} x₂ x₃ x₄ x₅ d) with natEQ x y | natEQ x z
    act-weak-ana apt f f' (AAZipCase2 x₄ x₅ x₆ x₇ d) | Inl refl | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAZipCase2 x₄ x₅ x₆ x₇ d) | Inl refl | Inr x₃ = abort (π1 f')
    act-weak-ana apt f f' (AAZipCase2 x₄ x₅ x₆ x₇ d) | Inr x₂ | Inl refl = abort (π1 (π2 f'))
    act-weak-ana {x = x} apt f f' (AAZipCase2 {x = y} {y = z} x₄ x₅ x₆ x₇ d) | Inr x₂ | Inr x₃ = AAZipCase2 (lem-extend (flip x₂) x₄)
                                                                                    (lem-extend (flip x₃) x₅)
                                                                                    (wt-weak-synth apt x₆ (π1 (π2 (π2 f'))))
                                                                                    x₇
                                                                                    (act-exchange-ana (flip x₂) (act-weak-ana (lem-extend x₂ apt) (π1 (π2 (π2 (π2 f)))) (π1 (π2 (π2 (π2 f')))) d))
    act-weak-ana {x = x} apt f f' (AAZipCase3 {x = y} {y = z} x₂ x₃ x₄ x₅ d) with natEQ x y | natEQ x z
    act-weak-ana apt f f' (AAZipCase3 x₄ x₅ x₆ x₇ d) | Inl refl | Inl refl = abort (π1 f')
    act-weak-ana apt f f' (AAZipCase3 x₄ x₅ x₆ x₇ d) | Inl refl | Inr x₃ = abort (π1 f')
    act-weak-ana apt f f' (AAZipCase3 x₄ x₅ x₆ x₇ d) | Inr x₂ | Inl refl = abort (π1 (π2 f'))
    act-weak-ana {x = x} apt f f' (AAZipCase3 {x = y} {y = z} x₄ x₅ x₆ x₇ d) | Inr x₂ | Inr x₃ = AAZipCase3 (lem-extend (flip x₂) x₄)
                                                                                    (lem-extend (flip x₃) x₅)
                                                                                    (wt-weak-synth apt x₆ (π1 (π2 (π2 f'))))
                                                                                    x₇
                                                                                    (act-exchange-ana (flip x₃) (act-weak-ana (lem-extend x₃ apt) (π2 (π2 (π2 (π2 f)))) (π2 (π2 (π2 (π2 f')))) d))
    act-weak-ana apt f f' (AAConProd1 x₁) = AAConProd1 x₁
    act-weak-ana apt f f' (AAConProd2 x₁) = AAConProd2 x₁
    act-weak-ana apt f f' (AAZipProdL x₁ x₂) = AAZipProdL x₁ (act-weak-ana apt (π1 f) (π1 f') x₂)
    act-weak-ana apt f f' (AAZipProdR x₁ x₂) = AAZipProdR x₁ (act-weak-ana apt (π2 f) (π2 f') x₂)

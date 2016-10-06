open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase

module moveerase where
  -- type actions don't change the term other than moving the cursor
  -- around
  moveeraset : {t t' : τ̂} {δ : direction} →
            (t + move δ +> t') →
            (t ◆t) == (t' ◆t)
  moveeraset TMArrChild1 = refl
  moveeraset TMArrChild2 = refl
  moveeraset TMArrParent1 = refl
  moveeraset TMArrParent2 = refl
  moveeraset (TMArrZip1 {t2 = t2} m) = ap1 (λ x → x ==> t2) (moveeraset m)
  moveeraset (TMArrZip2 {t1 = t1} m) = ap1 (λ x → t1 ==> x) (moveeraset m)

  -- the actual movements don't change the erasure
  moveerase : {e e' : ê} {δ : direction} →
            (e + move δ +>e e') →
            (e ◆e) == (e' ◆e)
  moveerase EMAscChild1 = refl
  moveerase EMAscChild2 = refl
  moveerase EMAscParent1 = refl
  moveerase EMAscParent2 = refl
  moveerase EMLamChild1 = refl
  moveerase EMLamParent = refl
  moveerase EMPlusChild1 = refl
  moveerase EMPlusChild2 = refl
  moveerase EMPlusParent1 = refl
  moveerase EMPlusParent2 = refl
  moveerase EMApChild1 = refl
  moveerase EMApChild2 = refl
  moveerase EMApParent1 = refl
  moveerase EMApParent2 = refl
  moveerase EMNEHoleChild1 = refl
  moveerase EMNEHoleParent = refl

  -- this form is essentially the same as above, but for judgemental
  -- erasure, which is sometimes more convenient.
  moveerasee' : {e e' : ê} {e◆ : ė} {δ : direction} →
            erase-e e e◆ →
            (e + move δ +>e e') →
            erase-e e' e◆
  moveerasee' er1 m with erase-e◆ er1
  ... | refl = ◆erase-e _ _ (! (moveerase m))

  moveeraset' : ∀{ t t◆ t'' δ} →
                 erase-t t t◆ →
                 t + move δ +> t'' →
                 erase-t t'' t◆
  moveeraset' er m with erase-t◆ er
  moveeraset' er m | refl = ◆erase-t _ _ (! (moveeraset m))

  -- the type of an expression resulting from a synthetic movement action
  -- is the same is when it started.
  pin : ∀ {Γ e t e' e◆ t' δ} →
          erase-e e e◆ →
          Γ ⊢ e◆ => t →
          Γ ⊢ e => t ~ move δ ~> e' => t' →
          t == t'
  pin _ _ (SAMove x) = refl
  pin _ _ (SAZipAsc1 x) = refl
  pin _ _ (SAZipAsc2 x x₁ x₂ x₃) = eraset-det (moveeraset' x₂ x) x₁
  pin _ _ (SAZipApAna x x₁ x₂) = refl
  pin _ _ (SAZipPlus1 x) = refl
  pin _ _ (SAZipPlus2 x) = refl
  pin _ _ (SAZipHole x x₁ d) = refl
  pin (EEApL er) (SAp wt x x₁) (SAZipApArr x₂ x₃ x₄ d x₅)
    with pin x₃ x₄ d
  ... | refl with erasee-det er x₃
  ... | refl with synthunicity x₄ wt
  ... | refl with matcharrunicity x x₂
  ... | refl = refl

  -- more generally, both of the full action judgments don't do anything to
  -- corrupt what happens with the movements.
  mutual
    moveerase-synth' : ∀{Γ e e' t δ } →
                          Γ ⊢ e => t ~ move δ ~> e' => t →
                          (e ◆e) == (e' ◆e)
    moveerase-synth' (SAMove x) = moveerase x
    moveerase-synth' (SAZipAsc1 x) = ap1 (λ q → q ·: _) (moveerase-ana x)
    moveerase-synth' (SAZipAsc2 x x₁ x₂ x₃) = ap1 (λ q → _ ·: q) (moveeraset x)
    moveerase-synth' (SAZipApArr x x₁ x₂ d x₃) with pin x₁ x₂ d
    ... | refl = ap1 (λ q → q ∘ _) (moveerase-synth' d)
    moveerase-synth' (SAZipApAna x x₁ x₂) = ap1 (λ q → _ ∘ q) (moveerase-ana x₂)
    moveerase-synth' (SAZipPlus1 x) = ap1 (λ q → q ·+ _) (moveerase-ana x)
    moveerase-synth' (SAZipPlus2 x) = ap1 (λ q → _ ·+ q) (moveerase-ana x)
    moveerase-synth' (SAZipHole x x₁ d) with pin x x₁ d
    ... | refl = ap1 <|_|> (moveerase-synth' d)

    moveerase-ana : ∀{Γ e e' t δ } →
                        Γ ⊢ e ~ move δ ~> e' ⇐ t →
                        (e ◆e) == (e' ◆e)
    moveerase-ana (AASubsume x x₁ x₂ x₃) with pin x x₁ x₂
    ... | refl = moveerase-synth' x₂
    moveerase-ana (AAMove x) = moveerase x
    moveerase-ana (AAZipLam x₁ x₂ d) = ap1 (λ q → ·λ _ q) (moveerase-ana d)

  moveerase-synth : ∀{Γ e e' t t' δ } →
                       Γ ⊢ (e ◆e) => t →
                       Γ ⊢ e => t ~ move δ ~> e' => t' →
                       (e ◆e) == (e' ◆e) × t == t'
  moveerase-synth wt d with pin (rel◆ _) wt d
  moveerase-synth wt d | refl = (moveerase-synth' d) , refl

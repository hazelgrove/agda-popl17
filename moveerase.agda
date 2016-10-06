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

  -- movements don't change either the type or expression under expression
  -- actions
  mutual
    moveerase-synth : ∀{Γ e e' e◆ t t' δ } →
                       (er : erase-e e e◆) →
                       Γ ⊢ e◆ => t →
                       Γ ⊢ e => t ~ move δ ~> e' => t' →
                       (e ◆e) == (e' ◆e) × t == t'
    moveerase-synth er wt (SAMove x) = moveerase x , refl
    moveerase-synth (EEAscL er) (SAsc x) (SAZipAsc1 x₁) = ap1 (λ q → q ·: _) (moveerase-ana er x x₁) , refl
    moveerase-synth er wt (SAZipAsc2 x x₁ x₂ x₃)
      with (moveeraset x)
    ... | qq = ap1 (λ q → _ ·: q) qq , eq-ert-trans qq x₂ x₁
    moveerase-synth (EEApL er) (SAp wt x x₁) (SAZipApArr x₂ x₃ x₄ d x₅)
      with erasee-det x₃ er
    ... | refl with synthunicity wt x₄
    ... | refl with moveerase-synth er x₄ d
    ... | pp , refl with matcharrunicity x x₂
    ... | refl = (ap1 (λ q → q ∘ _) pp ) , refl
    moveerase-synth (EEApR er) (SAp wt x x₁) (SAZipApAna x₂ x₃ x₄)
      with synthunicity x₃ wt
    ... | refl with matcharrunicity x x₂
    ... | refl = ap1 (λ q → _ ∘ q)  (moveerase-ana er x₁ x₄ ) , refl
    moveerase-synth (EEPlusL er) (SPlus x x₁) (SAZipPlus1 x₂) = ap1 (λ q → q ·+ _) (moveerase-ana er x x₂)  , refl
    moveerase-synth (EEPlusR er) (SPlus x x₁) (SAZipPlus2 x₂) = ap1 (λ q → _ ·+ q) (moveerase-ana er x₁ x₂) , refl
    moveerase-synth er wt (SAZipHole x x₁ d) = ap1 <|_|> (π1 (moveerase-synth x x₁ d)) , refl

    moveerase-ana : ∀{Γ e e' e◆ t δ } →
                      (er : erase-e e e◆) →
                      Γ ⊢ e◆ <= t →
                      Γ ⊢ e ~ move δ ~> e' ⇐ t →
                      (e ◆e) == (e' ◆e)
    moveerase-ana er wt (AASubsume x x₁ x₂ x₃) = π1 (moveerase-synth x x₁ x₂)
    moveerase-ana er wt (AAMove x) = moveerase x
    moveerase-ana (EELam er) (ASubsume () x₂) _
    moveerase-ana (EELam er) (ALam x₁ x₂ wt) (AAZipLam x₃ x₄ d) with matcharrunicity x₂ x₄
    ... | refl =  ap1 (λ q → ·λ _ q) (moveerase-ana er wt d)

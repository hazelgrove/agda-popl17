open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase

module moveerase where
  -- theorem: movement doesn't change the term other than moving the cursor
  -- around.
  moveerase : {e e' : ê} {δ : direction} →
            (e + move δ +>e e') →
            (e ◆e) == (e' ◆e)
  moveerase EMAscFirstChild = refl
  moveerase EMAscParent1 = refl
  moveerase EMAscParent2 = refl
  moveerase EMAscNextSib = refl
  moveerase EMLamFirstChild = refl
  moveerase EMLamParent = refl
  moveerase EMPlusFirstChild = refl
  moveerase EMPlusParent1 = refl
  moveerase EMPlusParent2 = refl
  moveerase EMPlusNextSib = refl
  moveerase EMApFirstChild = refl
  moveerase EMApParent1 = refl
  moveerase EMApParent2 = refl
  moveerase EMApNextSib = refl
  moveerase EMNEHoleFirstChild = refl
  moveerase EMNEHoleParent = refl

  moveeraset : {t t' : τ̂} {δ : direction} →
            (t + move δ +> t') →
            (t ◆t) == (t' ◆t)
  moveeraset TMArrFirstChild = refl
  moveeraset TMArrParent1 = refl
  moveeraset TMArrParent2 = refl
  moveeraset TMArrNextSib = refl
  moveeraset (TMArrZip1 {t2 = t2} m) = ap1 (λ x → x ==> t2) (moveeraset m)
  moveeraset (TMArrZip2 {t1 = t1} m) = ap1 (λ x → t1 ==> x) (moveeraset m)

  -- this form is essentially the same as above, but for judgemental erasure
  moveerase' : {e e' : ê} {e◆ : ė} {δ : direction} →
            erase-e e e◆ →
            (e + move δ +>e e') →
            erase-e e' e◆
  moveerase' er1 m with erase-e◆ er1
  ... | refl = ◆erase-e _ _ (! (moveerase m))

  -- as a consequence, movements preserve types upto erase
  synthmove-er : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t : τ̇} {δ : direction} →
                 erase-e e e◆  →
                 erase-e e' e'◆ →
                 (e + move δ +>e e') →
                 (Γ ⊢ e◆ => t) →
                 (Γ ⊢ e'◆ => t)
  synthmove-er er1 er2 m wt with erasee-det (moveerase' er1 m) er2
  ... | refl = wt

  anamove-er : {Γ : ·ctx} {δ : direction} {e e' : ê} {e◆ e'◆ : ė} {t : τ̇} →
            erase-e e e◆ →
            erase-e e' e'◆ →
            (p : e + move δ +>e e') →
            (Γ ⊢ e◆ <= t) →
            (Γ ⊢ e'◆ <= t)
  anamove-er er1 er2 m wt with erasee-det (moveerase' er1 m) er2
  ... | refl = wt

  lem-erase-step : ∀{ t t◆ t'' δ} →
                 erase-t t t◆ →
                 t + move δ +> t'' →
                 erase-t t'' t◆
  lem-erase-step er m with erase-t◆ er
  lem-erase-step er m | refl = ◆erase-t _ _ (! (moveeraset m))

open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase

module moveerase where
  -- theorem: movement doesn't change the term other than moving the cursor
  -- around.
  moveeraset : {t t' : τ̂} {δ : direction} →
            (t + move δ +> t') →
            (t ◆t) == (t' ◆t)
  moveeraset TMArrFirstChild = refl
  moveeraset TMArrParent1 = refl
  moveeraset TMArrParent2 = refl
  moveeraset TMArrNextSib = refl
  moveeraset (TMArrZip1 {t2 = t2} m) = ap1 (λ x → x ==> t2) (moveeraset m)
  moveeraset (TMArrZip2 {t1 = t1} m) = ap1 (λ x → t1 ==> x) (moveeraset m)

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

  --- this is a restricted form of determinism that's just enough to let
  --- the lemma below go through, which is needed for reachability
  pin : ∀ {Γ e t e' e◆ t' δ} →
          erase-e e e◆ →
          Γ ⊢ e◆ => t →
          Γ ⊢ e => t ~ move δ ~> e' => t' →
          t == t'
  pin _ _ (SAMove x) = refl
  pin _ _ (SAZipAsc1 x) = refl
  pin _ _ (SAZipAsc2 x x₁ x₂ x₃) = eraset-det (lem-erase-step x₂ x) x₁
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

  -- more generally, movement actions don't change the erasure, even if
  -- they occur within a zipper
  mutual
    synth-move-er : ∀{Γ e e◆ e' t δ } →
                   erase-e e e◆ →
                   Γ ⊢ e◆ => t →
                   Γ ⊢ e => t ~ move δ ~> e' => t →
                   erase-e e' e◆
    synth-move-er er wt (SAMove x) = moveerase' er x
    synth-move-er (EEAscL er) (SAsc x) (SAZipAsc1 x₁) = EEAscL (ana-move-er er x x₁)
    synth-move-er (EEAscR x) (SAsc x₁) (SAZipAsc2 x₂ x₃ x₄ x₅) = EEAscR (lem-erase-step x₄ x₂)
    synth-move-er (EEApL er) (SAp wt x x₁) (SAZipApArr x₂ x₃ x₄ α x₅)
      with pin x₃ x₄ α
    ... | refl with erasee-det x₃ er
    ... | refl with synthunicity wt x₄
    ... | refl = EEApL (synth-move-er er wt α)
    synth-move-er (EEApR er) (SAp wt x x₁) (SAZipApAna x₂ x₃ x₄)
      with synthunicity x₃ wt
    ... | refl with matcharrunicity x₂ x
    ... | refl = EEApR (ana-move-er er x₁ x₄)
    synth-move-er (EEPlusL er) (SPlus x x₁) (SAZipPlus1 x₂) = EEPlusL (ana-move-er er x x₂)
    synth-move-er (EEPlusR er) (SPlus x x₁) (SAZipPlus2 x₂) = EEPlusR (ana-move-er er x₁ x₂)
    synth-move-er (EENEHole er) (SNEHole wt) (SAZipHole x x₁ α)
      with erasee-det x er
    ... | refl with synthunicity x₁ wt
    ... | refl with pin x x₁ α
    ... | refl = EENEHole (synth-move-er er wt α)

    ana-move-er : ∀{Γ e e◆ e' t δ } →
                        erase-e e e◆ →
                        Γ ⊢ e◆ <= t →
                        Γ ⊢ e ~ move δ ~> e' ⇐ t →
                        erase-e e' e◆
    ana-move-er (EELam _) (ASubsume () _) _

    ana-move-er er wt (AASubsume x x₁ x₂ x₃)
      with pin x x₁ x₂
    ... | refl with erasee-det er x
    ... | refl = synth-move-er x x₁ x₂
    ana-move-er er wt (AAMove x) = moveerase' er x

    ana-move-er (EELam er) (ALam x₁ x₂ wt) (AAZipLam x₃ x₄ α)
      with matcharrunicity x₄ x₂
    ... | refl = EELam (ana-move-er er wt α)

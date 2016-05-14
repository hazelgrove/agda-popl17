open import Nat
open import Prelude
open import Hazelnut-core

module Hazelnut-sensible where
  -- theorem 1: action sensibility
  synthmovelem : {Γ : ·ctx} {e e' : ê} {t : τ̇} {δ : direction} →
                 (e + move δ +>e e') →
                 (Γ ⊢ e ◆e => t) →
                 (Γ ⊢ e' ◆e => t)
  synthmovelem EMAscFirstChild d2 = d2
  synthmovelem EMAscParent1 d2 = d2
  synthmovelem EMAscParent2 d2 = d2
  synthmovelem EMAscNextSib d2 = d2
  synthmovelem EMAscPrevSib d2 = d2
  synthmovelem EMLamFirstChild d2 = d2
  synthmovelem EMLamParent d2 = d2
  synthmovelem EMPlusFirstChild d2 = d2
  synthmovelem EMPlusParent1 d2 = d2
  synthmovelem EMPlusParent2 d2 = d2
  synthmovelem EMPlusNextSib d2 = d2
  synthmovelem EMPlusPrevSib d2 = d2
  synthmovelem EMApFirstChild d2 = d2
  synthmovelem EMApParent1 d2 = d2
  synthmovelem EMApParent2 d2 = d2
  synthmovelem EMApNextSib d2 = d2
  synthmovelem EMApPrevSib d2 = d2
  synthmovelem EMFHoleFirstChild d2 = d2
  synthmovelem EMFHoleParent d2 = d2

  -- movements preserve analytic types up to erasure. this lemma seems
  -- silly because all it seems to do in each case is return the second
  -- derivation D. the pattern matching here, though, constrains what that
  -- derivation may be in each case, and is therefore actually
  -- non-trivial. it's just that most of the work is happening in the
  -- implicit arguments.
  anamovelem : {Γ : ·ctx} {δ : direction} {e e' : ê} {t : τ̇}
            (p : e + move δ +>e e') →
            (Γ ⊢ e ◆e <= t) →
            (Γ ⊢ e' ◆e <= t)
  anamovelem EMAscFirstChild d2 = d2
  anamovelem EMAscParent1 d2 = d2
  anamovelem EMAscParent2 d2 = d2
  anamovelem EMAscNextSib d2 = d2
  anamovelem EMAscPrevSib d2 = d2
  anamovelem EMLamFirstChild d2 = d2
  anamovelem EMLamParent d2 = d2
  anamovelem EMPlusFirstChild d2 = d2
  anamovelem EMPlusParent1 d2 = d2
  anamovelem EMPlusParent2 d2 = d2
  anamovelem EMPlusNextSib d2 = d2
  anamovelem EMPlusPrevSib d2 = d2
  anamovelem EMApFirstChild d2 = d2
  anamovelem EMApParent1 d2 = d2
  anamovelem EMApParent2 d2 = d2
  anamovelem EMApNextSib d2 = d2
  anamovelem EMApPrevSib d2 = d2
  anamovelem EMFHoleFirstChild d2 = d2
  anamovelem EMFHoleParent d2 = d2

  mutual
    -- if an action transforms an zexp in a synthetic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense1 : {Γ : ·ctx} {e e' : ê} {t t' : τ̇} {α : action} →
                (Γ ⊢ e => t ~ α ~> e' => t') →
                (Γ ⊢ (e  ◆e) => t) →
                 Γ ⊢ (e' ◆e) => t'
    actsense1 (SAMove x) D2 = synthmovelem x D2
    actsense1 SADel D2 = SEHole
    actsense1 SAConAsc D2 = SAsc (ASubsume D2 TCRefl)
    actsense1 (SAConVar p) D2 = SVar p
    actsense1 (SAConLam p) D2 = SAsc (ALam p (ASubsume SEHole TCRefl))
    actsense1 SAConAp1 D2 = SAp D2 (ASubsume SEHole TCHole1)
    actsense1 SAConAp2 D2 = SApHole D2 (ASubsume SEHole TCRefl)
    actsense1 (SAConAp3 x) D2 = SApHole (SFHole D2) (ASubsume SEHole TCRefl)
    actsense1 SAConArg D2 = SApHole SEHole (ASubsume D2 TCHole2)
    actsense1 SAConNumlit D2 = SNum
    actsense1 (SAConPlus1 TCRefl) D2 = SPlus (ASubsume D2 TCRefl) (ASubsume SEHole TCHole1)
    actsense1 (SAConPlus1 TCHole2) D2 = SPlus (ASubsume D2 TCHole1) (ASubsume SEHole TCHole1)
    actsense1 (SAConPlus2 x) D2 = SPlus (ASubsume (SFHole D2) TCHole1) (ASubsume SEHole TCHole1)
    actsense1 (SAFinish x) D2 = x
    actsense1 (SAZipAsc1 x) (SAsc D2) = SAsc (actsense2 x D2)
    actsense1 (SAZipAsc2 x x₁) _ = SAsc x₁
    actsense1 (SAZipAp1 x D1 x₁) D2 = SAp (actsense1 D1 x) x₁
    actsense1 (SAZipAp2 x D1 x₁) D2 = SApHole (actsense1 D1 x) x₁
    actsense1 (SAZipAp3 x x₁) (SAp D2 x₃)     with synthunicity x D2
    ... | refl = SAp x (actsense2 x₁ x₃)
    actsense1 (SAZipAp3 x x₁) (SApHole D2 x₂) with synthunicity x D2
    ... | ()
    actsense1 (SAZipAp4 x x₁) (SAp D2 x₂)     with synthunicity x D2
    ... | ()
    actsense1 (SAZipAp4 x x₁) (SApHole D2 x₂)  = SApHole x (actsense2 x₁ x₂)
    actsense1 (SAZipPlus1 x) (SPlus x₁ x₂) = SPlus (actsense2 x x₁) x₂
    actsense1 (SAZipPlus2 x) (SPlus x₁ x₂) = SPlus x₁ (actsense2 x x₂)
    actsense1 (SAZipHole1 x D1 x₁) D2 = SFHole (actsense1 D1 x)
    actsense1 (SAZipHole2 x D1) D2 = SEHole

    -- if an action transforms an zexp in an analytic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense2  : {Γ : ·ctx} {e e' : ê} {t : τ̇} {α : action} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  (Γ ⊢ (e ◆e) <= t) →
                  (Γ ⊢ (e' ◆e) <= t)
    actsense2 (AASubsume x act p) D2 = ASubsume (actsense1 act x) p
    actsense2 (AAMove x) D2 = anamovelem x D2
    actsense2 AADel _ = ASubsume SEHole TCHole1
    actsense2 AAConAsc D2 = ASubsume (SAsc D2) TCRefl
    actsense2 (AAConVar x₁ p) D2 = ASubsume (SFHole (SVar p)) TCHole1
    actsense2 (AAConLam1 p) (ASubsume SEHole TCHole1) = ALam p (ASubsume SEHole TCHole1)
    actsense2 (AAConLam2 p n~) (ASubsume SEHole TCRefl) = abort (n~ TCHole2)
    actsense2 (AAConLam2 p x₁) (ASubsume SEHole TCHole1) = ASubsume (SFHole (SAsc (ALam p (ASubsume SEHole TCRefl)))) TCHole1
    actsense2 (AAConLam2 p n~) (ASubsume SEHole TCHole2) = abort (n~ TCHole2)
    actsense2 (AAConNumlit _) _ = ASubsume (SFHole SNum) TCHole1
    actsense2 (AAFinish x) _ = x
    actsense2 (AAZipLam _ _ ) (ASubsume () _)

    actsense2 (AAZipLam x₁ (AASubsume x₂ x₃ x₄)) (ALam x₅ D2) = ALam x₅ (actsense2 (AASubsume x₂ x₃ x₄) D2)
    actsense2 (AAZipLam x₁ (AAMove x₂)) (ALam x₃ D2) = ALam x₃ (anamovelem x₂ D2)
    actsense2 (AAZipLam x₁ AADel) (ALam x₂ D2) = ALam x₂ (ASubsume SEHole TCHole1)
    actsense2 (AAZipLam x₁ AAConAsc) (ALam x₂ (ASubsume x₃ x₄)) = ALam x₂ (ASubsume (SAsc (ASubsume x₃ x₄)) TCRefl)
    actsense2 (AAZipLam x₁ AAConAsc) (ALam x₂ (ALam x₃ D2)) = ALam x₂ (ASubsume (SAsc (ALam x₃ D2)) TCRefl)
    actsense2 (AAZipLam x₁ (AAConVar x₃ p)) (ALam x₄ D2) = ALam x₄ (ASubsume (SFHole (SVar p)) TCHole1)
    actsense2 (AAZipLam x₁ (AAConLam1 x₃)) (ALam x₄ D2) = ALam x₄ (ALam x₃ (ASubsume SEHole TCHole1))
    actsense2 (AAZipLam x₁ (AAConLam2 x₃ x₄)) (ALam x₅ D2) = ALam x₅ (ASubsume (SFHole (SAsc (ALam x₃ (ASubsume SEHole TCRefl))))
                                                                        TCHole1)
    actsense2 (AAZipLam x₁ (AAConNumlit x₂)) (ALam x₃ D2) = ALam x₃ (ASubsume (SFHole SNum) TCHole1)
    actsense2 (AAZipLam x₁ (AAFinish x₂)) (ALam x₃ D2) = ALam x₃ x₂
    actsense2 (AAZipLam x₁ (AAZipLam x₃ D1)) (ALam x₄ (ASubsume () x₆))
    actsense2 (AAZipLam x₁ (AAZipLam x₃ D1)) (ALam x₄ (ALam x₅ D2)) = ALam x₄ (ALam x₃ (actsense2 D1 D2))

open import Nat
open import Prelude
open import core

module sensible where
  -- theorem: action sensibility
  synthmovelem : {Γ : ·ctx} {e e' : ê} {t : τ̇} {δ : direction} →
                 (e + move δ +>e e') →
                 (Γ ⊢ e ◆e => t) →
                 (Γ ⊢ e' ◆e => t)
  synthmovelem EMAscFirstChild d2 = d2
  synthmovelem EMAscParent1 d2 = d2
  synthmovelem EMAscParent2 d2 = d2
  synthmovelem EMAscNextSib d2 = d2
  synthmovelem EMLamFirstChild d2 = d2
  synthmovelem EMLamParent d2 = d2
  synthmovelem EMPlusFirstChild d2 = d2
  synthmovelem EMPlusParent1 d2 = d2
  synthmovelem EMPlusParent2 d2 = d2
  synthmovelem EMPlusNextSib d2 = d2
  synthmovelem EMApFirstChild d2 = d2
  synthmovelem EMApParent1 d2 = d2
  synthmovelem EMApParent2 d2 = d2
  synthmovelem EMApNextSib d2 = d2
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
  anamovelem EMLamFirstChild d2 = d2
  anamovelem EMLamParent d2 = d2
  anamovelem EMPlusFirstChild d2 = d2
  anamovelem EMPlusParent1 d2 = d2
  anamovelem EMPlusParent2 d2 = d2
  anamovelem EMPlusNextSib d2 = d2
  anamovelem EMApFirstChild d2 = d2
  anamovelem EMApParent1 d2 = d2
  anamovelem EMApParent2 d2 = d2
  anamovelem EMApNextSib d2 = d2
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
    actsense1 (SAConLam p) D2 = SAsc (ALam p MAArr (ASubsume SEHole TCRefl))
    actsense1 (SAConApArr m) D2 = SAp D2 m (ASubsume SEHole TCHole1)
    actsense1 (SAConApOtw m) D2 = SAp (SFHole D2) MAHole (ASubsume SEHole TCRefl)
    actsense1 SAConArg D2 = SAp SEHole MAHole (ASubsume D2 TCHole2)
    actsense1 SAConNumlit D2 = SNum
    actsense1 (SAConPlus1 TCRefl) D2 = SPlus (ASubsume D2 TCRefl) (ASubsume SEHole TCHole1)
    actsense1 (SAConPlus1 TCHole2) D2 = SPlus (ASubsume D2 TCHole1) (ASubsume SEHole TCHole1)
    actsense1 (SAConPlus2 x) D2 = SPlus (ASubsume (SFHole D2) TCHole1) (ASubsume SEHole TCHole1)
    actsense1 (SAFinish x) D2 = x
    actsense1 (SAZipAsc1 x) (SAsc D2) = SAsc (actsense2 x D2)
    actsense1 (SAZipAsc2 x x₁) _ = SAsc x₁
    actsense1 (SAZipApArr a b c d) D2 = SAp (actsense1 c b) a d
    actsense1 (SAZipApAna a b c) (SAp D2 x x₁)
      with synthunicity b D2
    ... | refl with matchunicity a x
    ... | refl = SAp D2 x (actsense2 c x₁)
    actsense1 (SAZipPlus1 x) (SPlus x₁ x₂) = SPlus (actsense2 x x₁) x₂
    actsense1 (SAZipPlus2 x) (SPlus x₁ x₂) = SPlus x₁ (actsense2 x x₂)
    actsense1 (SAZipHole1 x D1 x₁) D2 = SFHole (actsense1 D1 x)
    actsense1 (SAZipHole2 x D1) D2 = SEHole
    actsense1 SAConFHole D2 = SFHole D2

    -- if an action transforms an zexp in an analytic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense2  : {Γ : ·ctx} {e e' : ê} {t : τ̇} {α : action} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  (Γ ⊢ (e ◆e) <= t) →
                  (Γ ⊢ (e' ◆e) <= t)
    actsense2 (AASubsume x act p) _ = ASubsume (actsense1 act x) p
    actsense2 (AAMove x)        D2                       = anamovelem x D2
    actsense2 AADel             _                        = ASubsume SEHole TCHole1
    actsense2 AAConAsc          D2                       = ASubsume (SAsc D2) TCRefl
    actsense2 (AAConVar _ p)    _                        = ASubsume (SFHole (SVar p)) TCHole1
    actsense2 (AAConLam1 m p)  (ASubsume SEHole _)       = ALam m p (ASubsume SEHole TCHole1)
    actsense2 (AAConNumlit _)   _                        = ASubsume (SFHole SNum) TCHole1
    actsense2 (AAFinish x)      _                        = x

    actsense2 (AAConLam2 _ n~) (ASubsume SEHole TCRefl)  = abort (n~ TCHole2)
    actsense2 (AAConLam2 p _)  (ASubsume SEHole TCHole1) = ASubsume (SFHole (SAsc (ALam p MAArr (ASubsume SEHole TCRefl)))) TCHole1
    actsense2 (AAConLam2 _ n~) (ASubsume SEHole TCHole2) = abort (n~ TCHole2)

    -- all subsumptions in the right derivation are bogus, because there's no
    -- rule for lambdas synthetically
    actsense2 (AAZipLam _ _ _) (ASubsume () _)

    -- the zipper possibilities
    actsense2 (AAZipLam apt m (AASubsume {p = p} x₁ x₂ x₃)) (ALam x₄ x₅ d2) with matchunicity m x₅
    ... | refl = ALam x₄ x₅ (actsense2 (AASubsume {p = p} x₁ x₂ x₃) d2)
    actsense2 (AAZipLam apt m (AAMove x₁))          (ALam x₂ x₃ d2) = ALam x₂ x₃ (anamovelem x₁ d2)
    actsense2 (AAZipLam apt m AADel)                _               = ALam apt m (ASubsume SEHole TCHole1)
    actsense2 (AAZipLam apt m AAConAsc) (ALam x₁ x₂ (ASubsume x₃ x₄)) with matchunicity m x₂
    ... | refl = ALam x₁ x₂ (ASubsume (SAsc (ASubsume x₃ x₄)) TCRefl)
    actsense2 (AAZipLam apt m AAConAsc) (ALam x₁ x₂ (ALam x₄ x₅ d2)) with matchunicity m x₂
    ... | refl = ALam x₁ x₂ (ASubsume (SAsc (ALam x₄ x₅ d2)) TCRefl)
    actsense2 (AAZipLam apt m (AAConVar x₂ p))      (ALam x₃ x₄ d2) with matchunicity m x₄
    ... | refl = ALam x₃ x₄ (ASubsume (SFHole (SVar p)) TCHole1)
    actsense2 (AAZipLam apt m (AAConLam1 x₂ x₃))    (ALam x₄ x₅ d2) with matchunicity m x₅
    ... | refl = ALam x₄ x₅ (ALam x₂ x₃ (ASubsume SEHole TCHole1))
    actsense2 (AAZipLam apt m (AAConLam2 x₂ x₃))    (ALam x₄ x₅ d2) with matchunicity m x₅
    ... | refl = ALam x₄ x₅ (ASubsume (SFHole (SAsc (ALam x₂ MAArr (ASubsume SEHole TCRefl))))
                               TCHole1)
    actsense2 (AAZipLam apt m (AAConNumlit x₁))     (ALam x₂ x₃ d2) with matchunicity m x₃
    ... | refl = ALam x₂ x₃ (ASubsume (SFHole SNum) TCHole1)
    actsense2 (AAZipLam apt m (AAFinish x₁))        (ALam x₂ x₃ d2) with matchunicity m x₃
    ... | refl = ALam x₂ x₃ x₁
    actsense2 (AAZipLam apt m (AAZipLam x₂ x₃ d1)) (ALam x₄ x₅ (ASubsume () x₇))
    actsense2 (AAZipLam apt m (AAZipLam x₂ x₃ d1)) (ALam x₄ x₅ (ALam x₆ x₇ d2)) with matchunicity m x₅
    ... | refl with matchunicity x₃ x₇
    ... | refl = ALam x₄ x₅ (ALam x₆ x₇ (actsense2 d1 d2))

open import Nat
open import Prelude
open import core
open import judgemental-erase
open import checks

module sensible where
  -- movements preserve types upto erase
  synthmovelem : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t : τ̇} {δ : direction} →
                 erase-e e e◆  →
                 erase-e e' e'◆ →
                 (e + move δ +>e e') →
                 (Γ ⊢ e◆ => t) →
                 (Γ ⊢ e'◆ => t)
  synthmovelem {Γ = Γ} {t = t} er1 er2 m wt with erase-e◆ er1 | erase-e◆ er2
  ... | refl | refl = {!!} -- tr (λ x → Γ ⊢ x => t) (moveerase m)

  anamovelem : {Γ : ·ctx} {δ : direction} {e e' : ê} {t : τ̇}
            (p : e + move δ +>e e') →
            (Γ ⊢ e ◆e <= t) →
            (Γ ⊢ e' ◆e <= t)
  anamovelem {Γ = Γ} {t = t} m = tr (λ x → Γ ⊢ x <= t) (moveerase m)

  mutual
    -- if an action transforms an zexp in a synthetic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense1 : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t t' : τ̇} {α : action} →
                erase-e e e◆  →
                erase-e e' e'◆ →
                Γ ⊢ e => t ~ α ~> e' => t' →
                Γ ⊢ e◆ => t →
                Γ ⊢ e'◆ => t'
    actsense1 er er' (SAMove x) wt = synthmovelem er er' x wt

    -- in all the nonzipper cases, the focus must be at the top for the
    -- action rule to apply, so we just build the new derivation
    -- directly. no recursion is needed; these are effectively base cases.
    actsense1 _ EETop SADel _ = SEHole
    actsense1 EETop (EEAscR ETTop) SAConAsc wt = SAsc (ASubsume wt TCRefl)
    actsense1 _ EETop (SAConVar p) _ = SVar p
    actsense1 EETop (EEAscR (ETArrL ETTop)) (SAConLam x₂) SEHole = SAsc (ALam x₂ MAArr (ASubsume SEHole TCRefl))
    actsense1 EETop (EEApR EETop) (SAConApArr x) wt = SAp wt x (ASubsume SEHole TCHole1)
    actsense1 EETop (EEApR EETop) (SAConApOtw x) wt = SAp (SNEHole wt) MAHole (ASubsume SEHole TCRefl)
    actsense1 EETop (EEApL EETop) SAConArg wt = SAp SEHole MAHole (ASubsume wt TCHole2)
    actsense1 _ EETop SAConNumlit _ = SNum
    actsense1 EETop (EEPlusR EETop) (SAConPlus1 TCRefl) wt = SPlus (ASubsume wt TCRefl) (ASubsume SEHole TCHole1)
    actsense1 EETop (EEPlusR EETop) (SAConPlus1 TCHole2) wt = SPlus (ASubsume wt TCHole1) (ASubsume SEHole TCHole1)
    actsense1 EETop (EEPlusR EETop) (SAConPlus2 x) wt = SPlus (ASubsume (SNEHole wt) TCHole1) (ASubsume SEHole TCHole1)
    actsense1 EETop (EENEHole EETop) SAConNEHole wt = SNEHole wt
    actsense1 _ EETop (SAFinish x) _ = x

    --- zipper cases. in each, we recur on the smaller action derivation,
    --- then reassemble the result
    actsense1 (EEAscL er) (EEAscL er') (SAZipAsc1 x) (SAsc x₁) = SAsc (actsense2' er er' x x₁)
    actsense1 (EEAscR x₁) (EEAscR x) (SAZipAsc2 x₂ x₃ x₄ x₅) (SAsc x₆) with eraset-det x x₃
    ... | refl = SAsc x₅

    actsense1 er (EEApL er')    (SAZipApArr x x₁ x₂ act x₃) wt with actsense1 x₁ er' act x₂
    ... | ih = SAp ih x x₃
    actsense1 (EEApR er) (EEApR er') (SAZipApAna x x₁ x₂) (SAp wt x₃ x₄)
      with synthunicity x₁ wt
    ... | refl with matchunicity x x₃
    ... | refl with actsense2' er er' x₂ x₄
    ... | ih = SAp wt x ih

    actsense1 (EEPlusL er) (EEPlusL er') (SAZipPlus1 x) (SPlus x₁ x₂) with actsense2' er er' x x₁
    ... | ih = SPlus ih x₂
    actsense1 (EEPlusR er) (EEPlusR er') (SAZipPlus2 x) (SPlus x₁ x₂) with actsense2' er er' x x₂
    ... | ih = SPlus x₁ ih

    actsense1 er (EENEHole er') (SAZipHole x x₁ act) wt with actsense1 x er' act x₁
    ... | ih = SNEHole ih



    actsense2'  : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t : τ̇} {α : action} →
                  erase-e e e◆ →
                  erase-e e' e'◆ →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  (Γ ⊢ e◆ <= t) →
                  (Γ ⊢ e'◆ <= t)
    actsense2' = {!!}


    -- if an action transforms an zexp in an analytic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense2  : {Γ : ·ctx} {e e' : ê} {t : τ̇} {α : action} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  (Γ ⊢ (e ◆e) <= t) →
                  (Γ ⊢ (e' ◆e) <= t)
    actsense2 (AASubsume a x act p) _                    = ASubsume (actsense1 a {!!} act x) p
    actsense2 (AAMove x)        D2                       = anamovelem x D2
    actsense2 AADel             _                        = ASubsume SEHole TCHole1
    actsense2 AAConAsc          D2                       = ASubsume (SAsc D2) TCRefl
    actsense2 (AAConVar _ p)    _                        = ASubsume (SNEHole (SVar p)) TCHole1
    actsense2 (AAConLam1 m p)  (ASubsume SEHole _)       = ALam m p (ASubsume SEHole TCHole1)
    actsense2 (AAConNumlit _)   _                        = ASubsume (SNEHole SNum) TCHole1
    actsense2 (AAFinish x)      _                        = x

    actsense2 (AAConLam2 _ n~) (ASubsume SEHole TCRefl)  = abort (n~ TCHole2)
    actsense2 (AAConLam2 p _)  (ASubsume SEHole TCHole1) = ASubsume (SNEHole (SAsc (ALam p MAArr (ASubsume SEHole TCRefl)))) TCHole1
    actsense2 (AAConLam2 _ n~) (ASubsume SEHole TCHole2) = abort (n~ TCHole2)

    -- all subsumptions in the right derivation are bogus, because there's no
    -- rule for lambdas synthetically
    actsense2 (AAZipLam _ _ _) (ASubsume () _)

    -- the zipper possibilities
    actsense2 (AAZipLam apt m (AASubsume a x₁ x₂ x₃)) (ALam x₄ x₅ d2)
      with matchunicity m x₅
    ... | refl = ALam x₄ m (actsense2 (AASubsume a x₁ x₂ x₃) d2)
    actsense2 (AAZipLam apt m (AAMove x₁))          (ALam x₂ x₃ d2) = ALam x₂ x₃ (anamovelem x₁ d2)
    actsense2 (AAZipLam apt m AADel)                _               = ALam apt m (ASubsume SEHole TCHole1)
    actsense2 (AAZipLam apt m AAConAsc) (ALam x₁ x₂ (ASubsume x₃ x₄)) with matchunicity m x₂
    ... | refl = ALam x₁ x₂ (ASubsume (SAsc (ASubsume x₃ x₄)) TCRefl)
    actsense2 (AAZipLam apt m AAConAsc) (ALam x₁ x₂ (ALam x₄ x₅ d2)) with matchunicity m x₂
    ... | refl = ALam x₁ x₂ (ASubsume (SAsc (ALam x₄ x₅ d2)) TCRefl)
    actsense2 (AAZipLam apt m (AAConVar x₂ p))      (ALam x₃ x₄ d2) with matchunicity m x₄
    ... | refl = ALam x₃ x₄ (ASubsume (SNEHole (SVar p)) TCHole1)
    actsense2 (AAZipLam apt m (AAConLam1 x₂ x₃))    (ALam x₄ x₅ d2) with matchunicity m x₅
    ... | refl = ALam x₄ x₅ (ALam x₂ x₃ (ASubsume SEHole TCHole1))
    actsense2 (AAZipLam apt m (AAConLam2 x₂ x₃))    (ALam x₄ x₅ d2) with matchunicity m x₅
    ... | refl = ALam x₄ x₅ (ASubsume (SNEHole (SAsc (ALam x₂ MAArr (ASubsume SEHole TCRefl))))
                               TCHole1)
    actsense2 (AAZipLam apt m (AAConNumlit x₁))     (ALam x₂ x₃ d2) with matchunicity m x₃
    ... | refl = ALam x₂ x₃ (ASubsume (SNEHole SNum) TCHole1)
    actsense2 (AAZipLam apt m (AAFinish x₁))        (ALam x₂ x₃ d2) with matchunicity m x₃
    ... | refl = ALam x₂ x₃ x₁
    actsense2 (AAZipLam apt m (AAZipLam x₂ x₃ d1)) (ALam x₄ x₅ (ASubsume () x₇))
    actsense2 (AAZipLam apt m (AAZipLam x₂ x₃ d1)) (ALam x₄ x₅ (ALam x₆ x₇ d2)) with matchunicity m x₅
    ... | refl with matchunicity x₃ x₇
    ... | refl = ALam x₄ x₅ (ALam x₆ x₇ (actsense2 d1 d2))

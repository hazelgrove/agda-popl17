open import Nat
open import Prelude
open import core
open import judgemental-erase
open import checks

module sensible where
  -- movements preserve types upto erase it doesn't change
  synthmovelem : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t : τ̇} {δ : direction} →
                 erase-e e e◆  →
                 erase-e e' e'◆ →
                 (e + move δ +>e e') →
                 (Γ ⊢ e ◆e => t) →
                 (Γ ⊢ e' ◆e => t)
  synthmovelem er1 er2 m wt = {!moveerase' er1 m!} -- tr (λ x → Γ ⊢ x => t) (moveerase m)

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
    actsense1 er er' (SAMove x) wt = {!!}
    actsense1 er EETop SADel wt = SEHole
    actsense1 EETop (EEAscR ETTop) SAConAsc wt = SAsc (ASubsume wt TCRefl)
    actsense1 er EETop (SAConVar p) wt = SVar p
    actsense1 er (EEAscR x₁) (SAConLam x₂) wt = {!x₁!}
    actsense1 er (EEApR er') (SAConApArr x) wt = {!!}
    actsense1 er (EEApR er') (SAConApOtw x) wt = {!!}
    actsense1 er (EEApL er') SAConArg wt = {!!}
    actsense1 er EETop SAConNumlit wt = {!!}
    actsense1 er (EEPlusR er') (SAConPlus1 x) wt = {!!}
    actsense1 er (EEPlusR er') (SAConPlus2 x) wt = {!!}
    actsense1 er (EENEHole er') SAConNEHole wt = {!!}
    actsense1 er EETop (SAFinish x) wt = x
    actsense1 er (EEAscL er') (SAZipAsc1 x) wt = {!!}
    actsense1 er (EEAscR x) (SAZipAsc2 x₁ x₂ x₃ x₄) wt = {!!}
    actsense1 er (EEApL er') (SAZipApArr x x₁ x₂ act x₃) wt = {!!}
    actsense1 er (EEApR er') (SAZipApAna x x₁ x₂) wt = {!!}
    actsense1 er (EEPlusL er') (SAZipPlus1 x) wt = {!!}
    actsense1 er (EEPlusR er') (SAZipPlus2 x) wt = {!!}
    actsense1 er (EENEHole er') (SAZipHole x x₁ act) wt = {!!}


    -- actsense1 (SAMove x) D2 = ? -- synthmovelem x D2
    -- actsense1 SADel D2 = ? -- SEHole
    -- actsense1 SAConAsc D2 = ? -- SAsc (ASubsume D2 TCRefl)
    -- actsense1 (SAConVar p) D2 = ? -- SVar p
    -- actsense1 (SAConLam p) D2 = ? -- SAsc (ALam p MAArr (ASubsume SEHole TCRefl))
    -- actsense1 (SAConApArr m) D2 = SAp D2 m (ASubsume SEHole TCHole1)
    -- actsense1 (SAConApOtw m) D2 = SAp (SNEHole D2) MAHole (ASubsume SEHole TCRefl)
    -- actsense1 SAConArg D2 = SAp SEHole MAHole (ASubsume D2 TCHole2)
    -- actsense1 SAConNumlit D2 = SNum
    -- actsense1 (SAConPlus1 TCRefl) D2 = SPlus (ASubsume D2 TCRefl) (ASubsume SEHole TCHole1)
    -- actsense1 (SAConPlus1 TCHole2) D2 = SPlus (ASubsume D2 TCHole1) (ASubsume SEHole TCHole1)
    -- actsense1 (SAConPlus2 x) D2 = SPlus (ASubsume (SNEHole D2) TCHole1) (ASubsume SEHole TCHole1)
    -- actsense1 (SAFinish x) D2 = x
    -- actsense1 (SAZipAsc1 x) (SAsc D2) = SAsc (actsense2 x D2)
    -- actsense1 (SAZipAsc2 a b x x₁) _ = {!!} -- SAsc x₁
    -- actsense1 (SAZipApArr a b c d e) D2 = {!!} --SAp (actsense1 c b) a d
    -- actsense1 (SAZipApAna a b c) (SAp D2 x x₁)
    --   with synthunicity b D2
    -- ... | refl with matchunicity a x
    -- ... | refl = SAp D2 x (actsense2 c x₁)
    -- actsense1 (SAZipPlus1 x) (SPlus x₁ x₂) = SPlus (actsense2 x x₁) x₂
    -- actsense1 (SAZipPlus2 x) (SPlus x₁ x₂) = SPlus x₁ (actsense2 x x₂)
    -- actsense1 (SAZipHole a x D1) D2 = {!!} -- SNEHole (actsense1 D1 x)
    -- actsense1 SAConNEHole D2 = SNEHole D2

    -- if an action transforms an zexp in an analytic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense2  : {Γ : ·ctx} {e e' : ê} {t : τ̇} {α : action} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  (Γ ⊢ (e ◆e) <= t) →
                  (Γ ⊢ (e' ◆e) <= t)
    actsense2 (AASubsume a x act p) _ =  {!!} -- ASubsume (actsense1 act x) p
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
    actsense2 (AAZipLam apt m (AASubsume a x₁ x₂ x₃)) (ALam x₄ x₅ d2) = {!!}
    --   with matchunicity m x₅
    -- ... | refl = ALam x₄ x₅ (actsense2 (AASubsume x₁ x₂ x₃) d2)
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

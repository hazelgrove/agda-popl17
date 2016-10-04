open import Nat
open import Prelude
open import core
open import judgemental-erase
open import moveerase

module sensibility where
  mutual
    -- if an action transforms a ê in a synthetic posistion to another ê,
    -- they have the same type up erasure of the cursor
    actsense-synth : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t t' : τ̇} {α : action} →
                erase-e e e◆  →
                erase-e e' e'◆ →
                Γ ⊢ e => t ~ α ~> e' => t' →
                Γ ⊢ e◆ => t →
                Γ ⊢ e'◆ => t'
    -- in the movement case, we defer to the movement erasure theorem
    actsense-synth er er' (SAMove x) wt with erasee-det (moveerase' er x) er'
    ... | refl = wt

    -- in all the nonzipper cases, the cursor must be at the top for the
    -- action rule to apply, so we just build the new derivation
    -- directly. no recursion is needed; these are effectively base cases.
    actsense-synth _ EETop SADel _ = SEHole
    actsense-synth EETop (EEAscR ETTop) SAConAsc wt = SAsc (ASubsume wt TCRefl)
    actsense-synth _ EETop (SAConVar p) _ = SVar p
    actsense-synth EETop (EEAscR (ETArrL ETTop)) (SAConLam x) SEHole = SAsc (ALam x MAArr (ASubsume SEHole TCRefl))
    actsense-synth EETop (EEApR EETop) (SAConApArr x) wt = SAp wt x (ASubsume SEHole TCHole1)
    actsense-synth EETop (EEApR EETop) (SAConApOtw x) wt = SAp (SNEHole wt) MAHole (ASubsume SEHole TCRefl)
    actsense-synth EETop (EEApL EETop) SAConArg wt = SAp SEHole MAHole (ASubsume wt TCHole2)
    actsense-synth _ EETop SAConNumlit _ = SNum
    actsense-synth EETop (EEPlusR EETop) (SAConPlus1 TCRefl) wt = SPlus (ASubsume wt TCRefl) (ASubsume SEHole TCHole1)
    actsense-synth EETop (EEPlusR EETop) (SAConPlus1 TCHole2) wt = SPlus (ASubsume wt TCHole1) (ASubsume SEHole TCHole1)
    actsense-synth EETop (EEPlusR EETop) (SAConPlus2 _) wt = SPlus (ASubsume (SNEHole wt) TCHole1) (ASubsume SEHole TCHole1)
    actsense-synth EETop (EENEHole EETop) SAConNEHole wt = SNEHole wt
    actsense-synth _ EETop (SAFinish x) _ = x

    --- zipper cases. in each, we recur on the smaller action derivation
    --- following the zipper structure, then reassemble the result
    actsense-synth (EEAscL er) (EEAscL er') (SAZipAsc1 x) (SAsc x₁)
      with actsense-ana er er' x x₁
    ... | ih = SAsc ih
    actsense-synth (EEAscR x₁) (EEAscR x) (SAZipAsc2 x₂ x₃ x₄ x₅) (SAsc x₆)
      with eraset-det x x₃
    ... | refl = SAsc x₅

    actsense-synth er (EEApL er') (SAZipApArr x x₁ x₂ act x₃) wt
      with actsense-synth x₁ er' act x₂
    ... | ih = SAp ih x x₃
    actsense-synth (EEApR er) (EEApR er') (SAZipApAna x x₁ x₂) (SAp wt x₃ x₄)
      with synthunicity x₁ wt
    ... | refl with matcharrunicity x x₃
    ... | refl with actsense-ana er er' x₂ x₄
    ... | ih = SAp wt x ih

    actsense-synth (EEPlusL er) (EEPlusL er') (SAZipPlus1 x) (SPlus x₁ x₂)
      with actsense-ana er er' x x₁
    ... | ih = SPlus ih x₂
    actsense-synth (EEPlusR er) (EEPlusR er') (SAZipPlus2 x) (SPlus x₁ x₂)
      with actsense-ana er er' x x₂
    ... | ih = SPlus x₁ ih

    actsense-synth er (EENEHole er') (SAZipHole x x₁ act) wt
      with actsense-synth x er' act x₁
    ... | ih = SNEHole ih

    -- if an action transforms an ê in an analytic posistion to another ê,
    -- they have the same type up erasure of the cursor.
    actsense-ana  : {Γ : ·ctx} {e e' : ê} {e◆ e'◆ : ė} {t : τ̇} {α : action} →
                  erase-e e  e◆ →
                  erase-e e' e'◆ →
                  Γ ⊢ e ~ α ~> e' ⇐ t →
                  Γ ⊢ e◆ <= t →
                  Γ ⊢ e'◆ <= t
    -- in the subsumption case, punt to the other theorem
    actsense-ana er1 er2 (AASubsume x x₁ x₂ x₃) _ = ASubsume (actsense-synth x er2 x₂ x₁) x₃

    -- for movement, appeal to the movement-erasure theorem
    actsense-ana er1 er2 (AAMove x) wt with erasee-det (moveerase' er1 x) er2
    ... | refl = wt

    -- in the nonzipper cases, we again know where the hole must be, so we
    -- force it and then build the relevant derivation directly.
    actsense-ana EETop EETop AADel wt = ASubsume SEHole TCHole1
    actsense-ana EETop (EEAscR ETTop) AAConAsc wt = ASubsume (SAsc wt) TCRefl
    actsense-ana EETop (EENEHole EETop) (AAConVar x₁ p) wt = ASubsume (SNEHole (SVar p)) TCHole1
    actsense-ana EETop (EELam EETop) (AAConLam1 x₁ x₂) wt = ALam x₁ x₂ (ASubsume SEHole TCHole1)
    actsense-ana EETop (EENEHole EETop) (AAConNumlit x) wt = ASubsume (SNEHole SNum) TCHole1
    actsense-ana EETop EETop (AAFinish x) wt = x
    actsense-ana EETop (EENEHole (EEAscR (ETArrL ETTop))) (AAConLam2 x _) (ASubsume SEHole q) =
                     ASubsume (SNEHole (SAsc (ALam x MAArr (ASubsume SEHole TCRefl)))) q

    -- all subsumptions in the right derivation are bogus, because there's no
    -- rule for lambdas synthetically
    actsense-ana (EELam _) (EELam _) (AAZipLam _ _ _) (ASubsume () _)

    -- that leaves only the zipper cases for lambda, where we force the
    -- forms and then recurr into the body of the lambda being checked.
    actsense-ana (EELam er1) (EELam er2) (AAZipLam x₁ x₂ act) (ALam x₄ x₅ wt)
      with matcharrunicity x₂ x₅
    ... | refl with actsense-ana er1 er2 act wt
    ... | ih = ALam x₄ x₅ ih

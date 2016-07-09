open import Nat
open import Prelude
open import core
open import judgemental-erase

module deterministic where
  -- the same action applied to the same type makes the same resultant
  -- type.
  actdet1 : {t t' t'' : τ̂} {α : action} →
            (t + α +> t') →
            (t + α +> t'') →
            (t' == t'')
  actdet1 TMFirstChild TMFirstChild = refl
  actdet1 TMParent1 TMParent1 = refl
  actdet1 TMParent1 (TMZip1 ())
  actdet1 TMParent2 TMParent2 = refl
  actdet1 TMParent2 (TMZip2 ())
  actdet1 TMNextSib TMNextSib = refl
  actdet1 TMNextSib (TMZip1 ())
  actdet1 TMDel TMDel = refl
  actdet1 TMConArrow TMConArrow = refl
  actdet1 TMConNum TMConNum = refl
  actdet1 (TMZip1 ()) TMParent1
  actdet1 (TMZip1 ()) TMNextSib
  actdet1 (TMZip1 p1) (TMZip1 p2) with actdet1 p1 p2
  ... | refl = refl
  actdet1 (TMZip2 ()) TMParent2
  actdet1 (TMZip2 p1) (TMZip2 p2) with actdet1 p1 p2
  ... | refl = refl

  -- non-movement lemmas; theses show up pervasively throughout and save a
  -- lot of pattern matching.
  lem-nomove-pars : ∀{Γ e t e' t'} → Γ ⊢ ▹ e ◃ => t ~ move parent ~> e' => t' → ⊥
  lem-nomove-pars (SAMove ())

  lem-nomove-para : ∀{Γ e t e'} → Γ ⊢ ▹ e ◃ ~ move parent ~> e' ⇐ t → ⊥
  lem-nomove-para (AASubsume e x x₁ x₂) = lem-nomove-pars x₁
  lem-nomove-para (AAMove ())

  lem-nomove-nss : ∀{Γ e t e' t'} → Γ ⊢ ▹ e ◃ => t ~ move nextSib ~> e' => t' → ⊥
  lem-nomove-nss (SAMove ())

  lem-nomove-nsa : ∀{Γ e t e'} → Γ ⊢ ▹ e ◃ ~ move nextSib ~> e' ⇐ t → ⊥
  lem-nomove-nsa (AASubsume e  x x₁ x₂) = lem-nomove-nss x₁
  lem-nomove-nsa (AAMove ())

  lem-nomove-part : ∀ {t t'} → ▹ t ◃ + move parent +> t' → ⊥
  lem-nomove-part ()

  -- all expressions only move to one other expression
  movedet : {e e' e'' : ê} {δ : direction} →
            (e + move δ +>e e') →
            (e + move δ +>e e'') →
            e' == e''
  movedet EMAscFirstChild EMAscFirstChild = refl
  movedet EMAscParent1 EMAscParent1 = refl
  movedet EMAscParent2 EMAscParent2 = refl
  movedet EMAscNextSib EMAscNextSib = refl
  movedet EMLamFirstChild EMLamFirstChild = refl
  movedet EMLamParent EMLamParent = refl
  movedet EMPlusFirstChild EMPlusFirstChild = refl
  movedet EMPlusParent1 EMPlusParent1 = refl
  movedet EMPlusParent2 EMPlusParent2 = refl
  movedet EMPlusNextSib EMPlusNextSib = refl
  movedet EMApFirstChild EMApFirstChild = refl
  movedet EMApParent1 EMApParent1 = refl
  movedet EMApParent2 EMApParent2 = refl
  movedet EMApNextSib EMApNextSib = refl
  movedet EMNEHoleFirstChild EMNEHoleFirstChild = refl
  movedet EMNEHoleParent EMNEHoleParent = refl

  -- if a move action on a synthetic action makes a new form, it's unique
  synthmovedet : {Γ : ·ctx} {e e' e'' : ê} {t' t'' : τ̇} {δ : direction} →
         (Γ ⊢ e => t' ~ move δ ~> e'' => t'') →
         (e + move δ +>e e') →
         e'' == e'
  synthmovedet (SAMove EMAscFirstChild) EMAscFirstChild = refl
  synthmovedet (SAMove EMAscParent1) EMAscParent1 = refl
  synthmovedet (SAMove EMAscParent2) EMAscParent2 = refl
  synthmovedet (SAMove EMAscNextSib) EMAscNextSib = refl
  synthmovedet (SAMove EMLamFirstChild) EMLamFirstChild = refl
  synthmovedet (SAMove EMLamParent) EMLamParent = refl
  synthmovedet (SAMove EMPlusFirstChild) EMPlusFirstChild = refl
  synthmovedet (SAMove EMPlusParent1) EMPlusParent1 = refl
  synthmovedet (SAMove EMPlusParent2) EMPlusParent2 = refl
  synthmovedet (SAMove EMPlusNextSib) EMPlusNextSib = refl
  synthmovedet (SAMove EMApFirstChild) EMApFirstChild = refl
  synthmovedet (SAMove EMApParent1) EMApParent1 = refl
  synthmovedet (SAMove EMApParent2) EMApParent2 = refl
  synthmovedet (SAMove EMApNextSib) EMApNextSib = refl
  synthmovedet (SAMove EMNEHoleFirstChild) EMNEHoleFirstChild = refl
  synthmovedet (SAMove EMNEHoleParent) EMNEHoleParent = refl
  -- all these cases lead to absurdities based on movement
  synthmovedet (SAZipAsc1 x) EMAscParent1 = abort (lem-nomove-para x)
  synthmovedet (SAZipAsc1 x) EMAscNextSib = abort (lem-nomove-nsa x)
  synthmovedet (SAZipAsc2 e1 e2 x _) EMAscParent2 = {!!} -- abort (lem-nomove-part x)
  synthmovedet (SAZipApArr e _ _ x _) EMApParent1 = {!!} --  abort (lem-nomove-pars x)
  synthmovedet (SAZipApArr e _ _ x _) EMApNextSib = {!!} -- abort (lem-nomove-nss x)
  synthmovedet (SAZipApAna _ _ x) EMApParent2   = abort (lem-nomove-para x)
  synthmovedet (SAZipPlus1 x) EMPlusParent1 = abort (lem-nomove-para x)
  synthmovedet (SAZipPlus1 x) EMPlusNextSib = abort (lem-nomove-nsa x)
  synthmovedet (SAZipPlus2 x) EMPlusParent2 = abort (lem-nomove-para x)
  synthmovedet (SAZipHole e _ x) EMNEHoleParent = {!!} -- abort (lem-nomove-pars x)

  -- these are techincal lemmas for the cases of the main theorem

  -- this two lemmas would not be needed except that currently only one of
  -- the two determinism arguments uses jugemental erasure.
  -- lem-alam : ∀{Γ x t1 t2 e} →
  --         Γ ⊢ ·λ x (e ◆e) <= (t1 ==> t2) →
  --         (Γ ,, (x , t1)) ⊢ e ◆e <= t2
  -- lem-alam (ASubsume () x₂)
  -- lem-alam (ALam x MAArr d1) = d1

  -- lem-alamh : ∀{Γ x e} →
  --         Γ ⊢ ·λ x (e ◆e) <= <||> →
  --         (Γ ,, (x , <||>)) ⊢ e ◆e <= <||>
  -- lem-alamh (ASubsume () x₂)
  -- lem-alamh (ALam x₁ MAHole d) = d

  mutual
    -- an action on an expression in a synthetic position produces one
    -- resultant expression and type.
    actdet2 : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t t' t'' : τ̇} {α : action} →
              (E : erase-e e e◆) →
              (Γ ⊢ e◆ => t) →
              (Γ ⊢ e => t ~ α ~> e'  => t') →
              (Γ ⊢ e => t ~ α ~> e'' => t'') →
              (e' == e'' × t' == t'')
    actdet2 EETop (SAsc x) (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet2 EETop (SAsc x) SADel SADel = refl , refl
    actdet2 EETop (SAsc x) SAConAsc SAConAsc = refl , refl
    actdet2 EETop (SAsc x) SAConArg SAConArg = refl , refl
    actdet2 EETop (SAsc x) (SAConPlus1 x₁) (SAConPlus1 x₂) = refl , refl
    actdet2 EETop (SAsc x) (SAConPlus1 x₁) (SAConPlus2 x₂) = abort (x₂ x₁)
    actdet2 EETop (SAsc x) (SAConPlus2 x₁) (SAConPlus1 x₂) = abort (x₁ x₂)
    actdet2 EETop (SAsc x) (SAConPlus2 x₁) (SAConPlus2 x₂) = refl , refl
    actdet2 EETop (SAsc x) (SAConApArr x₁) (SAConApArr x₂) with matchunicity x₁ x₂
    ... | refl = refl , refl
    actdet2 EETop (SAsc x) (SAConApArr x₁) (SAConApOtw x₂) = abort (x₂ (matchconsist x₁))
    actdet2 EETop (SAsc x) (SAConApOtw x₁) (SAConApArr x₂) = abort (x₁ (matchconsist x₂))
    actdet2 EETop (SAsc x) (SAConApOtw x₁) (SAConApOtw x₂) = refl , refl
    actdet2 EETop (SAsc x) SAConNEHole SAConNEHole = refl , refl

    actdet2 (EEAscL E) (SAsc x) (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet2 (EEAscL E) (SAsc x) (SAMove EMAscParent1) (SAZipAsc1 x₂) = abort (lem-nomove-para x₂)
    actdet2 (EEAscL E) (SAsc x) (SAMove EMAscNextSib) (SAZipAsc1 x₂) = abort (lem-nomove-nsa x₂)
    actdet2 (EEAscL E) (SAsc x) (SAZipAsc1 x₁) (SAMove EMAscParent1) = abort (lem-nomove-para x₁)
    actdet2 (EEAscL E) (SAsc x) (SAZipAsc1 x₁) (SAMove EMAscNextSib) = abort (lem-nomove-nsa x₁)
    actdet2 (EEAscL E) (SAsc x) (SAZipAsc1 x₁) (SAZipAsc1 x₂)
      with actdet3 {!!} (lem-erase-ana E x) x₁ x₂
    ... | refl = refl , refl

    actdet2 (EEAscR x) (SAsc x₁) (SAMove x₂) (SAMove x₃) = movedet x₂ x₃ , refl
    actdet2 (EEAscR x) (SAsc x₁) (SAMove EMAscParent2) (SAZipAsc2 _ _ _ x₄) = {!!}
    actdet2 (EEAscR x) (SAsc x₁) (SAZipAsc2 _ _ _ x₂) (SAMove EMAscParent2) = {!!}
    actdet2 (EEAscR x) (SAsc x₂) (SAZipAsc2 _ _ x₁ x₃) (SAZipAsc2 _ _ x₄ x₅) = {!!}
    --   with actdet1 x₁ x₄
    -- ... | refl = refl , refl

    actdet2 EETop (SVar x) (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet2 EETop (SVar x) SADel SADel = refl , refl
    actdet2 EETop (SVar x) SAConAsc SAConAsc = refl , refl
    actdet2 EETop (SVar x) SAConArg SAConArg = refl , refl
    actdet2 EETop (SVar x) (SAConPlus1 x₁) (SAConPlus1 x₂) = refl , refl
    actdet2 EETop (SVar x) (SAConPlus1 x₁) (SAConPlus2 x₂) = abort (x₂ x₁)
    actdet2 EETop (SVar x) (SAConPlus2 x₁) (SAConPlus1 x₂) = abort (x₁ x₂)
    actdet2 EETop (SVar x) (SAConPlus2 x₁) (SAConPlus2 x₂) = refl , refl
    actdet2 EETop (SVar x) (SAConApArr x₁) (SAConApArr x₂) with matchunicity x₁ x₂
    ... | refl = refl , refl
    actdet2 EETop (SVar x) (SAConApArr x₁) (SAConApOtw x₂) = abort (x₂ (matchconsist x₁))
    actdet2 EETop (SVar x) (SAConApOtw x₁) (SAConApArr x₂) = abort (x₁ (matchconsist x₂))
    actdet2 EETop (SVar x) (SAConApOtw x₁) (SAConApOtw x₂) = refl , refl
    actdet2 EETop (SVar x) SAConNEHole SAConNEHole = refl , refl

    actdet2 EETop (SAp m wt x) (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet2 EETop (SAp m wt x) SADel SADel = refl , refl
    actdet2 EETop (SAp m wt x) SAConAsc SAConAsc = refl , refl
    actdet2 EETop (SAp m wt x) SAConArg SAConArg = refl , refl
    actdet2 EETop (SAp m wt x) (SAConPlus1 x₁) (SAConPlus1 x₂) = refl , refl
    actdet2 EETop (SAp m wt x) (SAConPlus1 x₁) (SAConPlus2 x₂) = abort (x₂ x₁)
    actdet2 EETop (SAp m wt x) (SAConPlus2 x₁) (SAConPlus1 x₂) = abort (x₁ x₂)
    actdet2 EETop (SAp m wt x) (SAConPlus2 x₁) (SAConPlus2 x₂) = refl , refl
    actdet2 EETop (SAp m wt x) (SAConApArr x₁) (SAConApArr x₂) with matchunicity x₁ x₂
    ... | refl = refl , refl
    actdet2 EETop (SAp m wt x) (SAConApArr x₁) (SAConApOtw x₂) = abort (x₂ (matchconsist x₁))
    actdet2 EETop (SAp m wt x) (SAConApOtw x₁) (SAConApArr x₂) = abort (x₁ (matchconsist x₂))
    actdet2 EETop (SAp m wt x) (SAConApOtw x₁) (SAConApOtw x₂) = refl , refl
    actdet2 EETop (SAp m wt x) SAConNEHole SAConNEHole = refl , refl

    actdet2 (EEApL E) (SAp m wt x) (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet2 (EEApL E) (SAp m wt x) (SAMove EMApParent1) (SAZipApArr _ x₂ x₃ d2 x₄) = abort (lem-nomove-pars d2)
    actdet2 (EEApL E) (SAp m wt x) (SAMove EMApNextSib) (SAZipApArr _ x₂ x₃ d2 x₄) = abort (lem-nomove-nss d2)
    actdet2 (EEApL E) (SAp m wt x) (SAZipApArr _ x₁ x₂ d1 x₃) (SAMove EMApParent1) = abort (lem-nomove-pars d1)
    actdet2 (EEApL E) (SAp m wt x) (SAZipApArr _ x₁ x₂ d1 x₃) (SAMove EMApNextSib) = abort (lem-nomove-nss d1)
    actdet2 (EEApL E) (SAp m wt x) (SAZipApArr _ x₁ x₂ d1 x₃) (SAZipApArr _ x₄ x₅ d2 x₆) = {!!}
    --  with synthunicity x₂ x₅
    -- ... | refl with actdet2 x₅ d1 d2
    -- ... | refl , refl with matchunicity x₁ x₄
    -- ... | refl = refl , refl

    actdet2 (EEApR E) (SAp m wt x) (SAMove x₁) (SAMove x₂) = movedet x₁ x₂ , refl
    actdet2 (EEApR E) (SAp m wt x) (SAMove EMApParent2) (SAZipApAna x₂ x₃ x₄) = abort (lem-nomove-para x₄)
    actdet2 (EEApR E) (SAp m wt x) (SAZipApAna x₁ x₂ x₃) (SAMove EMApParent2) = abort (lem-nomove-para x₃)
    actdet2 (EEApR E) (SAp m wt x) (SAZipApAna x₁ x₂ d1) (SAZipApAna x₄ x₅ d2)
     with synthunicity m x₂
    ... | refl with matchunicity x₁ wt
    ... | refl with synthunicity m x₅
    ... | refl with matchunicity x₄ wt
    ... | refl with erase-e◆ E
    ... | refl with actdet3 {!!} x d1 d2
    ... | refl = refl , refl

    actdet2 EETop SNum (SAMove x) (SAMove x₁) = movedet x x₁ , refl
    actdet2 EETop SNum SADel SADel = refl , refl
    actdet2 EETop SNum SAConAsc SAConAsc = refl , refl
    actdet2 EETop SNum SAConArg SAConArg = refl , refl
    actdet2 EETop SNum (SAConPlus1 x) (SAConPlus1 x₁) = refl , refl
    actdet2 EETop SNum (SAConPlus1 x) (SAConPlus2 x₁) = abort (x₁ x)
    actdet2 EETop SNum (SAConPlus2 x) (SAConPlus1 x₁) = abort (x x₁)
    actdet2 EETop SNum (SAConPlus2 x) (SAConPlus2 x₁) = refl , refl
    actdet2 EETop SNum (SAConApArr x) (SAConApArr x₁) with matchunicity x x₁
    ... | refl = refl , refl
    actdet2 EETop SNum (SAConApArr x) (SAConApOtw x₁) = abort (x₁ (matchconsist x))
    actdet2 EETop SNum (SAConApOtw x) (SAConApArr x₁) = abort (x (matchconsist x₁))
    actdet2 EETop SNum (SAConApOtw x) (SAConApOtw x₁) = refl , refl
    actdet2 EETop SNum SAConNEHole SAConNEHole = refl , refl

    actdet2 EETop (SPlus x x₁) (SAMove x₂) (SAMove x₃) = movedet x₂ x₃ , refl
    actdet2 EETop (SPlus x x₁) SADel SADel = refl , refl
    actdet2 EETop (SPlus x x₁) SAConAsc SAConAsc = refl , refl
    actdet2 EETop (SPlus x x₁) SAConArg SAConArg = refl , refl
    actdet2 EETop (SPlus x x₁) (SAConPlus1 x₂) (SAConPlus1 x₃) = refl , refl
    actdet2 EETop (SPlus x x₁) (SAConPlus1 x₂) (SAConPlus2 x₃) = abort (x₃ x₂)
    actdet2 EETop (SPlus x x₁) (SAConPlus2 x₂) (SAConPlus1 x₃) = abort (x₂ x₃)
    actdet2 EETop (SPlus x x₁) (SAConPlus2 x₂) (SAConPlus2 x₃) = refl , refl
    actdet2 EETop (SPlus x x₁) (SAConApArr x₂) (SAConApArr x₃) with matchunicity x₂ x₃
    ... | refl = refl , refl
    actdet2 EETop (SPlus x x₁) (SAConApArr x₂) (SAConApOtw x₃) = abort (matchnotnum x₂)
    actdet2 EETop (SPlus x x₁) (SAConApOtw x₂) (SAConApArr x₃) = abort (matchnotnum x₃)
    actdet2 EETop (SPlus x x₁) (SAConApOtw x₂) (SAConApOtw x₃) = refl , refl
    actdet2 EETop (SPlus x x₁) SAConNEHole SAConNEHole = refl , refl

    actdet2 (EEPlusL E) (SPlus x x₁) (SAMove x₂) (SAMove x₃) = movedet x₂ x₃ , refl
    actdet2 (EEPlusL E) (SPlus x x₁) (SAMove EMPlusParent1) (SAZipPlus1 d2) = abort (lem-nomove-para d2)
    actdet2 (EEPlusL E) (SPlus x x₁) (SAMove EMPlusNextSib) (SAZipPlus1 d2) = abort (lem-nomove-nsa d2)
    actdet2 (EEPlusL E) (SPlus x x₁) (SAZipPlus1 x₂) (SAMove EMPlusParent1) = abort (lem-nomove-para x₂)
    actdet2 (EEPlusL E) (SPlus x x₁) (SAZipPlus1 x₂) (SAMove EMPlusNextSib) = abort (lem-nomove-nsa x₂)
    actdet2 (EEPlusL E) (SPlus x x₁) (SAZipPlus1 x₂) (SAZipPlus1 x₃)
      = ap1 (λ x₄ → x₄ ·+₁ _) (actdet3 {!!} (lem-erase-ana E x) x₂ x₃) , refl

    actdet2 (EEPlusR E) (SPlus x x₁) (SAMove x₂) (SAMove x₃) = movedet x₂ x₃ , refl
    actdet2 (EEPlusR E) (SPlus x x₁) (SAMove EMPlusParent2) (SAZipPlus2 x₃) = abort (lem-nomove-para x₃)
    actdet2 (EEPlusR E) (SPlus x x₁) (SAZipPlus2 x₂) (SAMove EMPlusParent2) = abort (lem-nomove-para x₂)
    actdet2 (EEPlusR E) (SPlus x x₁) (SAZipPlus2 x₂) (SAZipPlus2 x₃)
      = ap1 (_·+₂_ _) (actdet3 {!!} (lem-erase-ana E x₁) x₂ x₃) , refl

    actdet2 EETop SEHole (SAMove x) (SAMove x₁) = movedet x x₁ , refl
    actdet2 EETop SEHole SADel SADel = refl , refl
    actdet2 EETop SEHole SAConAsc SAConAsc = refl , refl
    actdet2 EETop SEHole (SAConVar {Γ = G} p) (SAConVar p₁) = refl , (ctxunicity {Γ = G} p p₁)
    actdet2 EETop SEHole (SAConLam x₁) (SAConLam x₂) = refl , refl
    actdet2 EETop SEHole SAConArg SAConArg = refl , refl
    actdet2 EETop SEHole SAConNumlit SAConNumlit = refl , refl
    actdet2 EETop SEHole (SAConPlus1 x) (SAConPlus1 x₁) = refl , refl
    actdet2 EETop SEHole (SAConPlus1 x) (SAConPlus2 x₁) = abort (x₁ x)
    actdet2 EETop SEHole (SAConPlus2 x) (SAConPlus1 x₁) = abort (x x₁)
    actdet2 EETop SEHole (SAConPlus2 x) (SAConPlus2 x₁) = refl , refl
    actdet2 EETop SEHole (SAConApArr x) (SAConApArr x₁) with matchunicity x x₁
    ... | refl = refl , refl
    actdet2 EETop SEHole (SAConApArr x) (SAConApOtw x₁) = abort (x₁ TCHole2)
    actdet2 EETop SEHole (SAConApOtw x) (SAConApArr x₁) = abort (x TCHole2)
    actdet2 EETop SEHole (SAConApOtw x) (SAConApOtw x₁) = refl , refl
    actdet2 EETop SEHole SAConNEHole SAConNEHole = refl , refl

    actdet2 EETop (SNEHole wt) (SAMove x) (SAMove x₁) = movedet x x₁ , refl
    actdet2 EETop (SNEHole wt) SADel SADel = refl , refl
    actdet2 EETop (SNEHole wt) SAConAsc SAConAsc = refl , refl
    actdet2 EETop (SNEHole wt) SAConArg SAConArg = refl , refl
    actdet2 EETop (SNEHole wt) (SAConPlus1 x) (SAConPlus1 x₁) = refl , refl
    actdet2 EETop (SNEHole wt) (SAConPlus1 x) (SAConPlus2 x₁) = abort (x₁ x)
    actdet2 EETop (SNEHole wt) (SAConPlus2 x) (SAConPlus1 x₁) = abort (x x₁)
    actdet2 EETop (SNEHole wt) (SAConPlus2 x) (SAConPlus2 x₁) = refl , refl
    actdet2 EETop (SNEHole wt) (SAFinish x) (SAFinish x₁) = refl , synthunicity x x₁
    actdet2 EETop (SNEHole wt) (SAConApArr x) (SAConApArr x₁) with matchunicity x x₁
    ... | refl = refl , refl
    actdet2 EETop (SNEHole wt) (SAConApArr x) (SAConApOtw x₁) = abort (x₁ TCHole2)
    actdet2 EETop (SNEHole wt) (SAConApOtw x) (SAConApArr x₁) = abort (x TCHole2)
    actdet2 EETop (SNEHole wt) (SAConApOtw x) (SAConApOtw x₁) = refl , refl
    actdet2 EETop (SNEHole wt) SAConNEHole SAConNEHole = refl , refl

    actdet2 (EENEHole E) (SNEHole wt) (SAMove x) (SAMove x₁) = movedet x x₁ , refl
    actdet2 (EENEHole E) (SNEHole wt) (SAMove EMNEHoleParent) (SAZipHole _ x₁ d2) = abort (lem-nomove-pars d2)
    actdet2 (EENEHole E) (SNEHole wt) (SAZipHole _ x d1) (SAMove EMNEHoleParent) = abort (lem-nomove-pars d1)
    actdet2 (EENEHole E) (SNEHole wt) (SAZipHole _ x d1) (SAZipHole _ x₁ d2) = {!!}
    --   with synthunicity x x₁
    -- ... | refl with actdet2 x₁ d1 d2
    -- ... | refl , refl = refl , refl

    -- an action on an expression in an analytic position produces one
    -- resultant expression and type.
    actdet3 : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t : τ̇} {α : action} →
              -- (Γ ⊢ (e ◆e) <= t) →
              (erase-e e e◆) →
              (Γ ⊢ e◆ <= t) →
              (Γ ⊢ e ~ α ~> e' ⇐ t) →
              (Γ ⊢ e ~ α ~> e'' ⇐ t) →
              (e' == e'')
    actdet3 = {!!}
    -- actdet3 D1 (AASubsume x x₁ x₂) (AASubsume x₃ x₄ x₅)
    --  with synthunicity x x₃
    -- ... | refl = π1 (actdet2 x x₁ x₄)

    -- actdet3 D1 (AASubsume _ y _) (AAMove w) = synthmovedet y w
    -- actdet3 D1 (AASubsume _ SADel _) AADel = refl
    -- actdet3 D1 (AASubsume x SAConAsc x₂) AAConAsc = {!!}
    -- actdet3 {Γ = G} (ASubsume x x₁) (AASubsume x₂ (SAConVar p) x₄) (AAConVar x₅ p₁)
    --  with ctxunicity {Γ = G} p p₁
    -- ... | refl = abort (x₅ x₄)
    -- actdet3 D1 (AASubsume x₁ (SAConLam x₂) x₃) (AAConLam1 x x₄) = {!!}
    -- actdet3 D1 (AASubsume x₁ (SAConLam x₃) x₂) (AAConLam2 x₄ x₅) = abort (x₅ x₂)
    -- actdet3 D1 (AASubsume x SAConNumlit x₂) (AAConNumlit x₃) = abort (x₃ x₂)
    -- actdet3 D1 (AASubsume x (SAFinish x₁) x₂) (AAFinish x₃) = refl
    -- actdet3 D1 (AASubsume x₁ (SAMove EMLamParent) x₂) (AAZipLam x x₄ x₆) = abort (lem-nomove-para x₆)

    -- actdet3 D1 (AAMove x) (AASubsume x₁ x₂ x₃) =  ! (synthmovedet x₂ x)
    -- actdet3 D1 (AAMove x) (AAMove x₁) = movedet x x₁
    -- actdet3 D1 (AAMove EMLamParent) (AAZipLam x x₃ d) = abort (lem-nomove-para d)

    -- actdet3 D1 AADel (AASubsume _ SADel _) = refl
    -- actdet3 D1 AADel AADel = refl

    -- actdet3 D1 AAConAsc (AASubsume x SAConAsc x₂) = {!!}
    -- actdet3 D1 AAConAsc AAConAsc = refl

    -- actdet3 {Γ = G} D1 (AAConVar x₁ p) (AASubsume x₂ (SAConVar p₁) x₄)
    --  with ctxunicity {Γ = G} p p₁
    -- ... | refl = abort (x₁ x₄)
    -- actdet3 D1 (AAConVar x₁ p) (AAConVar x₂ p₁) = refl

    -- actdet3 D1 (AAConLam1 x x₃) (AASubsume SEHole (SAConLam x₅) x₆) = {!!}
    -- actdet3 D1 (AAConLam1 x x₁) (AAConLam1 y x₂) = refl
    -- actdet3 D1 (AAConLam1 x₁ MAHole) (AAConLam2 x₄ x₅) = abort (x₅ TCHole2)
    -- actdet3 D1 (AAConLam1 x₁ MAArr) (AAConLam2 x₄ x₅) = abort (x₅ (TCArr TCHole1 TCHole1))

    -- actdet3 D1 (AAConLam2 x₁ x₂) (AASubsume x₃ (SAConLam x₄) x₅) = abort (x₂ x₅)
    -- actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam1 y MAHole) = abort (x₂ TCHole2)
    -- actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam1 y MAArr) = abort (x₂ (TCArr TCHole1 TCHole1))
    -- actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam2 x₃ x₄) = refl

    -- actdet3 D1 (AAConNumlit x) (AASubsume x₁ SAConNumlit x₃) = abort (x x₃)
    -- actdet3 D1 (AAConNumlit x) (AAConNumlit x₁) = refl

    -- actdet3 D1 (AAFinish x) (AASubsume x₁ (SAFinish x₂) x₃) = refl
    -- actdet3 D1 (AAFinish x) (AAFinish x₁) = refl

    -- actdet3 D1 (AAZipLam x x₃ D2) (AASubsume x₁ (SAMove EMLamParent) x₄) = abort (lem-nomove-para D2)
    -- actdet3 D1 (AAZipLam x x₃ d) (AAMove EMLamParent) = abort (lem-nomove-para d)
    -- actdet3 D1 (AAZipLam {e = e} a1 MAHole D2) (AAZipLam x2 MAHole D3) with actdet3 (lem-alamh {e = e} D1) D2 D3
    -- ... | refl = refl
    -- actdet3 D1 (AAZipLam {e = e} a1 MAArr D2) (AAZipLam x2 MAArr D3) with actdet3 (lem-alam {e = e} D1) D2 D3
    -- ... | refl = refl

open import Nat
open import Prelude
open import Hazelnut-core

module Hazelnut-deterministic where
  -- theorem 2

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
  actdet1 TMPrevSib TMPrevSib = refl
  actdet1 TMPrevSib (TMZip2 ())
  actdet1 TMDel TMDel = refl
  actdet1 TMConArrow TMConArrow = refl
  actdet1 TMConNum TMConNum = refl
  actdet1 (TMZip1 ()) TMParent1
  actdet1 (TMZip1 ()) TMNextSib
  actdet1 (TMZip1 p1) (TMZip1 p2) with actdet1 p1 p2
  ... | refl = refl
  actdet1 (TMZip2 ()) TMParent2
  actdet1 (TMZip2 ()) TMPrevSib
  actdet1 (TMZip2 p1) (TMZip2 p2) with actdet1 p1 p2
  ... | refl = refl

  -- all expressions only move to one other expression
  movedet : {e e' e'' : ê} {δ : direction} →
            (e + move δ +>e e') →
            (e + move δ +>e e'') →
            e' == e''
  movedet EMAscFirstChild EMAscFirstChild = refl
  movedet EMAscParent1 EMAscParent1 = refl
  movedet EMAscParent2 EMAscParent2 = refl
  movedet EMAscNextSib EMAscNextSib = refl
  movedet EMAscPrevSib EMAscPrevSib = refl
  movedet EMLamFirstChild EMLamFirstChild = refl
  movedet EMLamParent EMLamParent = refl
  movedet EMPlusFirstChild EMPlusFirstChild = refl
  movedet EMPlusParent1 EMPlusParent1 = refl
  movedet EMPlusParent2 EMPlusParent2 = refl
  movedet EMPlusNextSib EMPlusNextSib = refl
  movedet EMPlusPrevSib EMPlusPrevSib = refl
  movedet EMApFirstChild EMApFirstChild = refl
  movedet EMApParent1 EMApParent1 = refl
  movedet EMApParent2 EMApParent2 = refl
  movedet EMApNextSib EMApNextSib = refl
  movedet EMApPrevSib EMApPrevSib = refl
  movedet EMFHoleFirstChild EMFHoleFirstChild = refl
  movedet EMFHoleParent EMFHoleParent = refl

  -- a lemma for actdet3. an arrow type given to a hole might as well be
  -- holes itself.
  lem1 : {Γ : ·ctx} {t1 t2 : τ̇} →
           Γ ⊢ <||> <= (t1 ==> t2) →
           (t1 ==> t2) ~ (<||> ==> <||>)
  lem1 (ASubsume SEHole TCHole1) = TCArr TCHole1 TCHole1

  -- a lemma for actdet3. if a move action on a synthetic action makes a
  -- new form, it's unique
  synthmovedet : {Γ : ·ctx} {e e' e'' : ê} {t' t'' : τ̇} {δ : direction} →
         (Γ ⊢ e => t' ~ move δ ~> e'' => t'') →
         (e + move δ +>e e') →
         e'' == e'
  synthmovedet (SAMove EMAscFirstChild) EMAscFirstChild = refl
  synthmovedet (SAMove EMAscParent1) EMAscParent1 = refl
  synthmovedet (SAMove EMAscParent2) EMAscParent2 = refl
  synthmovedet (SAMove EMAscNextSib) EMAscNextSib = refl
  synthmovedet (SAMove EMAscPrevSib) EMAscPrevSib = refl
  synthmovedet (SAMove EMLamFirstChild) EMLamFirstChild = refl
  synthmovedet (SAMove EMLamParent) EMLamParent = refl
  synthmovedet (SAMove EMPlusFirstChild) EMPlusFirstChild = refl
  synthmovedet (SAMove EMPlusParent1) EMPlusParent1 = refl
  synthmovedet (SAMove EMPlusParent2) EMPlusParent2 = refl
  synthmovedet (SAMove EMPlusNextSib) EMPlusNextSib = refl
  synthmovedet (SAMove EMPlusPrevSib) EMPlusPrevSib = refl
  synthmovedet (SAMove EMApFirstChild) EMApFirstChild = refl
  synthmovedet (SAMove EMApParent1) EMApParent1 = refl
  synthmovedet (SAMove EMApParent2) EMApParent2 = refl
  synthmovedet (SAMove EMApNextSib) EMApNextSib = refl
  synthmovedet (SAMove EMApPrevSib) EMApPrevSib = refl
  synthmovedet (SAMove EMFHoleFirstChild) EMFHoleFirstChild = refl
  synthmovedet (SAMove EMFHoleParent) EMFHoleParent = refl
  -- all these cases lead to absurdities after a few levels
  synthmovedet (SAZipAsc1 (AASubsume _ (SAMove ()) _)) EMAscParent1
  synthmovedet (SAZipAsc1 (AAMove ())) EMAscParent1
  synthmovedet (SAZipAsc1 (AASubsume _ (SAMove ()) _)) EMAscNextSib
  synthmovedet (SAZipAsc1 (AAMove ())) EMAscNextSib
  synthmovedet (SAZipAsc2 () _) EMAscParent2
  synthmovedet (SAZipAsc2 () _) EMAscPrevSib
  synthmovedet (SAZipAp1 _ (SAMove ()) (ASubsume _ _)) EMApParent1
  synthmovedet (SAZipAp1 _ (SAMove ()) (ALam _ _)) EMApParent1
  synthmovedet (SAZipAp1 _ (SAMove ()) _) EMApNextSib
  synthmovedet (SAZipAp2 _ (SAMove ()) _) EMApParent1
  synthmovedet (SAZipAp2 _ (SAMove ()) _) EMApNextSib
  synthmovedet (SAZipAp3 _ (AASubsume _ (SAMove ()) _)) EMApParent2
  synthmovedet (SAZipAp3 _ (AAMove ())) EMApParent2
  synthmovedet (SAZipAp3 _ (AASubsume _ (SAMove ()) _)) EMApPrevSib
  synthmovedet (SAZipAp3 _ (AAMove ())) EMApPrevSib
  synthmovedet (SAZipAp4 _ (AASubsume _ (SAMove ()) _)) EMApParent2
  synthmovedet (SAZipAp4 _ (AAMove ())) EMApParent2
  synthmovedet (SAZipAp4 _ (AASubsume _ (SAMove ()) _)) EMApPrevSib
  synthmovedet (SAZipAp4 _ (AAMove ())) EMApPrevSib
  synthmovedet (SAZipPlus1 (AASubsume _ (SAMove ()) _)) EMPlusParent1
  synthmovedet (SAZipPlus1 (AAMove ())) EMPlusParent1
  synthmovedet (SAZipPlus1 (AASubsume _ (SAMove ()) _)) EMPlusNextSib
  synthmovedet (SAZipPlus1 (AAMove ())) EMPlusNextSib
  synthmovedet (SAZipPlus2 (AASubsume _ (SAMove ()) _)) EMPlusParent2
  synthmovedet (SAZipPlus2 (AAMove ())) EMPlusParent2
  synthmovedet (SAZipPlus2 (AASubsume _ (SAMove ()) _)) EMPlusPrevSib
  synthmovedet (SAZipPlus2 (AAMove ())) EMPlusPrevSib
  synthmovedet (SAZipHole1 _ (SAMove ()) x) EMFHoleParent
  synthmovedet (SAZipHole2 _ (SAMove ())) EMFHoleParent

  lem3 : ∀{ Γ e t } → Γ ⊢ (e ·: t) <= t → Γ ⊢ e <= t
  lem3 (ASubsume (SAsc x) x₁) = x

  lem4 : ∀{ Γ e eh t t2 } →
         Γ ⊢ e ∘ (eh ◆e) => t →
         Γ ⊢ e => (t2 ==> t) →
         Γ ⊢ (eh ◆e) <= t2
  lem4 (SAp (SAsc x₁) x) (SAsc x₂) = x
  lem4 {Γ = G} (SAp (SVar x₁) x) (SVar x₂)
    with ctxunicity {Γ = G}  x₁ x₂
  ... | refl = x
  lem4 (SAp (SAp d1 x₁) x) (SAp d2 x₂)
    with synthunicity d1 d2
  ... | refl = x
  lem4 (SApHole () x) (SAsc x₁)
  lem4 {Γ = G} (SApHole (SVar x₁) x) (SVar x₂)
    with ctxunicity {Γ = G} x₁ x₂
  ... | ()
  lem4 (SApHole (SAp d1 x₁) x) (SAp d2 x₂)
    with synthunicity d1 d2
  ... | ()
  lem4 (SApHole (SApHole d1 x₁) x) (SAp d2 x₂)
    with synthunicity d1 d2
  ... | ()

  mutual
    actdet2 : {Γ : ·ctx} {e e' e'' : ê} {t t' t'' : τ̇} {α : action} →
              (Γ ⊢ (e ◆e) => t) →
              (Γ ⊢ e => t ~ α ~> e'  => t') →
              (Γ ⊢ e => t ~ α ~> e'' => t'') →
              (e' == e'' × t' == t'')
    actdet2 wt (SAMove x) (SAMove x₁) = movedet x x₁ , refl
    actdet2 wt (SAMove EMAscParent1) (SAZipAsc1 (AASubsume _ (SAMove ()) _))
    actdet2 wt (SAMove EMAscParent1) (SAZipAsc1 (AAMove ()))
    actdet2 wt (SAMove EMAscNextSib) (SAZipAsc1 (AASubsume _ (SAMove ()) _))
    actdet2 wt (SAMove EMAscNextSib) (SAZipAsc1 (AAMove ()))
    actdet2 wt (SAMove EMAscParent2) (SAZipAsc2 () x₂)
    actdet2 wt (SAMove EMAscPrevSib) (SAZipAsc2 () x₂)
    actdet2 wt (SAMove EMApParent1) (SAZipAp1 x₁ (SAMove ()) x₂)
    actdet2 wt (SAMove EMApNextSib) (SAZipAp1 x₁ (SAMove ()) x₂)
    actdet2 wt (SAMove EMApParent1) (SAZipAp2 x₁ (SAMove ()) x₂)
    actdet2 wt (SAMove EMApNextSib) (SAZipAp2 x₁ (SAMove ()) x₂)
    actdet2 wt (SAMove EMApParent2) (SAZipAp3 x₁ (AASubsume x (SAMove ()) x₃))
    actdet2 wt (SAMove EMApParent2) (SAZipAp3 x₁ (AAMove ()))
    actdet2 wt (SAMove EMApPrevSib) (SAZipAp3 x₁ (AASubsume x (SAMove ()) x₃))
    actdet2 wt (SAMove EMApPrevSib) (SAZipAp3 x₁ (AAMove ()))
    actdet2 wt (SAMove EMApParent2) (SAZipAp4 x₁ (AASubsume x (SAMove ()) x₃))
    actdet2 wt (SAMove EMApParent2) (SAZipAp4 x₁ (AAMove ()))
    actdet2 wt (SAMove EMApPrevSib) (SAZipAp4 x₁ (AASubsume x (SAMove ()) x₃))
    actdet2 wt (SAMove EMApPrevSib) (SAZipAp4 x₁ (AAMove ()))
    actdet2 wt (SAMove EMPlusParent1) (SAZipPlus1 (AASubsume x (SAMove ()) x₂))
    actdet2 wt (SAMove EMPlusParent1) (SAZipPlus1 (AAMove ()))
    actdet2 wt (SAMove EMPlusNextSib) (SAZipPlus1 (AASubsume x (SAMove ()) x₂))
    actdet2 wt (SAMove EMPlusNextSib) (SAZipPlus1 (AAMove ()))
    actdet2 wt (SAMove EMPlusParent2) (SAZipPlus2 (AASubsume x (SAMove ()) x₂))
    actdet2 wt (SAMove EMPlusParent2) (SAZipPlus2 (AAMove ()))
    actdet2 wt (SAMove EMPlusPrevSib) (SAZipPlus2 (AASubsume x (SAMove ()) x₂))
    actdet2 wt (SAMove EMPlusPrevSib) (SAZipPlus2 (AAMove ()))
    actdet2 wt (SAMove EMFHoleParent) (SAZipHole1 x₁ (SAMove ()) x₂)
    actdet2 wt (SAMove EMFHoleParent) (SAZipHole2 x₁ (SAMove ()))

    actdet2 wt SADel SADel = refl , refl

    actdet2 wt SAConAsc SAConAsc = refl , refl

    actdet2 {Γ = G} wt (SAConVar p) (SAConVar p₁)
      with ctxunicity {Γ = G} p p₁
    ... | refl = refl , refl

    actdet2 wt (SAConLam x₁) (SAConLam x₂) = refl , refl

    actdet2 wt SAConAp1 SAConAp1 = refl , refl
    actdet2 wt SAConAp1 (SAConAp3 x) = {!!} -- not sure #1

    actdet2 wt SAConAp2 SAConAp2 = refl , refl
    actdet2 wt SAConAp2 (SAConAp3 x) = abort (x TCHole2)

    actdet2 wt (SAConAp3 x) SAConAp1 = {!!} -- not sure #1 sym
    actdet2 wt (SAConAp3 x) SAConAp2 = abort (x TCHole2)
    actdet2 wt (SAConAp3 x) (SAConAp3 x₁) = refl , refl

    actdet2 wt SAConArg SAConArg = refl , refl

    actdet2 wt SAConNumlit SAConNumlit = refl , refl

    actdet2 wt (SAConPlus1 x) (SAConPlus1 x₁) = refl , refl
    actdet2 wt (SAConPlus1 x) (SAConPlus2 x₁) = abort (x₁ x)

    actdet2 wt (SAConPlus2 x) (SAConPlus1 x₁) = abort (x x₁)
    actdet2 wt (SAConPlus2 x) (SAConPlus2 x₁) = refl , refl

    actdet2 wt (SAFinish x) (SAFinish x₁)
      with synthunicity x x₁
    ... | refl = refl , refl

    actdet2 wt (SAZipAsc1 (AASubsume _ (SAMove ()) _)) (SAMove EMAscParent1)
    actdet2 wt (SAZipAsc1 (AAMove ())) (SAMove EMAscParent1)
    actdet2 wt (SAZipAsc1 x) (SAMove EMAscNextSib) = {!!} -- pattern gen problem
    actdet2 {t = t} wt (SAZipAsc1 x) (SAZipAsc1 x₁) =
         ap1 (λ q → q ·:₁ t) (actdet3 (lem3 (ASubsume wt TCRefl)) x x₁) , refl

    actdet2 wt (SAZipAsc2 () x₁) (SAMove EMAscParent2)
    actdet2 wt (SAZipAsc2 () x₁) (SAMove EMAscPrevSib)
    actdet2 wt (SAZipAsc2 x x₁) (SAZipAsc2 x₂ x₃) with actdet1 x x₂
    ... | refl = refl , refl

    actdet2 wt (SAZipAp1 x (SAMove ()) x₁) (SAMove EMApParent1)
    actdet2 wt (SAZipAp1 x (SAMove ()) x₁) (SAMove EMApNextSib)
    actdet2 wt (SAZipAp1 x d1 x₁) (SAZipAp1 x₂ d2 x₃)
      with synthunicity x₂ x
    ... | refl with actdet2 x d1 d2 -- todo: double-barrelded with should work here
    ... | p1 , refl = (ap1 (λ q → q ∘₁ _) p1) , refl
    actdet2 wt (SAZipAp1 x d1 x₁) (SAZipAp2 x₂ d2 x₃)
      with synthunicity x x₂
    ... | refl with actdet2 x d1 d2 -- todo: and here
    actdet2 wt (SAZipAp1 _ _ _ ) (SAZipAp2 _ _ _) | refl | _ , ()

    actdet2 wt (SAZipAp2 x (SAMove ()) x₁) (SAMove EMApParent1)
    actdet2 wt (SAZipAp2 x (SAMove ()) x₁) (SAMove EMApNextSib)
    actdet2 wt (SAZipAp2 x d1 x₁) (SAZipAp1 x₂ d2 x₃)
      with synthunicity x x₂
    ... | refl with actdet2 x d1 d2
    actdet2 wt (SAZipAp2 x d1 x₁) (SAZipAp1 x₂ d2 x₃) | refl | p1 , ()
    actdet2 wt (SAZipAp2 x d1 _) (SAZipAp2 x₂ d2 _)
      with synthunicity x x₂
    ... | refl = (ap1 (λ q → q ∘₁ _) (π1 (actdet2 x₂ d1 d2))) , refl

    actdet2 wt (SAZipAp3 x (AASubsume x₁ (SAMove ()) x₃)) (SAMove EMApParent2)
    actdet2 wt (SAZipAp3 x (AAMove ())) (SAMove EMApParent2)
    actdet2 wt (SAZipAp3 x x₁) (SAMove EMApPrevSib) = {!x₁!} -- p.g.p.
    actdet2 wt (SAZipAp3 {eh = eh} x x₁) (SAZipAp3 x₂ x₃)
      with synthunicity x x₂
    ... | refl = ap1 (_∘₂_ _) (actdet3 (lem4 {eh = eh} wt x) x₁ x₃) , refl
    actdet2 wt (SAZipAp3 x x₁) (SAZipAp4 x₂ x₃)
      with synthunicity x x₂
    ... | ()

    actdet2 wt (SAZipAp4 x (AASubsume x₁ (SAMove ()) x₃)) (SAMove EMApParent2)
    actdet2 wt (SAZipAp4 x (AAMove ())) (SAMove EMApParent2)
    actdet2 wt (SAZipAp4 x (AASubsume x₁ x₂ x₃)) (SAMove EMApPrevSib) = {!x₂!} -- p.g.p.
    actdet2 wt (SAZipAp4 x (AAMove ())) (SAMove EMApPrevSib)
    actdet2 wt (SAZipAp4 x x₁) (SAZipAp3 x₂ x₃)
      with synthunicity x x₂
    ... | ()
    actdet2 wt (SAZipAp4 x x₁) (SAZipAp4 x₂ x₃) = {!!}

    actdet2 wt (SAZipPlus1 x) d2 = {!!}

    actdet2 wt (SAZipPlus2 x) d2 = {!!}

    actdet2 wt (SAZipHole1 x d1 x₁) (SAMove x₂) = {!!}
    actdet2 wt (SAZipHole1 x d1 x₁) (SAZipHole1 x₂ d2 x₃) = {!!}
    actdet2 wt (SAZipHole1 x d1 x₁) (SAZipHole2 x₂ d2) = {!!}

    actdet2 wt (SAZipHole2 x d1) d2 = {!!}

    -- actions on analytic expressions produce the same expression
    actdet3 : {Γ : ·ctx} {e e' e'' : ê} {t : τ̇} {α : action} →
              (Γ ⊢ (e ◆e) <= t) →
              (Γ ⊢ e ~ α ~> e' ⇐ t) →
              (Γ ⊢ e ~ α ~> e'' ⇐ t) →
              (e' == e'')
    actdet3 D1 (AASubsume x x₁ x₂) (AASubsume x₃ x₄ x₅)
     with synthunicity x x₃
    ... | refl = π1 (actdet2 x x₁ x₄)

    actdet3 D1 (AASubsume _ y _) (AAMove w) = synthmovedet y w
    actdet3 D1 (AASubsume _ SADel _) AADel = refl
    actdet3 D1 (AASubsume x SAConAsc x₂) AAConAsc = {!!}                 -- bad kind 1
    actdet3 {Γ = G} (ASubsume x x₁) (AASubsume x₂ (SAConVar p) x₄) (AAConVar x₅ p₁)
     with ctxunicity {Γ = G} p p₁
    ... | refl = abort (x₅ x₄)
    actdet3 D1 (AASubsume x₁ (SAConLam x₂) x₃) (AAConLam1 x₄) = {!!}     -- bad kind 2
    actdet3 D1 (AASubsume x₁ (SAConLam x₃) x₂) (AAConLam2 x₄ x₅) = abort (x₅ x₂)
    actdet3 D1 (AASubsume x SAConNumlit x₂) (AAConNumlit x₃) = abort (x₃ x₂)
    actdet3 D1 (AASubsume x (SAFinish x₁) x₂) (AAFinish x₃) = refl
    actdet3 D1 (AASubsume x₁ x₃ x₂) (AAZipLam x₄ D3) = {!!}

    actdet3 D1 (AAMove x) (AASubsume x₁ x₂ x₃) =  ! (synthmovedet x₂ x)
    actdet3 D1 (AAMove x) (AAMove x₁) = movedet x x₁
    actdet3 D1 (AAMove EMLamParent) (AAZipLam x₃ (AASubsume x₁ (SAMove ()) x₄))
    actdet3 D1 (AAMove EMLamParent) (AAZipLam x₃ (AAMove ()))

    actdet3 D1 AADel (AASubsume _ SADel _) = refl
    actdet3 D1 AADel AADel = refl

    actdet3 D1 AAConAsc (AASubsume x SAConAsc x₂) = {!!}                 -- bad kind 1
    actdet3 D1 AAConAsc AAConAsc = refl

    actdet3 {Γ = G} D1 (AAConVar x₁ p) (AASubsume x₂ (SAConVar p₁) x₄)
     with ctxunicity {Γ = G} p p₁
    ... | refl = abort (x₁ x₄)
    actdet3 D1 (AAConVar x₁ p) (AAConVar x₂ p₁) = refl

    actdet3 D1 (AAConLam1 x₃) (AASubsume SEHole (SAConLam x₅) x₆) = {!!} -- bad kind 2
    actdet3 D1 (AAConLam1 x₁) (AAConLam1 x₂) = refl
    actdet3 D1 (AAConLam1 x₃) (AAConLam2 x₄ x₅) = abort (x₅ (lem1 D1))

    actdet3 D1 (AAConLam2 x₁ x₂) (AASubsume x₃ (SAConLam x₄) x₅) = abort (x₂ x₅)
    actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam1 x₃) = abort (x₂ (lem1 D1))
    actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam2 x₃ x₄) = refl

    actdet3 D1 (AAConNumlit x) (AASubsume x₁ SAConNumlit x₃) = abort (x x₃)
    actdet3 D1 (AAConNumlit x) (AAConNumlit x₁) = refl

    actdet3 D1 (AAFinish x) (AASubsume x₁ (SAFinish x₂) x₃) = refl
    actdet3 D1 (AAFinish x) (AAFinish x₁) = refl

    actdet3 D1 (AAZipLam x₃ D2) D3 = {!!}

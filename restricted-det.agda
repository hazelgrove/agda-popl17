open import Nat
open import Prelude
open import core
open import judgemental-erase
open import aasubsume-min

module restricted-det where
  -- the same action applied to the same type makes the same type
  actdet-type : {t t' t'' : τ̂} {α : action} →
            (t + α +> t') →
            (t + α +> t'') →
            (t' == t'')
  actdet-type TMArrFirstChild TMArrFirstChild = refl
  actdet-type TMArrParent1 TMArrParent1 = refl
  actdet-type TMArrParent1 (TMArrZip1 ())
  actdet-type TMArrParent2 TMArrParent2 = refl
  actdet-type TMArrParent2 (TMArrZip2 ())
  actdet-type TMArrNextSib TMArrNextSib = refl
  actdet-type TMArrNextSib (TMArrZip1 ())
  actdet-type TMDel TMDel = refl
  actdet-type TMConArrow TMConArrow = refl
  actdet-type TMConNum TMConNum = refl
  actdet-type (TMArrZip1 ()) TMArrParent1
  actdet-type (TMArrZip1 ()) TMArrNextSib
  actdet-type (TMArrZip1 p1) (TMArrZip1 p2) with actdet-type p1 p2
  ... | refl = refl
  actdet-type (TMArrZip2 ()) TMArrParent2
  actdet-type (TMArrZip2 p1) (TMArrZip2 p2) with actdet-type p1 p2
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

  -- non-movement lemmas; theses show up pervasively throughout and save a
  -- lot of pattern matching.
  lem-nomove-part : ∀ {t t'} → ▹ t ◃ + move parent +> t' → ⊥
  lem-nomove-part ()

  lem-nomove-pars : ∀{Γ e t e' t'} → Γ ⊢ ▹ e ◃ => t ~ move parent ~> e' => t' → ⊥
  lem-nomove-pars (SAMove ())

  lem-nomove-nss : ∀{Γ e t e' t'} → Γ ⊢ ▹ e ◃ => t ~ move nextSib ~> e' => t' → ⊥
  lem-nomove-nss (SAMove ())

  lem-nomove-para : ∀{Γ e t e'} → Γ ⊢ ▹ e ◃ ~ move parent ~> e' ⇐ t → ⊥
  lem-nomove-para (AASubsume e x x₁ x₂) = lem-nomove-pars x₁
  lem-nomove-para (AAMove ())

  lem-nomove-nsa : ∀{Γ e t e'} → Γ ⊢ ▹ e ◃ ~ move nextSib ~> e' ⇐ t → ⊥
  lem-nomove-nsa (AASubsume e  x x₁ x₂) = lem-nomove-nss x₁
  lem-nomove-nsa (AAMove ())

  -- if a move action on a synthetic action makes a new form, it's unique
  synthmovedet : {Γ : ·ctx} {e e' e'' : ê} {t' t'' : τ̇} {δ : direction} →
         (Γ ⊢ e => t' ~ move δ ~> e'' => t'') →
         (e + move δ +>e e') →
         e'' == e'
  synthmovedet (SAMove m1) m2 = movedet m1 m2
  -- all these cases lead to absurdities based on movement
  synthmovedet (SAZipAsc1 x) EMAscParent1         = abort (lem-nomove-para x)
  synthmovedet (SAZipAsc1 x) EMAscNextSib         = abort (lem-nomove-nsa x)
  synthmovedet (SAZipAsc2 x _ _ _) EMAscParent2   = abort (lem-nomove-part x)
  synthmovedet (SAZipApArr _ _ _ x _) EMApParent1 = abort (lem-nomove-pars x)
  synthmovedet (SAZipApArr _ _ _ x _) EMApNextSib = abort (lem-nomove-nss x)
  synthmovedet (SAZipApAna _ _ x) EMApParent2     = abort (lem-nomove-para x)
  synthmovedet (SAZipPlus1 x) EMPlusParent1       = abort (lem-nomove-para x)
  synthmovedet (SAZipPlus1 x) EMPlusNextSib       = abort (lem-nomove-nsa x)
  synthmovedet (SAZipPlus2 x) EMPlusParent2       = abort (lem-nomove-para x)
  synthmovedet (SAZipHole _ _ x) EMNEHoleParent   = abort (lem-nomove-pars x)

  anamovedet : {Γ : ·ctx} {e e' e'' : ê} {t : τ̇} {δ : direction} →
         (Γ ⊢ e ~ move δ ~> e'' ⇐ t) →
         (e + move δ +>e e') →
         e'' == e'
  anamovedet (AASubsume x₂ x x₃ x₁) m = synthmovedet x₃ m
  anamovedet (AAMove x) m = movedet x m
  anamovedet (AAZipLam x₁ x₂ d) EMLamParent = abort (lem-nomove-para d)

  same-synth :  {e' e'' : ê} {t' t'' : τ̇} {Γ : ·ctx} {e : ê} {t : τ̇}  {α : action}  →
       (d1 : Γ ⊢ e => t ~ α ~> e'  => t')
       (d2 : Γ ⊢ e => t ~ α ~> e'' => t'') → Set
  same-synth {e'} {e''} {t'} {t''} d1 d2 = (e' == e'') × (t' == t'')

  same-ana : {e' e'' : ê} {Γ : ·ctx} {e : ê} {t : τ̇} {α : action}
              (d1 : Γ ⊢ e ~ α ~> e' ⇐ t) →
              (d2 : Γ ⊢ e ~ α ~> e'' ⇐ t) → Set
  same-ana {e'} {e''} d1 d2 = e' == e''


  mutual
    -- an action on an expression in a synthetic position produces one
    -- resultant expression and type.
    resdet-synth : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t t' t'' : τ̇} {α : action} →
              (E : erase-e e e◆) →
              (wt : Γ ⊢ e◆ => t) →
              (d1 : Γ ⊢ e => t ~ α ~> e'  => t') →
              (d2 : Γ ⊢ e => t ~ α ~> e'' => t'') →
              same-synth (π1 (π2 (min-synth d1))) (π1 (π2 (min-synth d2)))
    resdet-synth E wt d1 d2 with min-synth d1 | min-synth d2
    ... | (e' , d1' , p) | (e'' , d2' , q) = {!!}

    -- an action on an expression in an analytic position produces one
    -- resultant expression and type.
    resdet-ana : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t : τ̇} {α : action} →
              (erase-e e e◆) →
              (Γ ⊢ e◆ <= t) →
              (d1 : Γ ⊢ e ~ α ~> e' ⇐ t) →
              (d2 : Γ ⊢ e ~ α ~> e'' ⇐ t) →
              (p1 : aasubmin-ana d1) →
              (p2 : aasubmin-ana d2) →
              e' == e''
    resdet-ana = {!!}

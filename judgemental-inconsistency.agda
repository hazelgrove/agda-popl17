open import Nat
open import Prelude
open import core

module judgemental-inconsistency where
  data incon : τ̇ → τ̇ → Set where
    ICNumArr1 : {t1 t2 : τ̇} → incon num (t1 ==> t2)
    ICNumArr2 : {t1 t2 : τ̇} → incon (t1 ==> t2) num
    ICNumPlus1 : {t1 t2 : τ̇} → incon num (t1 ⊕ t2)
    ICNumPlus2 : {t1 t2 : τ̇} → incon (t1 ⊕ t2) num
    ICArr1 : {t1 t2 t3 t4 : τ̇} →
               incon t1 t3 →
               incon (t1 ==> t2) (t3 ==> t4)
    ICArr2 : {t1 t2 t3 t4 : τ̇} →
               incon t2 t4 →
               incon (t1 ==> t2) (t3 ==> t4)
    ICPlus1 : {t1 t2 t3 t4 : τ̇} →
               incon t1 t3 →
               incon (t1 ⊕ t2) (t3 ⊕ t4)
    ICPlus2 : {t1 t2 t3 t4 : τ̇} →
               incon t2 t4 →
               incon (t1 ⊕ t2) (t3 ⊕ t4)
    ICPlusArr1 : {t1 t2 t3 t4 : τ̇} → incon (t1 ⊕ t2) (t3 ==> t4)
    ICPlusArr2 : {t1 t2 t3 t4 : τ̇} → incon (t1 ==> t2) (t3 ⊕ t4)

  -- inconsistency is symmetric
  inconsym : ∀ {t1 t2} → incon t1 t2 → incon t2 t1
  inconsym ICNumArr1 = ICNumArr2
  inconsym ICNumArr2 = ICNumArr1
  inconsym ICNumPlus1 = ICNumPlus2
  inconsym ICNumPlus2 = ICNumPlus1
  inconsym (ICArr1 x) = ICArr1 (inconsym x)
  inconsym (ICArr2 x) = ICArr2 (inconsym x)
  inconsym (ICPlus1 x) = ICPlus1 (inconsym x)
  inconsym (ICPlus2 x) = ICPlus2 (inconsym x)
  inconsym ICPlusArr1 = ICPlusArr2
  inconsym ICPlusArr2 = ICPlusArr1


  -- if an arrow type is ~̸, either the domain or the range must be ~̸. this
  -- is aggressively classical in flavor BUT happens to be true
  -- constructively, if only because ~ is deciable.
  lem==> : ∀{t1 t2 t3 t4} →
        (t1 ==> t2) ~̸ (t3 ==> t4) →
        (t1 ~̸ t3) + (t2 ~̸ t4)
  lem==> {t1} {t2} {t3} {t4} ncon with ~dec t1 t3
  ... | Inl x = Inr (λ x₁ → ncon (TCArr x x₁))
  ... | Inr x = Inl x

  lem⊕ : ∀{t1 t2 t3 t4} →
        (t1 ⊕ t2) ~̸ (t3 ⊕ t4) →
        (t1 ~̸ t3) + (t2 ~̸ t4)
  lem⊕ {t1} {t2} {t3} {t4} ncon with ~dec t1 t3
  ... | Inl x = Inr (λ x₁ → ncon (TCPlus x x₁))
  ... | Inr x = Inl x


  --inconsistency isn't reflexive
  incon-nrefl : ∀{t} → incon t t → ⊥
  incon-nrefl (ICArr1 x) = incon-nrefl x
  incon-nrefl (ICArr2 x) = incon-nrefl x
  incon-nrefl (ICPlus1 x) = incon-nrefl x
  incon-nrefl (ICPlus2 x) = incon-nrefl x

  -- first half of iso
  to~̸ : (t1 t2 : τ̇) → incon t1 t2 → t1 ~̸ t2
  to~̸ .num ._ ICNumArr1 ()
  to~̸ ._ .num ICNumArr2 ()
  to~̸ .num ._ ICNumPlus1 ()
  to~̸ ._ .num ICNumPlus2 ()
  to~̸ ._ ._ ICPlusArr1 ()
  to~̸ ._ ._ ICPlusArr2 ()
   -- arr cases
  to~̸ ._ ._ (ICArr1 incon) TCRefl = abort (incon-nrefl incon)
  to~̸ ._ ._ (ICArr1 incon) (TCArr x x₁) = to~̸ _ _ incon x
  to~̸ ._ ._ (ICArr2 incon) TCRefl = abort (incon-nrefl incon)
  to~̸ ._ ._ (ICArr2 incon) (TCArr x x₁) = to~̸ _ _ incon x₁
   -- plus cases
  to~̸ ._ ._ (ICPlus1 incon) TCRefl = abort (incon-nrefl incon)
  to~̸ ._ ._ (ICPlus1 incon) (TCPlus x x₁) = to~̸ _ _ incon x
  to~̸ ._ ._ (ICPlus2 incon) TCRefl = abort (incon-nrefl incon)
  to~̸ ._ ._ (ICPlus2 incon) (TCPlus x x₁) = to~̸ _ _ incon x₁


  -- second half of iso
  from~̸ : (t1 t2 : τ̇) → t1 ~̸ t2 → incon t1 t2
  from~̸ num (t2 ==> t3) ncon = ICNumArr1
  from~̸ (t1 ==> t2) num ncon = ICNumArr2
  from~̸ (t1 ==> t2) (t3 ==> t4) ncon with lem==> ncon
  ... | Inl qq = ICArr1 (from~̸ _ _ qq)
  ... | Inr qq = ICArr2 (from~̸ _ _ qq)
  from~̸ num (t1 ⊕ t2) x = ICNumPlus1
  from~̸ (t1 ⊕ t2) num _ = ICNumPlus2
  from~̸ (t1 ⊕ t2) (t3 ==> t4) _ = ICPlusArr1
  from~̸ (x ==> x₁) (t1 ⊕ t2) _ = ICPlusArr2
  from~̸ (x ⊕ x₁) (t1 ⊕ t2) ncon with lem⊕ ncon
  ... | Inl qq = ICPlus1 (from~̸ _ _ qq)
  ... | Inr qq = ICPlus2 (from~̸ _ _ qq)
  -- the remaining consistent types all lead to absurdities
  from~̸ num num ncon = abort (ncon TCRefl)
  from~̸ num ⦇⦈ ncon = abort (ncon TCHole1)
  from~̸ ⦇⦈ num ncon = abort (ncon TCHole2)
  from~̸ ⦇⦈ ⦇⦈ ncon = abort (ncon TCRefl)
  from~̸ ⦇⦈ (t2 ==> t3) ncon = abort (ncon TCHole2)
  from~̸ (t1 ==> t2) ⦇⦈ ncon = abort (ncon TCHole1)
  from~̸ (t1 ⊕ t2) ⦇⦈ ncon = abort (ncon TCHole1)
  from~̸ ⦇⦈ (t1 ⊕ t2) x = abort (x TCHole2)

  -- need to display that at least one of the round-trips above is stable
  -- for this to be structure preserving and really an iso.
  rt : (t1 t2 : τ̇) → (x : t1 ~̸ t2) → (to~̸ t1 t2 (from~̸ t1 t2 x)) == x
  rt num (t2 ==> t3) x         = funext (λ x₁ → abort (x x₁))
  rt (t1 ==> t2) num x         = funext (λ x₁ → abort (x x₁))
  rt (t1 ==> t2) (t3 ==> t4) x = funext (λ x₁ → abort (x x₁))
  rt num num x                 = abort (x TCRefl)
  rt num ⦇⦈ x                = abort (x TCHole1)
  rt ⦇⦈ num x                = abort (x TCHole2)
  rt ⦇⦈ ⦇⦈ x               = abort (x TCRefl)
  rt ⦇⦈ (t2 ==> t3) x        = abort (x TCHole2)
  rt (t1 ==> t2) ⦇⦈ x        = abort (x TCHole1)
  rt (t1 ⊕ t2) num x           = funext (λ ())
  rt (t1 ⊕ t2) ⦇⦈ x          = abort (x TCHole1)
  rt (t1 ⊕ t2) (t3 ==> t4) x   = funext (λ ())
  rt num (t1 ⊕ t2) x           = funext (λ ())
  rt ⦇⦈ (t1 ⊕ t2) x          = abort (x TCHole2)
  rt (t1 ==> t2) (t3 ⊕ t4) x   = funext (λ ())
  rt (t1 ⊕ t2) (t3 ⊕ t4) x     = funext (λ x₁ → abort (x x₁))

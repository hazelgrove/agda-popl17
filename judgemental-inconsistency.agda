open import Nat
open import Prelude
open import core

module judgemental-inconsistency where
  data incon : τ̇ → τ̇ → Set where
    ICNum1 : {t1 t2 : τ̇} → incon num (t1 ==> t2)
    ICNum2 : {t1 t2 : τ̇} → incon (t1 ==> t2) num
    ICArr1 : {t1 t2 t3 t4 : τ̇} →
               incon t1 t3 →
               incon (t1 ==> t2) (t3 ==> t4)
    ICArr2 : {t1 t2 t3 t4 : τ̇} →
               incon t2 t4 →
               incon (t1 ==> t2) (t3 ==> t4)

  -- if an arrow type is ~̸, either the domain or the range must be ~̸. this
  -- is aggressively classical in flavor BUT happens to be true
  -- constructively because only ~ is deciable.
  lem : ∀{t1 t2 t3 t4} →
        (t1 ==> t2) ~̸ (t3 ==> t4) →
        (t1 ~̸ t3) + (t2 ~̸ t4)
  lem {t1} {t2} {t3} {t4} ncon with ~dec t1 t3
  ... | Inl x = Inr (λ x₁ → ncon (TCArr x x₁))
  ... | Inr x = Inl x

  -- first half of iso
  to~̸ : (t1 t2 : τ̇) → incon t1 t2 → t1 ~̸ t2
  to~̸ num .num () TCRefl
  to~̸ num .<||> () TCHole1
  to~̸ <||> .<||> () TCRefl
  to~̸ <||> .<||> () TCHole1
  to~̸ <||> t2 () TCHole2
  to~̸ (t1 ==> t2) .(t1 ==> t2) (ICArr1 x) TCRefl = abort (to~̸ _ _ x TCRefl)
  to~̸ (t1 ==> t2) .(t1 ==> t2) (ICArr2 x) TCRefl = abort (to~̸ _ _ x TCRefl)
  to~̸ (t1 ==> t2) ._ x (TCArr x₁ x₂) = {!!}

  -- second half of iso
  from~̸ : (t1 t2 : τ̇) → t1 ~̸ t2 → incon t1 t2
  from~̸ num (t2 ==> t3) ncon = ICNum1
  from~̸ (t1 ==> t2) num ncon = ICNum2
  from~̸ (t1 ==> t2) (t3 ==> t4) ncon with lem ncon
  ... | Inl qq = ICArr1 (from~̸ _ _ qq)
  ... | Inr qq = ICArr2 (from~̸ _ _ qq)
  -- the remaining consistent types all lead to absurdities
  from~̸ num num ncon = abort (ncon TCRefl)
  from~̸ num <||> ncon = abort (ncon TCHole1)
  from~̸ <||> num ncon = abort (ncon TCHole2)
  from~̸ <||> <||> ncon = abort (ncon TCRefl)
  from~̸ <||> (t2 ==> t3) ncon = abort (ncon TCHole2)
  from~̸ (t1 ==> t2) <||> ncon = abort (ncon TCHole1)

  -- need to display that at least one of the round-trips above is stable
  -- for this to be structure preserving and really an iso.

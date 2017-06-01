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
  from~̸ (t1 ==> t2) (t3 ==> t4) ncon with ~dec t1 t3
  ... | Inl qq = ICArr2 (from~̸ t2 t4 (λ x → ncon (TCArr qq x)))
  ... | Inr qq = ICArr1 (from~̸ _ _ qq)
  from~̸ num (t1 ⊕ t2) x = ICNumPlus1
  from~̸ (t1 ⊕ t2) num _ = ICNumPlus2
  from~̸ (t1 ⊕ t2) (t3 ==> t4) _ = ICPlusArr1
  from~̸ (x ==> x₁) (t1 ⊕ t2) _ = ICPlusArr2
  from~̸ (t1 ⊕ t2) (t3 ⊕ t4) ncon with ~dec t1 t3
  ... | Inl qq = ICPlus2 (from~̸ t2 t4 (λ x → ncon (TCPlus qq x)))
  ... | Inr qq = ICPlus1 (from~̸ _ _ qq)

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
  rt1 : (t1 t2 : τ̇) → (x : t1 ~̸ t2) → (to~̸ t1 t2 (from~̸ t1 t2 x)) == x
  rt1 num (t2 ==> t3) x         = funext (λ x₁ → abort (x x₁))
  rt1 (t1 ==> t2) num x         = funext (λ x₁ → abort (x x₁))
  rt1 (t1 ==> t2) (t3 ==> t4) x = funext (λ x₁ → abort (x x₁))
  rt1 num num x                 = abort (x TCRefl)
  rt1 num ⦇⦈ x                  = abort (x TCHole1)
  rt1 ⦇⦈ num x                  = abort (x TCHole2)
  rt1 ⦇⦈ ⦇⦈ x                   = abort (x TCRefl)
  rt1 ⦇⦈ (t2 ==> t3) x          = abort (x TCHole2)
  rt1 (t1 ==> t2) ⦇⦈ x          = abort (x TCHole1)
  rt1 (t1 ⊕ t2) num x           = funext (λ ())
  rt1 (t1 ⊕ t2) ⦇⦈ x            = abort (x TCHole1)
  rt1 (t1 ⊕ t2) (t3 ==> t4) x   = funext (λ ())
  rt1 num (t1 ⊕ t2) x           = funext (λ ())
  rt1 ⦇⦈ (t1 ⊕ t2) x            = abort (x TCHole2)
  rt1 (t1 ==> t2) (t3 ⊕ t4) x   = funext (λ ())
  rt1 (t1 ⊕ t2) (t3 ⊕ t4) x     = funext (λ x₁ → abort (x x₁))


  -- if inconsistency at arrows and plusses is proof-irrelevant, then all
  -- of inconsistency is proof-irrelevant
  incon-irrelev : (arr-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ==> t2) (t3 ==> t4)) → x == y) →
                  (plus-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊕ t2) (t3 ⊕ t4)) → x == y) →
                (t1 t2 : τ̇) (x y : incon t1 t2) → x == y
  incon-irrelev arr-incon-irrelev plus-incon-irrelev .num _ ICNumArr1 ICNumArr1 = refl
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ .num ICNumArr2 ICNumArr2 = refl
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICArr1 x) (ICArr1 y) = ap1 ICArr1 (incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ x y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICArr1 x) (ICArr2 y) = arr-incon-irrelev (ICArr1 x) (ICArr2 y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICArr2 x) (ICArr1 y) = arr-incon-irrelev (ICArr2 x) (ICArr1 y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICArr2 x) (ICArr2 y) = ap1 ICArr2 (incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ x y )
  incon-irrelev arr-incon-irrelev plus-incon-irrelev .num _ ICNumPlus1 ICNumPlus1 = refl
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ .num ICNumPlus2 ICNumPlus2 = refl
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICPlus1 x) (ICPlus1 y) = ap1 ICPlus1 (incon-irrelev arr-incon-irrelev plus-incon-irrelev  _ _ x y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICPlus1 x) (ICPlus2 y) = plus-incon-irrelev (ICPlus1 x) (ICPlus2 y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICPlus2 x) (ICPlus1 y) = plus-incon-irrelev (ICPlus2 x) (ICPlus1 y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ (ICPlus2 x) (ICPlus2 y) = ap1 ICPlus2 (incon-irrelev arr-incon-irrelev plus-incon-irrelev  _ _ x y)
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ ICPlusArr1 ICPlusArr1 = refl
  incon-irrelev arr-incon-irrelev plus-incon-irrelev _ _ ICPlusArr2 ICPlusArr2 = refl

  -- if inconsistency at arrows and plusses is proof-irrelevant, then the
  -- round trip is stable up to equality
  rt2 : (arr-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ==> t2) (t3 ==> t4)) → x == y) →
        (plus-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊕ t2) (t3 ⊕ t4)) → x == y) →
        (t1 t2 : τ̇) → (x : incon t1 t2) → (from~̸ t1 t2 (to~̸ t1 t2 x)) == x
  rt2 arr-incon-irrelev plus-incon-irrelev .num _ ICNumArr1 = refl
  rt2 arr-incon-irrelev plus-incon-irrelev _ .num ICNumArr2 = refl
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ==> t2) (t3 ==> t4) (ICArr1 x) with ~dec t1 t3
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ==> t2) (t3 ==> t4) (ICArr1 x₁) | Inl x = abort (to~̸ t1 t3 x₁ x)
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ==> t2) (t3 ==> t4) (ICArr1 x₁) | Inr x = ap1 ICArr1 (incon-irrelev arr-incon-irrelev plus-incon-irrelev t1 t3 (from~̸ t1 t3 x) x₁)
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ==> t2) (t3 ==> t4) (ICArr2 x) with ~dec t1 t3
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ==> t2) (t3 ==> t4) (ICArr2 x₁) | Inl x = ap1 ICArr2 (incon-irrelev arr-incon-irrelev plus-incon-irrelev t2 t4 (from~̸ t2 t4 (to~̸ t2 t4 x₁)) x₁)
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ==> t2) (t3 ==> t4) (ICArr2 x₁) | Inr x = arr-incon-irrelev (ICArr1 (from~̸ t1 t3 x)) (ICArr2 x₁)
  rt2 arr-incon-irrelev plus-incon-irrelev .num _ ICNumPlus1 = refl
  rt2 arr-incon-irrelev plus-incon-irrelev _ .num ICNumPlus2 = refl
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus1 ic) with ~dec t1 t3
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus1 ic) | Inl x = abort (to~̸ _ _ ic x)
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus1 ic) | Inr x = ap1 ICPlus1 (incon-irrelev arr-incon-irrelev plus-incon-irrelev t1 t3 _ _ )
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus2 ic) with ~dec t1 t3
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus2 ic) | Inl x = ap1 ICPlus2 (incon-irrelev arr-incon-irrelev plus-incon-irrelev t2 t4 _ _ )
  rt2 arr-incon-irrelev plus-incon-irrelev (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus2 ic) | Inr x = plus-incon-irrelev (ICPlus1 (from~̸ t1 t3 x)) (ICPlus2 ic)
  rt2 arr-incon-irrelev plus-incon-irrelev _ _ ICPlusArr1 = refl
  rt2 arr-incon-irrelev plus-incon-irrelev _ _ ICPlusArr2 = refl

  -- if inconsistency at arrows and plusses is proof-irrelevant, then the
  -- two defintions of inconsistency are isomorphic
  incon-iso : (arr-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ==> t2) (t3 ==> t4)) → x == y)
              (plus-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊕ t2) (t3 ⊕ t4)) → x == y)
                                   → (t1 t2 : τ̇) → (incon t1 t2) ≃ (t1 ~̸ t2)
  incon-iso arr-incon-irrelev plus-incon-irrelev t1 t2 = (to~̸ t1 t2) , (from~̸ t1 t2) , (rt2 arr-incon-irrelev plus-incon-irrelev t1 t2) , (rt1 t1 t2)

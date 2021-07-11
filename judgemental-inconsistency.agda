open import Nat
open import Prelude
open import core

module judgemental-inconsistency where
  data incon : τ̇ → τ̇ → Set where
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
    ICProd1 : {t1 t2 t3 t4 : τ̇} →
               incon t1 t3 →
               incon (t1 ⊠ t2) (t3 ⊠ t4)
    ICProd2 : {t1 t2 t3 t4 : τ̇} →
               incon t2 t4 →
               incon (t1 ⊠ t2) (t3 ⊠ t4)
               
    ICNumArr : {t1 t2 : τ̇} → incon num (t1 ==> t2)
    ICNumPlus : {t1 t2 : τ̇} → incon num (t1 ⊕ t2)
    ICNumProd : {t1 t2 : τ̇} → incon num (t1 ⊠ t2)
    
    ICArrNum : {t1 t2 : τ̇} → incon (t1 ==> t2) num
    ICArrPlus : {t1 t2 t3 t4 : τ̇} → incon (t1 ==> t2) (t3 ⊕ t4)
    ICArrProd : {t1 t2 t3 t4 : τ̇} → incon (t1 ==> t2) (t3 ⊠ t4)

     
    ICPlusNum : {t1 t2 : τ̇} → incon (t1 ⊕ t2) num
    ICPlusArr : {t1 t2 t3 t4 : τ̇} → incon (t1 ⊕ t2) (t3 ==> t4)
    ICPlusProd : {t1 t2 t3 t4 : τ̇} → incon (t1 ⊕ t2) (t3 ⊠ t4)
    
    ICProdNum : {t1 t2 : τ̇} → incon (t1 ⊠ t2) num
    ICProdArr : {t1 t2 t3 t4 : τ̇} → incon (t1 ⊠ t2) (t3 ==> t4)
    ICProdPlus : {t1 t2 t3 t4 : τ̇} → incon (t1 ⊠ t2) (t3 ⊕ t4)

    
  -- inconsistency is symmetric
  inconsym : ∀ {t1 t2} → incon t1 t2 → incon t2 t1
  inconsym (ICArr1 x) = ICArr1 (inconsym x)
  inconsym (ICArr2 x) = ICArr2 (inconsym x)
  inconsym (ICPlus1 x) = ICPlus1 (inconsym x)
  inconsym (ICPlus2 x) = ICPlus2 (inconsym x)
  inconsym (ICProd1 x) = ICProd1 (inconsym x)
  inconsym (ICProd2 x) = ICProd2 (inconsym x)
  inconsym ICNumArr = ICArrNum
  inconsym ICNumPlus = ICPlusNum
  inconsym ICNumProd = ICProdNum
  inconsym ICArrNum = ICNumArr
  inconsym ICArrPlus = ICPlusArr
  inconsym ICArrProd = ICProdArr
  inconsym ICPlusNum = ICNumPlus
  inconsym ICPlusArr = ICArrPlus
  inconsym ICPlusProd = ICProdPlus
  inconsym ICProdNum = ICNumProd
  inconsym ICProdArr = ICArrProd
  inconsym ICProdPlus = ICPlusProd

  --inconsistency isn't reflexive
  incon-nrefl : ∀{t} → incon t t → ⊥
  incon-nrefl (ICArr1 x) = incon-nrefl x
  incon-nrefl (ICArr2 x) = incon-nrefl x
  incon-nrefl (ICPlus1 x) = incon-nrefl x
  incon-nrefl (ICPlus2 x) = incon-nrefl x
  incon-nrefl (ICProd1 x) = incon-nrefl x
  incon-nrefl (ICProd2 x) = incon-nrefl x
  
  -- first half of iso
  to~̸ : (t1 t2 : τ̇) → incon t1 t2 → t1 ~̸ t2
  to~̸ .num ._ ICNumArr ()
  to~̸ .num ._ ICNumPlus ()
  to~̸ .num ._ ICNumProd ()
   
  to~̸ ._ .num ICArrNum ()
  to~̸ ._ ._ ICArrPlus ()
  to~̸ ._ ._ ICArrProd ()
  
  to~̸ ._ .num ICPlusNum ()
  to~̸ ._ ._ ICPlusArr ()
  to~̸ ._ ._ ICPlusProd ()

  to~̸ ._ .num ICProdNum ()
  to~̸ ._ ._ ICProdArr ()
  to~̸ ._ ._ ICProdPlus ()


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
  -- prod cases
  to~̸ ._ ._ (ICProd1 incon) TCRefl = abort (incon-nrefl incon)
  to~̸ ._ ._ (ICProd1 incon) (TCProd x x₁) = to~̸ _ _ incon x
  to~̸ ._ ._ (ICProd2 incon) TCRefl = abort (incon-nrefl incon)
  to~̸ ._ ._ (ICProd2 incon) (TCProd x x₁) = to~̸ _ _ incon x₁
  

  -- second half of iso
  from~̸ : (t1 t2 : τ̇) → t1 ~̸ t2 → incon t1 t2
  from~̸ num (t2 ==> t3) ncon = ICNumArr
  from~̸ num (t1 ⊕ t2) x = ICNumPlus
  from~̸ num (t1 ⊠ t2) x = ICNumProd
  from~̸ (t1 ==> t2) num ncon = ICArrNum
  from~̸ (x ==> x₁) (t1 ⊕ t2) _ = ICArrPlus
  from~̸ (x ==> x₁) (t1 ⊠ t2) _ = ICArrProd
  from~̸ (t1 ==> t2) (t3 ==> t4) ncon with ~dec t1 t3
  ... | Inl qq = ICArr2 (from~̸ t2 t4 (λ x → ncon (TCArr qq x)))
  ... | Inr qq = ICArr1 (from~̸ _ _ qq)
  
  from~̸ (t1 ⊕ t2) num _ = ICPlusNum
  from~̸ (t1 ⊕ t2) (t3 ==> t4) _ = ICPlusArr
  from~̸ (t1 ⊕ t2) (t3 ⊠ t4) ncon = ICPlusProd
  from~̸ (t1 ⊕ t2) (t3 ⊕ t4) ncon with ~dec t1 t3
  ... | Inl qq = ICPlus2 (from~̸ t2 t4 (λ x → ncon (TCPlus qq x)))
  ... | Inr qq = ICPlus1 (from~̸ _ _ qq)

  from~̸ (t1 ⊠ t2) num _ = ICProdNum
  from~̸ (t1 ⊠ t2) (t3 ==> t4) _ = ICProdArr
  from~̸ (t1 ⊠ t2) (t3 ⊕ t4) ncon = ICProdPlus
  from~̸ (t1 ⊠ t2) (t3 ⊠ t4) ncon with ~dec t1 t3
  ... | Inl qq = ICProd2 (from~̸ t2 t4 (λ x → ncon (TCProd qq x)))
  ... | Inr qq = ICProd1 (from~̸ _ _ qq)
  
  -- the remaining consistent types all lead to absurdities
  from~̸ num num ncon = abort (ncon TCRefl)
  from~̸ num ⦇-⦈ ncon = abort (ncon TCHole1)
  from~̸ ⦇-⦈ num ncon = abort (ncon TCHole2)
  from~̸ ⦇-⦈ ⦇-⦈ ncon = abort (ncon TCRefl)
  from~̸ ⦇-⦈ (t2 ==> t3) ncon = abort (ncon TCHole2)
  from~̸ (t1 ==> t2) ⦇-⦈ ncon = abort (ncon TCHole1)
  from~̸ (t1 ⊕ t2) ⦇-⦈ ncon = abort (ncon TCHole1)
  from~̸ ⦇-⦈ (t1 ⊕ t2) x = abort (x TCHole2)
  from~̸ (t1 ⊠ t2) ⦇-⦈ ncon = abort (ncon TCHole1)
  from~̸ ⦇-⦈ (t1 ⊠ t2) x = abort (x TCHole2)
  
  -- need to display that at least one of the round-trips above is stable
  -- for this to be structure preserving and really an iso.
  rt1 : (t1 t2 : τ̇) → (x : t1 ~̸ t2) → (to~̸ t1 t2 (from~̸ t1 t2 x)) == x
  rt1 num (t2 ==> t3) x         = funext (λ x₁ → abort (x x₁))
  rt1 (t1 ==> t2) num x         = funext (λ x₁ → abort (x x₁))
  rt1 (t1 ==> t2) (t3 ==> t4) x = funext (λ x₁ → abort (x x₁))
  rt1 num num x                 = abort (x TCRefl)
  rt1 num ⦇-⦈ x                  = abort (x TCHole1)
  rt1 ⦇-⦈ num x                  = abort (x TCHole2)
  rt1 ⦇-⦈ ⦇-⦈ x                   = abort (x TCRefl)
  rt1 ⦇-⦈ (t2 ==> t3) x          = abort (x TCHole2)
  rt1 (t1 ==> t2) ⦇-⦈ x          = abort (x TCHole1)
  rt1 (t1 ⊕ t2) num x           = funext (λ ())
  rt1 (t1 ⊕ t2) ⦇-⦈ x            = abort (x TCHole1)
  rt1 (t1 ⊕ t2) (t3 ==> t4) x   = funext (λ ())
  rt1 num (t1 ⊕ t2) x           = funext (λ ())
  rt1 ⦇-⦈ (t1 ⊕ t2) x            = abort (x TCHole2)
  rt1 (t1 ==> t2) (t3 ⊕ t4) x   = funext (λ ())
  rt1 (t1 ⊕ t2) (t3 ⊕ t4) x     = funext (λ x₁ → abort (x x₁))
  rt1 num (z ⊠ z₁) x            = funext (λ ())
  rt1 ⦇-⦈ (z ⊠ z₁) x             = funext (λ x₁ → abort (x x₁))
  rt1 (y ==> y₁) (z ⊠ z₁) x     = funext (λ ())
  rt1 (y ⊕ y₁) (z ⊠ z₁) x       = funext (λ ())
  rt1 (y ⊠ y₁) num x            = funext (λ ())
  rt1 (y ⊠ y₁) ⦇-⦈ x             = funext (λ x₁ → abort (x x₁))
  rt1 (y ⊠ y₁) (z ==> z₁) x     = funext (λ ())
  rt1 (y ⊠ y₁) (z ⊕ z₁) x       = funext (λ ())
  rt1 (y ⊠ y₁) (z ⊠ z₁) x       = funext (λ x₁ → abort (x x₁))

  -- if inconsistency at arrows and plusses is proof-irrelevant, then all
  -- of inconsistency is proof-irrelevant
  incon-irrelev :
    (arr-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ==> t2) (t3 ==> t4)) → x == y) →
    (plus-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊕ t2) (t3 ⊕ t4)) → x == y) →
    (prod-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊠ t2) (t3 ⊠ t4)) → x == y) →
                (t1 t2 : τ̇) (x y : incon t1 t2) → x == y
  incon-irrelev _ _ _ .num _ ICNumArr ICNumArr = refl
  incon-irrelev _ _ _ _ .num ICArrNum ICArrNum = refl
  incon-irrelev ar pl pr _ _ (ICArr1 x) (ICArr1 y) = ap1 ICArr1 (incon-irrelev ar pl pr _ _ x y)
  incon-irrelev ar _ _ _ _ (ICArr1 x) (ICArr2 y) = ar (ICArr1 x) (ICArr2 y)
  incon-irrelev ar _ _ _ _ (ICArr2 x) (ICArr1 y) = ar (ICArr2 x) (ICArr1 y)
  incon-irrelev ar pl pr _ _ (ICArr2 x) (ICArr2 y) = ap1 ICArr2 (incon-irrelev ar pl pr _ _ x y )
  incon-irrelev _ _ _ .num _ ICNumPlus ICNumPlus = refl
  incon-irrelev _ _ _ _ .num ICPlusNum ICPlusNum = refl
  incon-irrelev ar pl pr _ _ (ICPlus1 x) (ICPlus1 y) = ap1 ICPlus1
                                                           (incon-irrelev ar pl pr _ _ x y)
  incon-irrelev _ pl _ _ _ (ICPlus1 x) (ICPlus2 y) = pl (ICPlus1 x) (ICPlus2 y)
  incon-irrelev _ pl _ _ _ (ICPlus2 x) (ICPlus1 y) = pl (ICPlus2 x) (ICPlus1 y)
  incon-irrelev ar pl pr _ _ (ICPlus2 x) (ICPlus2 y) = ap1 ICPlus2
                                                           (incon-irrelev ar pl pr _ _ x y)
  incon-irrelev _ _ _ _ _ ICPlusArr ICPlusArr = refl
  incon-irrelev _ _ _ _ _ ICArrPlus ICArrPlus = refl
  incon-irrelev ar pl pr _ _ (ICProd1 x) y = pr (ICProd1 x) y
  incon-irrelev ar pl pr _ _ (ICProd2 x) y = pr (ICProd2 x) y
  incon-irrelev ar pl pr .num _ ICNumProd ICNumProd = refl
  incon-irrelev ar pl pr _ _ ICArrProd ICArrProd = refl
  incon-irrelev ar pl pr _ _ ICPlusProd ICPlusProd = refl
  incon-irrelev ar pl pr _ .num ICProdNum ICProdNum = refl
  incon-irrelev ar pl pr _ _ ICProdArr ICProdArr = refl
  incon-irrelev ar pl pr _ _ ICProdPlus ICProdPlus = refl
  
  -- if inconsistency at arrows and plusses is proof-irrelevant, then the
  -- round trip is stable up to equality
  rt2 : (arr-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ==> t2) (t3 ==> t4)) → x == y) →
        (plus-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊕ t2) (t3 ⊕ t4)) → x == y) →
        (prod-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊠ t2) (t3 ⊠ t4)) → x == y) →
        (t1 t2 : τ̇) → (x : incon t1 t2) → (from~̸ t1 t2 (to~̸ t1 t2 x)) == x
  rt2 _ _ _ .num _ ICNumArr = refl
  rt2 _ _ _ _ .num ICArrNum = refl
  rt2 ar pl pr (t1 ==> t2) (t3 ==> t4) (ICArr1 ic) with ~dec t1 t3
  ... | Inl x = abort (to~̸ t1 t3 ic x)
  ... | Inr x = ap1 ICArr1
                    (incon-irrelev ar pl pr t1 t3 (from~̸ t1 t3 x) ic)
  rt2 ar pl pr (t1 ==> t2) (t3 ==> t4) (ICArr2 ic) with ~dec t1 t3
  ... | Inl x = ap1 ICArr2
                    (incon-irrelev ar pl pr t2 t4 (from~̸ t2 t4 (to~̸ t2 t4 ic)) ic)
  ... | Inr x = ar (ICArr1 (from~̸ t1 t3 x)) (ICArr2 ic)
  rt2 _ _ _ .num _ ICNumPlus = refl
  rt2 _ _ _ _ .num ICPlusNum = refl
  rt2 ar pl pr (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus1 ic) with ~dec t1 t3
  ... | Inl x = abort (to~̸ _ _ ic x)
  ... | Inr x = ap1 ICPlus1 (incon-irrelev ar pl pr t1 t3 _ _ )
  rt2 ar pl pr (t1 ⊕ t2) (t3 ⊕ t4) (ICPlus2 ic) with ~dec t1 t3
  ... | Inl x = ap1 ICPlus2 (incon-irrelev ar pl pr t2 t4 _ _ )
  ... | Inr x = pl (ICPlus1 (from~̸ t1 t3 x)) (ICPlus2 ic)
  rt2 _ _ _ _ _ ICPlusArr = refl
  rt2 _ _ _ _ _ ICArrPlus = refl
  rt2 _ _ _ num (t1 ⊠ t2) ICNumProd = refl
  rt2 _ _ _ (t1 ==> t2) (t3 ⊠ t4) ICArrProd = refl
  rt2 _ _ _ (t1 ⊕ t2) (t3 ⊠ t4) ICPlusProd = refl
  rt2 _ _ _ (t1 ⊠ t2) num ICProdNum = refl
  rt2 _ _ _ (t1 ⊠ t2) (t3 ==> t4) ICProdArr = refl
  rt2 _ _ _ (t1 ⊠ t2) (t3 ⊕ t4) ICProdPlus = refl
  rt2 ar pl pr (t1 ⊠ t2) (t3 ⊠ t4) (ICProd1 ic) with ~dec t1 t3
  ... | Inl x = abort (to~̸ _ _ ic x)
  ... | Inr x = pr (ICProd1 (from~̸ t1 t3 x)) (ICProd1 ic)
  rt2 ar pl pr (t1 ⊠ t2) (t3 ⊠ t4) (ICProd2 ic) with ~dec t1 t3
  ... | Inl x = pr (ICProd2 (from~̸ t2 t4 (to~̸ t2 t4 ic))) (ICProd2 ic)
  ... | Inr x = pr (ICProd1 (from~̸ t1 t3 x)) (ICProd2 ic)
  
  -- if inconsistency at arrows and plusses is proof-irrelevant, then the
  -- two defintions of inconsistency are isomorphic
  incon-iso :
    (arr-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ==> t2) (t3 ==> t4)) → x == y) →
    (plus-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊕ t2) (t3 ⊕ t4)) → x == y) →
    (prod-incon-irrelev : {t1 t2 t3 t4 : τ̇} (x y : incon (t1 ⊠ t2) (t3 ⊠ t4)) → x == y) →
    (t1 t2 : τ̇) → (incon t1 t2) ≃ (t1 ~̸ t2)
  incon-iso ar pl pr t1 t2 = (to~̸ t1 t2) , (from~̸ t1 t2) , (rt2 ar pl pr t1 t2) , (rt1 t1 t2)

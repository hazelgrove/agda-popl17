open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module future-work where
  -- there is no list of actions that can be preformed in sequence that
  -- renders a complete term from (3 : <||>) 4.
  ex5 : ∀{Γ e' t'} →
          Σ[ L ∈ List action ]
             ((runsynth Γ (((N 3) ·:₂ ▹ <||> ◃) ∘₁ (N 4)) <||> L e' t')
               × ecomplete (e' ◆e))
          → ⊥
  ex5 (.[] , DoRefl , com) = π2 (π1 com)
  ex5 (._ , DoSynth (SAMove ()) rs , com)
  ex5 (._ , DoSynth (SAZipApArr x x₁ x₂ x₃ (ASubsume SNum x₅)) DoRefl , com) = {!!}
  ex5 (._ , DoSynth (SAZipApArr x x₁ x₂ x₃ (ASubsume SNum x₅)) (DoSynth x₄ DoRefl) , com) = {!!}
  ex5 (._ , DoSynth (SAZipApArr x x₁ x₂ x₃ (ASubsume SNum x₅)) (DoSynth x₄ (DoSynth x₆ rs)) , com) = {!rs!}

  cy : ∅ ⊢ ((·λ 0 <||>) ·: ((num ==> num) ==> num)) =>  ((num ==> num) ==> num)
  cy = SAsc (ALam refl MAArr (ASubsume SEHole TCHole1))

  -- TODO: the shower thoughts theorem

  lem-comp~det : ∀{ t t1 t2 } → tcomplete t → t ~ t1 → t ~ t2 → t1 ~ t2
  lem-comp~det tc TCRefl TCRefl = TCRefl
  lem-comp~det tc TCRefl TCHole1 = TCHole1
  lem-comp~det tc TCRefl TCHole2 = abort tc
  lem-comp~det tc TCRefl (TCArr c2 c3) = TCArr c2 c3
  lem-comp~det tc TCHole1 TCRefl = TCHole2
  lem-comp~det tc TCHole1 TCHole1 = TCRefl
  lem-comp~det tc TCHole1 TCHole2 = abort tc
  lem-comp~det tc TCHole1 (TCArr c2 c3) = TCHole2
  lem-comp~det tc TCHole2 TCRefl = abort tc
  lem-comp~det tc TCHole2 TCHole1 = abort tc
  lem-comp~det tc TCHole2 TCHole2 = abort tc
  lem-comp~det (π1 , π2) (TCArr c1 c2) TCRefl = TCArr (lem-comp~det π1 c1 TCRefl) (lem-comp~det π2 c2 TCRefl)
  lem-comp~det (π1 , π2) (TCArr c1 c2) TCHole1 = TCHole1
  lem-comp~det (π1 , π2) (TCArr c1 c2) (TCArr c3 c4) = TCArr (lem-comp~det π1 c1 c3) (lem-comp~det π2 c2 c4)
  lem-comp~det {._} {._} {._} _ (TCPlus {_} {_} {_} {_} _ _)
               (TCRefl {._}) = {!!}
  lem-comp~det {._} {._} {._} _ (TCPlus {_} {_} {_} {_} _ _)
               (TCHole1 {._}) = {!!}
  lem-comp~det {._} {_} {._} _ _ (TCPlus {_} {_} {_} {_} _ _) = {!!}


  lem-comp-match : ∀{t t1 t2 t'} → tcomplete t →
                                   t ▸arr (t1 ==> t2) →
                                   t ~ t' →
                                   Σ[ t2' ∈ τ̇ ] t' ▸arr (t1 ==> t2') × t2 ~ t2'
  lem-comp-match tc MAHole c = abort tc
  lem-comp-match (π1 , π2) MAArr TCRefl = _ , MAArr , TCRefl
  lem-comp-match (π1 , π2) MAArr TCHole1 = _ , {!!} , TCHole1
  lem-comp-match (π1 , π2) MAArr (TCArr c c₁) = _ , {!!} , c₁

  weaken-hole : ∀{ Γ x t1 e} →
                tcomplete t1 →
                (Γ ,, (x , t1)) ⊢ e <= <||> →
                (Γ ,, (x , <||>)) ⊢ e <= <||>
  weaken-hole tc (ASubsume x₁ x₂) = ASubsume {!!} x₂
  weaken-hole tc (ALam x₂ x₃ wt)  = ALam {!!} x₃ {!!}
  weaken-hole {_} {_} {_} {._} _ (AInl {._} {_} {._} {_} {_} _ _) = {!!}
  weaken-hole {_} {_} {_} {._} _ (AInr {._} {_} {._} {_} {_} _ _) = {!!}
  weaken-hole {_} {_} {_} {._} _
              (ACase {._} {_} {_} {_} {._} {_} {_} {_} {_} {_} _ _ _ _ _ _) = {!!}


  all-hole : ∀{Γ e t} → tcomplete t → Γ ⊢ e <= t → Γ ⊢ e <= <||>
  all-hole tc (ASubsume x _) = ASubsume x TCHole2
  all-hole tc (ALam _ MAHole _) = abort tc
  all-hole (π1 , π2) (ALam {Γ = G} {x = x} x₁ MAArr wt) = ALam x₁ MAHole (weaken-hole {Γ = G} {x = x} π1 (all-hole π2 wt) )
  all-hole {_} {._} {_} _ (AInl {._} {_} {._} {_} {_} _ _) = {!!}
  all-hole {_} {._} {_} _ (AInr {._} {_} {._} {_} {_} _ _) = {!!}
  all-hole {_} {._} {._} _
           (ACase {._} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _ _ _ _ _) = {!!}


  -- analysis and type consistency work together in the expected way
  anaconsis : ∀{Γ e t t'} → tcomplete t → Γ ⊢ e <= t → t ~ t' → Γ ⊢ e <= t'
  anaconsis tc (ASubsume x x₁) c = ASubsume x (lem-comp~det tc c x₁)
  anaconsis tc (ALam x₁ MAHole wt) c = abort tc
  anaconsis (π1 , π2) (ALam x₁ MAArr wt) TCRefl = ALam x₁ MAArr wt
  anaconsis (π1 , π2) (ALam x₁ MAArr wt) TCHole1 with anaconsis π2 wt TCHole1
  ... | ih = all-hole (π1 , π2) (ALam x₁ MAArr wt)
  anaconsis (π1 , π2) (ALam x₁ MAArr wt) (TCArr c1 c2) = ALam x₁ MAArr {!!}
  -- c with lem-comp-match (π1 , π2) MAArr c
  -- ... | (t2' , m' , c') = ALam x₁ m' (anaconsis π2 wt c')
  anaconsis {_} {._} {_} {_} _ (AInl {._} {_} {._} {_} {_} _ _) _ = {!!}
  anaconsis {_} {._} {_} {_} _ (AInr {._} {_} {._} {_} {_} _ _) _ = {!!}
  anaconsis {_} {._} {._} {_} _
            (ACase {._} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _ _ _ _ _) _ = {!!}



  -- horsing around with weakening the statement of determinism for the two
  -- cases that we can't prove in the analysis case.
  data near : ê → ê → Set where
    AscNear : ∀{e t1 t2} →
                      (t1 ~ t2) →
                      near (e ·:₂ ▹ t1 ◃) (e ·:₂ ▹ t2 ◃)
    -- LamNear :
    EqNear : ∀{ e1 e2 } → e1 == e2 → near e1 e2


  postulate
    actdet2 : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t t' t'' : τ̇} {α : action} →
              (E : erase-e e e◆) →
              (Γ ⊢ e◆ => t) →
              (Γ ⊢ e => t ~ α ~> e'  => t') →
              (Γ ⊢ e => t ~ α ~> e'' => t'') →
              (e' == e'' × t' == t'') -- this may not be provable; not sure
                                      -- about the recursive calls.
    movedet : {e e' e'' : ê} {δ : direction} →
              (e + move δ +>e e') →
              (e + move δ +>e e'') →
              e' == e''
    lem-nomove-para : ∀{Γ e t e'} → Γ ⊢ ▹ e ◃ ~ move parent ~> e' ⇐ t → ⊥
    synthmovedet : {Γ : ·ctx} {e e' e'' : ê} {t' t'' : τ̇} {δ : direction} →
         (Γ ⊢ e => t' ~ move δ ~> e'' => t'') →
         (e + move δ +>e e') →
         e'' == e'

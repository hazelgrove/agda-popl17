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

  all-hole : ∀{Γ e t} → tcomplete t → Γ ⊢ e <= t → Γ ⊢ e <= <||>
  all-hole tc (ASubsume x _) = ASubsume x TCHole2
  all-hole tc (ALam _ MAHole _) = abort tc
  all-hole (π1 , π2) (ALam {Γ = G} {x = x} x₁ MAArr wt) = ALam x₁ MAHole (weaken-hole {Γ = G} {x = x} π1 (all-hole π2 wt) )

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



  -- an action on an expression in an analytic position produces one
  -- resultant expression and type.
  actdet3 : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t : τ̇} {α : action} →
            (erase-e e e◆) →
            (Γ ⊢ e◆ <= t) →
            (Γ ⊢ e ~ α ~> e' ⇐ t) →
            (Γ ⊢ e ~ α ~> e'' ⇐ t) →
            near e' e''
  ---- lambda cases first
  -- an erased lambda can't be typechecked with subsume
  actdet3 (EELam _) (ASubsume () _) _ _

  -- lambdas never match with subsumption actions, because it won't be well typed.
  actdet3 EETop      (ALam x₁ x₂ wt) (AASubsume EETop () x₅ x₆) _
  actdet3 (EELam _) (ALam x₁ x₂ wt) (AASubsume (EELam x₃) () x₅ x₆) _
  actdet3 EETop      (ALam x₁ x₂ wt) _ (AASubsume EETop () x₅ x₆)
  actdet3 (EELam _) (ALam x₁ x₂ wt) _ (AASubsume (EELam x₃) () x₅ x₆)

  -- movements are the same reguardless of erasure
  actdet3 _ (ALam x₁ x₂ wt) (AAMove x₃) (AAMove x₄) = EqNear (movedet x₃ x₄)

  -- with the cursor at the top, there are only two possible actions
  actdet3 EETop (ALam x₁ x₂ wt) AADel AADel = EqNear refl
  actdet3 EETop (ALam x₁ x₂ wt) AAConAsc AAConAsc = EqNear refl

  -- otherwise, it has to be a zip. movement doesnt' cohere..
  actdet3 (EELam er) (ALam x₁ x₂ wt) (AAMove EMLamParent) (AAZipLam x₄ x₅ d2) = abort (lem-nomove-para d2)
  actdet3 (EELam er) (ALam x₁ x₂ wt) (AAZipLam x₃ x₄ d1) (AAMove EMLamParent) = abort (lem-nomove-para d1)

  -- and for the remaining case, recurr on the smaller derivations
  actdet3 (EELam er) (ALam x₁ x₂ wt) (AAZipLam x₃ x₄ d1) (AAZipLam x₅ x₆ d2)
     with matchunicity x₄ x₆
  ... | refl with matchunicity x₄ x₂
  ... | refl with actdet3 er wt d1 d2
  ... | AscNear q = {!!}
  ... | EqNear refl = EqNear refl

  ---- now the subsumption cases
    -- subsume / subsume, so pin things down then recurr
  actdet3 er (ASubsume a b) (AASubsume x x₁ x₂ x₃) (AASubsume x₄ x₅ x₆ x₇)
    with erasee-det x₄ x
  ... | refl with erasee-det er x₄
  ... | refl with synthunicity x₅ x₁
  ... | refl = EqNear (π1 (actdet2 x x₅ x₂ x₆))

  -- (these are all repeated below, irritatingly.)
  actdet3 er (ASubsume a b) (AASubsume x x₁ x₃ x₂) (AAMove x₄) = EqNear (synthmovedet x₃ x₄)
  actdet3 EETop (ASubsume a b) (AASubsume EETop x SADel x₁) AADel = EqNear refl
  actdet3 EETop (ASubsume a b) (AASubsume EETop x SAConAsc x₁) AAConAsc
    with synthunicity a x
  ... | refl = AscNear (~sym x₁)
  actdet3 EETop (ASubsume SEHole b) (AASubsume EETop SEHole (SAConVar {Γ = Γ} p) x₂) (AAConVar x₅ p₁)
    with ctxunicity {Γ = Γ} p p₁
  ... | refl = abort (x₅ x₂)
  actdet3 EETop (ASubsume SEHole b) (AASubsume EETop SEHole (SAConLam x₄) x₂) (AAConLam1 x₅ m) = {!!} -- unprovable
  actdet3 EETop (ASubsume a b) (AASubsume EETop x₁ (SAConLam x₃) x₂) (AAConLam2 x₅ x₆) = abort (x₆ x₂)
  actdet3 EETop (ASubsume a b) (AASubsume EETop x₁ SAConNumlit x₂) (AAConNumlit x₄) = abort (x₄ x₂)
  actdet3 EETop (ASubsume a b) (AASubsume EETop x (SAFinish x₂) x₁) (AAFinish x₄) = EqNear refl

    -- subsume / move
  actdet3 er (ASubsume a b) (AAMove x) (AASubsume x₁ x₂ x₃ x₄) = EqNear ( ! (synthmovedet x₃ x))
  actdet3 er (ASubsume a b) (AAMove x) (AAMove x₁) = EqNear (movedet x x₁)

    -- subsume / del
  actdet3 er (ASubsume a b) AADel (AASubsume x x₁ SADel x₃) = EqNear refl
  actdet3 er (ASubsume a b) AADel AADel = EqNear refl

    -- subsume / conasc
  actdet3 EETop (ASubsume a b) AAConAsc (AASubsume EETop x₁ SAConAsc x₃)
    with synthunicity a x₁
  ... | refl = AscNear x₃
  actdet3 er (ASubsume a b) AAConAsc AAConAsc = EqNear refl

    -- subsume / convar
  actdet3 EETop (ASubsume SEHole b) (AAConVar x₁ p) (AASubsume EETop SEHole (SAConVar {Γ = Γ} p₁) x₅)
    with ctxunicity {Γ = Γ} p p₁
  ... | refl = abort (x₁ x₅)
  actdet3 er (ASubsume a b) (AAConVar x₁ p) (AAConVar x₂ p₁) = EqNear refl

    -- subsume / conlam1
  actdet3 EETop (ASubsume SEHole b) (AAConLam1 x₁ x₂) (AASubsume EETop SEHole (SAConLam x₃) x₆) = {!!} -- unprovable
  actdet3 er (ASubsume a b) (AAConLam1 x₁ MAHole) (AAConLam2 x₃ x₄) = abort (x₄ TCHole2)
  actdet3 er (ASubsume a b) (AAConLam1 x₁ MAArr) (AAConLam2 x₃ x₄) = abort (x₄ (TCArr TCHole1 TCHole1))
  actdet3 er (ASubsume a b) (AAConLam1 x₁ x₂) (AAConLam1 x₃ x₄) = EqNear refl

    -- subsume / conlam2
  actdet3 EETop (ASubsume SEHole TCRefl) (AAConLam2 x₁ x₂) (AASubsume EETop SEHole x₅ x₆) = abort (x₂ TCHole2)
  actdet3 EETop (ASubsume SEHole TCHole1) (AAConLam2 x₁ x₂) (AASubsume EETop SEHole (SAConLam x₃) x₆) = abort (x₂ x₆)
  actdet3 EETop (ASubsume SEHole TCHole2) (AAConLam2 x₁ x₂) (AASubsume EETop SEHole x₅ x₆) = abort (x₂ TCHole2)
  actdet3 EETop (ASubsume a b) (AAConLam2 x₂ x₁) (AAConLam1 x₃ MAHole) = abort (x₁ TCHole2)
  actdet3 EETop (ASubsume a b) (AAConLam2 x₂ x₁) (AAConLam1 x₃ MAArr) = abort (x₁ (TCArr TCHole1 TCHole1))
  actdet3 er (ASubsume a b) (AAConLam2 x₂ x) (AAConLam2 x₃ x₄) = EqNear refl

    -- subsume / numlit
  actdet3 er (ASubsume a b) (AAConNumlit x) (AASubsume x₁ x₂ SAConNumlit x₄) = abort (x x₄)
  actdet3 er (ASubsume a b) (AAConNumlit x) (AAConNumlit x₁) = EqNear refl

    -- subsume / finish
  actdet3 er (ASubsume a b) (AAFinish x) (AASubsume x₁ x₂ (SAFinish x₃) x₄) = EqNear refl
  actdet3 er (ASubsume a b) (AAFinish x) (AAFinish x₁) = EqNear refl

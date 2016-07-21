open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module future-work where
  -- there is no list of actions that can be preformed in sequence that
  -- renders a complete term from (3 : <||>) 4. this is part of the argu
  ex5 : ∀{Γ e' t'} →
          Σ[ L ∈ List action ]
             ((runsynth Γ (((N 3) ·:₂ ▹ <||> ◃) ∘₁ (N 4)) <||> L e' t')
               × ecomplete (e' ◆e))
          → ⊥
  ex5 = {!!}

  cy : ∅ ⊢ ((·λ 0 <||>) ·: ((num ==> num) ==> num)) =>  ((num ==> num) ==> num)
  cy = SAsc (ALam refl MAArr (ASubsume SEHole TCHole1))


  -- TODO: the shower thoughts theorem

    -- not a theorem; same problem as the corresponding hole below
  semitrans : ∀{t t' t''} → t ~ t'' → t ~ t' → t'' ~ t'
  semitrans TCRefl TCRefl = TCRefl
  semitrans TCRefl TCHole1 = TCHole1
  semitrans TCRefl TCHole2 = TCHole2
  semitrans TCRefl (TCArr c c₁) = TCArr c c₁
  semitrans TCHole1 TCRefl = TCHole2
  semitrans TCHole1 TCHole1 = TCRefl
  semitrans TCHole1 TCHole2 = TCHole2
  semitrans TCHole1 (TCArr c c₁) = TCHole2
  semitrans TCHole2 TCRefl = TCHole1
  semitrans TCHole2 TCHole1 = TCHole1
  semitrans TCHole2 TCHole2 = {!!} -- unfillable; not enough info from TCHole2
  semitrans (TCArr a a₁) TCRefl = TCArr (semitrans a TCRefl) (semitrans a₁ TCRefl)
  semitrans (TCArr a a₁) TCHole1 = TCHole1
  semitrans (TCArr a a₁) (TCArr c c₁) = TCArr (semitrans a c) (semitrans a₁ c₁)

  -- analysis and type consistency work together in the expected way
  anaconsis : ∀{Γ e t t'} → Γ ⊢ e <= t → t ~ t' → Γ ⊢ e <= t'
  anaconsis (ASubsume x x₁) TCRefl = ASubsume x x₁
  anaconsis (ASubsume x x₁) TCHole1 = ASubsume x TCHole2
  anaconsis (ASubsume x TCRefl) TCHole2 = ASubsume x TCHole1
  anaconsis (ASubsume x TCHole1) TCHole2 = ASubsume x TCHole1
  anaconsis (ASubsume x TCHole2) TCHole2 = {!!}
  anaconsis (ASubsume x TCRefl) (TCArr con con₁) = ASubsume x (TCArr (~sym con) (~sym con₁))
  anaconsis (ASubsume x TCHole1) (TCArr con con₁) = ASubsume x TCHole1
  anaconsis (ASubsume x (TCArr x₁ x₂)) (TCArr con con₁) = ASubsume x (TCArr (semitrans con x₁) (semitrans con₁ x₂))

  anaconsis (ALam x₁ MAHole wt) TCRefl = ALam x₁ MAHole wt
  anaconsis (ALam x₁ MAHole wt) TCHole1 = ALam x₁ MAHole wt
  anaconsis (ALam x₁ MAHole wt) TCHole2 with anaconsis wt TCRefl -- you can put any of TC construtors here and this t/cs
  ... | ih = ALam x₁ {!!} ih
  anaconsis (ALam x₁ MAArr wt) TCRefl = ALam x₁ MAArr wt
  anaconsis (ALam x₁ MAArr wt) TCHole1 = ALam x₁ {!!} (anaconsis wt TCRefl) -- hole doesn't match anything
  anaconsis (ALam x₁ MAArr wt) (TCArr con con₁) with anaconsis wt con₁
  ... | ih = ALam x₁ MAArr {!!} -- the type in the context doesn't change, only in the analysis position. lemma?




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


  movements-synth : ∀{e e' t t' Γ} →
    (L : List action) (p : movements L) →
                    runsynth Γ e t L e' t' → t == t'
  movements-synth .[] AM[] DoRefl = refl
  movements-synth ._ (AM:: p) (DoSynth x x₁) with movements-synth _ p x₁ | x
  ... | refl | SAMove x₂ = refl
  ... | refl | SAZipAsc1 x₂ = refl
  ... | refl | SAZipAsc2 x₂ x₃ x₄ x₅ = eraset-det (lem-erase-step x₄ x₂) x₃
  ... | refl | SAZipApArr x₂ x₃ x₄ qq x₅ = {!!}
  ... | refl | SAZipApAna x₂ x₃ x₄ = refl
  ... | refl | SAZipPlus1 x₂ = refl
  ... | refl | SAZipPlus2 x₂ = refl
  ... | refl | SAZipHole x₂ x₃ qq = refl

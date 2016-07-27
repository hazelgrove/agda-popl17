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


  mutual
    aasubmin-ana : ∀{Γ e α e' t} → (Γ ⊢ e ~ α ~> e' ⇐ t) → Set
    aasubmin-ana (AASubsume x x₁ SAConAsc x₃) = ⊥
    aasubmin-ana (AASubsume x x₁ (SAConLam x₃) x₄) = ⊥
    aasubmin-ana (AASubsume x x₁ s x₃) = aasubmin-synth s
    aasubmin-ana (AAZipLam x₁ x₂ d) = aasubmin-ana d
    aasubmin-ana _ = ⊤

    aasubmin-synth : ∀{Γ e t α e' t'} → (Γ ⊢ e => t ~ α ~> e' => t') → Set
    aasubmin-synth (SAZipAsc1 x) = aasubmin-ana x
    aasubmin-synth (SAZipApArr x x₁ x₂ d x₃) = aasubmin-synth d
    aasubmin-synth (SAZipApAna x x₁ x₂) = aasubmin-ana x₂
    aasubmin-synth (SAZipPlus1 x) = aasubmin-ana x
    aasubmin-synth (SAZipPlus2 x) = aasubmin-ana x
    aasubmin-synth (SAZipHole x x₁ d) = aasubmin-synth d
    aasubmin-synth _ = ⊤

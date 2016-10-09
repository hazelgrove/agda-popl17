open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module future-work where
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
                                   Σ[ t2' ∈ τ̇ ] (t' ▸arr (t1 ==> t2') × t2 ~ t2')
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
  anaconsis tc (ASubsume x x₁) TCRefl = ASubsume x x₁
  anaconsis tc (ASubsume x x₁) TCHole1 = ASubsume x TCHole2
  anaconsis tc (ASubsume x x₁) TCHole2 = {!!}
  anaconsis (tc , tc2) (ASubsume x x₁) (TCArr con con₁) = {!!}
  anaconsis tc (ALam x₁ x₂ wt) TCRefl = ALam x₁ x₂ wt
  anaconsis tc (ALam x₁ x₂ wt) TCHole1 = ALam x₁ MAHole {!anaconsis ? wt!}
  anaconsis tc (ALam x₁ x₂ wt) TCHole2 = {!!}
  anaconsis tc (ALam x₁ x₂ wt) (TCArr con con₁) = {!!}

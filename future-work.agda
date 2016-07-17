open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks

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



  pseudodet : {Γ : ·ctx} {e e' e'' : ê} {e◆ : ė} {t t' : τ̇} {α : action} →
              (erase-e e e◆) →
              (Γ ⊢ e◆ <= t) →
              (Γ ⊢ e ~ α ~> e' ⇐ t) →
              (Γ ⊢ e ~ α ~> e'' ⇐ t') →
              (e' == e'' × t ~ t')
  pseudodet = {!!}

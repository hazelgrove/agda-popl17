open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module aasubsume-min where
  mutual
    aasubmin-synth : ∀{Γ e t α e' t'} → (Γ ⊢ e => t ~ α ~> e' => t') → Set
    aasubmin-synth (SAZipAsc1 x) = aasubmin-ana x
    aasubmin-synth (SAZipApArr x x₁ x₂ d x₃) = aasubmin-synth d
    aasubmin-synth (SAZipApAna x x₁ x₂) = aasubmin-ana x₂
    aasubmin-synth (SAZipPlus1 x) = aasubmin-ana x
    aasubmin-synth (SAZipPlus2 x) = aasubmin-ana x
    aasubmin-synth (SAZipHole x x₁ d) = aasubmin-synth d
    aasubmin-synth _ = ⊤

    aasubmin-ana : ∀{Γ e α e' t} → (Γ ⊢ e ~ α ~> e' ⇐ t) → Set
    aasubmin-ana (AASubsume x x₁ SAConAsc x₃) = ⊥
    aasubmin-ana (AASubsume x x₁ (SAConLam x₃) x₄) = ⊥
    aasubmin-ana (AASubsume x x₁ s x₃) = aasubmin-synth s
    aasubmin-ana (AAZipLam x₁ x₂ d) = aasubmin-ana d
    aasubmin-ana _ = ⊤


  mutual
    min-synth : ∀{Γ e t α e' t'} → (d : Γ ⊢ e => t ~ α ~> e' => t') →
                        Σ[ e'' ∈ ê ] Σ[ d' ∈ Γ ⊢ e => t ~ α ~> e'' => t' ] aasubmin-synth d'
    min-synth (SAMove x) = _ , SAMove x , <>
    min-synth SADel = _ , SADel , <>
    min-synth SAConAsc = _ , SAConAsc , <>
    min-synth (SAConVar p) = _ , SAConVar p , <>
    min-synth (SAConLam x₁) = _ , SAConLam x₁ , <>
    min-synth (SAConApArr x) = _ , SAConApArr x , <>
    min-synth (SAConApOtw x) = _ , SAConApOtw x , <>
    min-synth SAConNumlit = _ , SAConNumlit , <>
    min-synth (SAConPlus1 x) = _ , SAConPlus1 x , <>
    min-synth (SAConPlus2 x) = _ , SAConPlus2 x , <>
    min-synth SAConNEHole = _ , SAConNEHole , <>
    min-synth (SAFinish x) = _ , SAFinish x , <>
    min-synth (SAZipAsc2 x x₁ x₂ x₃) = _ , SAZipAsc2 x x₁ x₂ x₃ , <>
    min-synth (SAZipAsc1 x) with min-ana x
    ... | _ , a , b = _ ,  SAZipAsc1 a , b
    min-synth (SAZipApArr x x₁ x₂ d x₃) with min-synth d
    ... | _ , a , b = _ , (SAZipApArr x x₁ x₂ a x₃) , b
    min-synth (SAZipApAna x x₁ x₂) with min-ana x₂
    ... | _ , a , b = _ , SAZipApAna x x₁ a , b
    min-synth (SAZipPlus1 x) with min-ana x
    ... | _ , a , b = _ , SAZipPlus1 a , b
    min-synth (SAZipPlus2 x) with min-ana x
    ... | _ , a , b = _ , SAZipPlus2 a , b
    min-synth (SAZipHole x x₁ d) with min-synth d
    ... | _ , a , b = _ , SAZipHole x x₁ a , b

    min-ana : ∀{Γ e α e' t} → (d : Γ ⊢ e ~ α ~> e' ⇐ t) → Σ[ e'' ∈ ê ] Σ[ d' ∈  Γ ⊢ e ~ α ~> e'' ⇐ t ] aasubmin-ana d'
    min-ana (AASubsume {Γ = Γ} x x₁ (SAMove x₂) x₃) = _ , AAMove x₂ , <>
    min-ana (AASubsume x x₁ SADel x₃) = _ , AADel , <>
    min-ana (AASubsume {Γ = Γ}  {t = t} {t' = t'}  x x₁ SAConAsc x₃) = _ , AAConAsc {Γ = Γ} {t = t} , <>
    min-ana (AASubsume x x₁ (SAConVar p) x₃) = _ , AASubsume x x₁ (SAConVar p) x₃ , <>
    min-ana (AASubsume EETop SEHole (SAConLam x₃) TCRefl)        = _ , AAConLam1 x₃ MAArr , <>
    min-ana (AASubsume EETop SEHole (SAConLam x₃) TCHole2)       = _ , AAConLam1 x₃ MAHole , <>
    min-ana (AASubsume EETop SEHole (SAConLam x₃) (TCArr x₄ x₅)) = _ , AAConLam1 x₃ MAArr , <>
    min-ana (AASubsume x x₁ (SAConApArr x₂) x₃) = _ , AASubsume x x₁ (SAConApArr x₂) x₃ , <>
    min-ana (AASubsume x x₁ (SAConApOtw x₂) x₃) = _ , AASubsume x x₁ (SAConApOtw x₂) x₃ , <>
    min-ana (AASubsume x x₁ SAConNumlit x₃) = _ , AASubsume x x₁ SAConNumlit x₃ , <>
    min-ana (AASubsume x x₁ (SAConPlus1 x₂) x₃) = _ , AASubsume x x₁ (SAConPlus1 x₂) x₃ , <>
    min-ana (AASubsume x x₁ (SAConPlus2 x₂) x₃) = _ , AASubsume x x₁ (SAConPlus2 x₂) x₃ , <>
    min-ana (AASubsume x x₁ SAConNEHole x₃) = _ , AASubsume x x₁ SAConNEHole x₃ , <>
    min-ana (AASubsume x x₁ (SAFinish x₂) x₃) = _ ,  AASubsume x x₁ (SAFinish x₂) x₃ , <>
    min-ana (AASubsume x x₁ (SAZipAsc2 x₂ x₃ x₄ x₅) x₆) = _ , AASubsume x x₁ (SAZipAsc2 x₂ x₃ x₄ x₅) x₆ , <>
    min-ana (AASubsume x x₁ (SAZipAsc1 x₂) x₃) with min-ana x₂
    ... | a , b , c = _ , AASubsume x x₁ (SAZipAsc1 b) x₃ , c
    min-ana (AASubsume x x₁ (SAZipApArr x₂ x₃ x₄ x₅ x₆) x₇) with min-synth x₅
    ... | a , b , c = _ , AASubsume x x₁ (SAZipApArr x₂ x₃ x₄ b x₆) x₇ , c
    min-ana (AASubsume x x₁ (SAZipApAna x₂ x₃ x₄) x₅) with min-ana x₄
    ... | a , b , c = _ , AASubsume x x₁ (SAZipApAna x₂ x₃ b) x₅ , c
    min-ana (AASubsume x x₁ (SAZipPlus1 x₂) x₃) with min-ana x₂
    ... | a , b , c = _ , AASubsume x x₁ (SAZipPlus1 b) x₃ , c
    min-ana (AASubsume x x₁ (SAZipPlus2 x₂) x₃) with min-ana x₂
    ... | a , b , c = _ , AASubsume x x₁ (SAZipPlus2 b) x₃ , c
    min-ana (AASubsume x x₁ (SAZipHole x₂ x₃ x₄) x₅) with min-synth x₄
    ... | a , b , c = _ , AASubsume x x₁ (SAZipHole x₂ x₃ b) x₅ , c
    min-ana (AAMove x) = _ , AAMove x , <>
    min-ana AADel = _ , AADel , <>
    min-ana AAConAsc = _ , AAConAsc , <>
    min-ana (AAConVar x₁ p) = _ , AAConVar x₁ p , <>
    min-ana (AAConLam1 x₁ x₂) = _ , AAConLam1 x₁ x₂ , <>
    min-ana (AAConLam2 x₁ x₂) = _ , AAConLam2 x₁ x₂ , <>
    min-ana (AAConNumlit x) = _ , AAConNumlit x , <>
    min-ana (AAFinish x) = _ , AAFinish x , <>
    min-ana (AAZipLam x₁ x₂ d) with min-ana d
    ... | a , b , c = _ , AAZipLam x₁ x₂ b , c

  -- the minimization predicate propagates through subsumption rules as
  -- you'd expect
  min-ana-lem : ∀{e e' e◆ Γ t t' t'' α}
                 {a : erase-e e e◆}
                 {b : Γ ⊢ e◆ => t'}
                 {c : t ~ t''} →
                 (d : Γ ⊢ e => t' ~ α ~> e' => t'')
                → aasubmin-ana (AASubsume a b d c) → aasubmin-synth d
  min-ana-lem (SAMove x) min = <>
  min-ana-lem (SADel) min = <>
  min-ana-lem (SAConAsc) min = <>
  min-ana-lem (SAConVar p) min = <>
  min-ana-lem (SAConLam x₁) min = <>
  min-ana-lem (SAConApArr x) min = <>
  min-ana-lem (SAConApOtw x) min = <>
  min-ana-lem (SAConNumlit) min = <>
  min-ana-lem (SAConPlus1 x) min = <>
  min-ana-lem (SAConPlus2 x) min = <>
  min-ana-lem (SAConNEHole) min = <>
  min-ana-lem (SAFinish x) min = <>
  min-ana-lem (SAZipAsc1 x) min = min
  min-ana-lem (SAZipAsc2 x x₁ x₂ x₃) min = <>
  min-ana-lem (SAZipApArr x x₁ x₂ c x₃) min = min
  min-ana-lem (SAZipApAna x x₁ x₂) min = min
  min-ana-lem (SAZipPlus1 x) min = min
  min-ana-lem (SAZipPlus2 x) min = min
  min-ana-lem (SAZipHole x x₁ c) min = min

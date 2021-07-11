open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module aasubsume-min where
  -- this predicate on derivations of actions bans the cases that induce
  -- non-determinism.
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
    aasubmin-ana (AASubsume x x₁ SAConInl x₃) = ⊥
    aasubmin-ana (AASubsume x x₁ SAConInr x₃) = ⊥
    aasubmin-ana (AASubsume x x₁ (SAConLam x₃) x₄) = ⊥
    aasubmin-ana (AASubsume EETop SEHole (SAConCase1 a b c) x₄) = ⊥
    aasubmin-ana (AASubsume x x₁ SAConProd x₃) = ⊥
    aasubmin-ana (AASubsume x x₁ s x₃) = aasubmin-synth s
    aasubmin-ana (AAZipLam x₁ x₂ d) = aasubmin-ana d
    aasubmin-ana (AAZipInl x y) = aasubmin-ana y
    aasubmin-ana (AAZipInr x y) = aasubmin-ana y
    aasubmin-ana (AAZipCase1 a b c d e f g h) = aasubmin-synth e
    aasubmin-ana (AAZipCase2 a b c d e) = aasubmin-ana e
    aasubmin-ana (AAZipCase3 a b c d f) = aasubmin-ana f
    aasubmin-ana (AAZipProdL a b) = aasubmin-ana b
    aasubmin-ana (AAZipProdR a b) = aasubmin-ana b
    aasubmin-ana _ = ⊤

  -- the minimization predicate propagates through subsumption rules
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
  min-ana-lem SAConInl _ = <>
  min-ana-lem SAConInr _ = <>
  min-ana-lem (SAConCase1 x₁ x₂ x₃) _ = <>
  min-ana-lem (SAConCase2 x₁ x₂ x₃) _ = <>
  min-ana-lem SAConProd _ = <>
  
  -- any derivation of an action can be minimized to avoid this cases that
  -- induce non-determinism.
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
    min-synth SAConInl = _ , SAConInl , <>
    min-synth SAConInr = _ , SAConInr , <>
    min-synth (SAConCase1 a b c) = _ , (SAConCase1 a b c) , <>
    min-synth (SAConCase2 a b c) = _ , SAConCase2 a b c , <>
    min-synth SAConProd = _ , SAConProd , <>
    
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
    min-ana (AASubsume EETop (SAsc x₁) (SAConCase1 a b c) z) = _ ,
                                                                 AASubsume EETop (SAsc x₁) (SAConCase1 a b c) z , <>
    min-ana (AASubsume EETop (SVar x₁) (SAConCase1 a b c) z) = _ ,
                                                                 AASubsume EETop (SVar x₁) (SAConCase1 a b c) z , <>
    min-ana (AASubsume EETop (SAp y₁ x₁ x₂) (SAConCase1 a b c) z) = _ ,
                                                                      AASubsume EETop (SAp y₁ x₁ x₂) (SAConCase1 a b c) z , <>
    min-ana (AASubsume EETop SNum (SAConCase1 a b c) z) = _ ,
                                                            AASubsume EETop SNum (SAConCase1 a b c) z , <>
    min-ana (AASubsume EETop (SPlus x₁ x₂) (SAConCase1 a b c) z) = _ ,
                                                                     AASubsume EETop (SPlus x₁ x₂) (SAConCase1 a b c) z , <>
    min-ana (AASubsume EETop SEHole (SAConCase1 a b c) z) = _ , AAConCase a b , <>
    min-ana (AASubsume EETop (SNEHole y₁) (SAConCase1 a b c) z) = _ ,
                                                                    AASubsume EETop (SNEHole y₁) (SAConCase1 a b c) z , <>
    min-ana (AASubsume x y (SAConCase2 a b c) z) = _ , AASubsume x y (SAConCase2 a b c) z , <>
    min-ana (AASubsume EETop y SAConProd TCRefl) = ⟨ ▹ ⦇-⦈ ◃ , ⦇-⦈ ⟩₁ , AAConProd1 MPrProd , <>
    min-ana (AASubsume EETop y SAConProd TCHole2) = ⟨ ▹ ⦇-⦈ ◃ , ⦇-⦈ ⟩₁ , AAConProd1 MPrHole , <>
    min-ana (AASubsume EETop y SAConProd (TCProd z z₁)) = ⟨ ▹ ⦇-⦈ ◃ , ⦇-⦈ ⟩₁ , AAConProd1 MPrProd , <>
    
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
    min-ana (AASubsume x x₁ SAConInl TCRefl) = inl ▹ ⦇-⦈ ◃ , AAConInl1 MPPlus , <>
    min-ana (AASubsume x x₁ SAConInl TCHole2) = inl ▹ ⦇-⦈ ◃ , AAConInl1 MPHole , <>
    min-ana (AASubsume x x₁ SAConInl (TCPlus x₃ x₄)) = inl ▹ ⦇-⦈ ◃ , AAConInl1 MPPlus , <>
    min-ana (AASubsume x x₁ SAConInr TCRefl) = inr ▹ ⦇-⦈ ◃ , AAConInr1 MPPlus , <>
    min-ana (AASubsume x x₁ SAConInr TCHole2) = inr ▹ ⦇-⦈ ◃ , AAConInr1 MPHole , <>
    min-ana (AASubsume x x₁ SAConInr (TCPlus x₃ x₄)) = inr ▹ ⦇-⦈ ◃ , AAConInr1 MPPlus , <>
    min-ana (AAConInl1 x) = _ , AAConInl1 x , <>
    min-ana (AAConInl2 x) = _ , AAConInl2 x , <>
    min-ana (AAConInr1 x) = _ , AAConInr1 x , <>
    min-ana (AAConInr2 x) = _ , AAConInr2 x , <>
    min-ana (AAConCase x₁ x₂) = _ , AAConCase x₁ x₂ , <>
    min-ana (AAConProd1 x) = _ , (AAConProd1 x) , <>
    min-ana (AAConProd2 x) = _ , AAConProd2 x , <>
    min-ana (AAZipInl x x₁) with min-ana x₁
    ... | a , b , c = _ , AAZipInl x b , c
    min-ana (AAZipInr x x₁) with min-ana x₁
    ... | a , b , c = _ , AAZipInr x b , c
    min-ana (AAZipCase1 x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) with min-synth x₅
    ... | a , b , c = _ , AAZipCase1 x₁ x₂ x₃ x₄ b x₆ x₇ x₈ , c
    min-ana (AAZipCase2 x₁ x₂ x₃ x₄ x₅) with min-ana x₅
    ... | a , b , c = _ , AAZipCase2 x₁ x₂ x₃ x₄ b , c
    min-ana (AAZipCase3 x₁ x₂ x₃ x₄ x₆) with min-ana x₆
    ... | a , b , c = _ , AAZipCase3 x₁ x₂ x₃ x₄ b , c
    min-ana (AAZipProdL x x₁) with min-ana x₁
    ... | a , b , c = _ , AAZipProdL x b , c
    min-ana (AAZipProdR x x₁) with min-ana x₁
    ... | a , b , c = _ , (AAZipProdR x b) , c
    
  -- these theorems argue that if a derivation is already subsumption
  -- minimal than the minimzer does not change the resultant
  -- expression--that it's conservative in this sense. they do not argue
  -- that the derivation that's computer is itself the same as the input
  -- derivation.
  mutual
    min-fixed-synth : ∀ {Γ e t α e' t'} →
                         (d : Γ ⊢ e => t ~ α ~> e' => t') →
                         aasubmin-synth d →
                         e' == π1 (min-synth d)
    min-fixed-synth (SAMove x) min = refl
    min-fixed-synth SADel min = refl
    min-fixed-synth SAConAsc min = refl
    min-fixed-synth (SAConVar p) min = refl
    min-fixed-synth (SAConLam x₁) min = refl
    min-fixed-synth (SAConApArr x) min = refl
    min-fixed-synth (SAConApOtw x) min = refl
    min-fixed-synth SAConNumlit min = refl
    min-fixed-synth (SAConPlus1 x) min = refl
    min-fixed-synth (SAConPlus2 x) min = refl
    min-fixed-synth SAConNEHole min = refl
    min-fixed-synth (SAFinish x) min = refl
    min-fixed-synth (SAZipAsc1 x) min with min-fixed-ana x min
    ... | qq with min-ana x
    ... | (e'' , d' , min') = ap1 (λ q → q ·:₁ _) qq
    min-fixed-synth (SAZipAsc2 x x₁ x₂ x₃) min = refl
    min-fixed-synth (SAZipApArr x x₁ x₂ d x₃) min with min-fixed-synth d min
    ... | qq with min-synth d
    ... | (e'' , d' , min') = ap1 (λ q → q ∘₁ _) qq
    min-fixed-synth (SAZipApAna x x₁ x₂) min with min-fixed-ana x₂ min
    ... | qq with min-ana x₂
    ... | (e'' , _ , _) = ap1 (λ q → _ ∘₂ q) qq
    min-fixed-synth (SAZipPlus1 x) min with min-fixed-ana x min
    ... | qq with min-ana x
    ... | (e'' , _ , _) = ap1 (λ q → q ·+₁ _) qq
    min-fixed-synth (SAZipPlus2 x) min with min-fixed-ana x min
    ... | qq with min-ana x
    ... | (e'' , _ , _) = ap1 (λ q → _ ·+₂ q) qq
    min-fixed-synth (SAZipHole x x₁ d) min with min-fixed-synth d min
    ... | qq with min-synth d
    ... | (e'' , _ , _) = ap1 ⦇⌜_⌟⦈ qq
    min-fixed-synth SAConInl min = refl
    min-fixed-synth SAConInr min = refl
    min-fixed-synth (SAConCase1 x₁ x₂ x₃) min = refl
    min-fixed-synth (SAConCase2 x₁ x₂ x₃) min = refl
    min-fixed-synth SAConProd min = refl
    
    min-fixed-ana : ∀ {Γ e t α e' } →
                         (d : Γ ⊢ e ~ α ~> e' ⇐ t) →
                         aasubmin-ana d →
                         e' == π1 (min-ana d)
    min-fixed-ana (AASubsume x x₁ (SAMove x₂) x₃) min = refl
    min-fixed-ana (AASubsume x x₁ SADel x₃) min = refl
    min-fixed-ana (AASubsume x x₁ SAConAsc x₃) min = abort min
    min-fixed-ana (AASubsume x₁ x₂ (SAConVar p) x₃) min = refl
    min-fixed-ana (AASubsume x₁ x₂ (SAConLam x₃) x₄) min = abort min
    min-fixed-ana (AASubsume x x₁ (SAConApArr x₂) x₃) min = refl
    min-fixed-ana (AASubsume x x₁ (SAConApOtw x₂) x₃) min = refl
    min-fixed-ana (AASubsume x x₁ SAConNumlit x₃) min = refl
    min-fixed-ana (AASubsume x x₁ (SAConPlus1 x₂) x₃) min = refl
    min-fixed-ana (AASubsume x x₁ (SAConPlus2 x₂) x₃) min = refl
    min-fixed-ana (AASubsume x x₁ SAConNEHole x₃) min = refl
    min-fixed-ana (AASubsume x x₁ (SAFinish x₂) x₃) min = refl
    min-fixed-ana (AASubsume x x₁ (SAZipAsc1 x₂) x₃) min with min-fixed-ana x₂ min
    ... | qq with min-ana x₂
    ... | (e'' , _ , _) = ap1 (λ q → q ·:₁ _) qq
    min-fixed-ana (AASubsume x x₁ (SAZipAsc2 x₂ x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AASubsume x x₁ (SAZipApArr x₂ x₃ x₄ x₅ x₆) x₇) min with min-fixed-synth x₅ min
    ... | qq with min-synth x₅
    ... | (e'' , d' , min') = ap1 (λ q → q ∘₁ _) qq
    min-fixed-ana (AASubsume x x₁ (SAZipApAna x₂ x₃ x₄) x₅) min with min-fixed-ana x₄ min
    ... | qq with min-ana x₄
    ... | (e'' , _ , _) = ap1 (λ q → _ ∘₂ q) qq
    min-fixed-ana (AASubsume x x₁ (SAZipPlus1 x₂) x₃) min with min-fixed-ana x₂ min
    ... | qq with min-ana x₂
    ... | (e'' , _ , _) = ap1 (λ q → q ·+₁ _) qq
    min-fixed-ana (AASubsume x x₁ (SAZipPlus2 x₂) x₃) min with min-fixed-ana x₂ min
    ... | qq with min-ana x₂
    ... | (e'' , _ , _) = ap1 (λ q → _ ·+₂ q) qq
    min-fixed-ana (AASubsume x x₁ (SAZipHole x₂ x₃ x₄) x₅) min with min-fixed-synth x₄ min
    ... | qq with min-synth x₄
    ... | (e'' , _ , _) = ap1 ⦇⌜_⌟⦈ qq
    min-fixed-ana (AAMove x) min = refl
    min-fixed-ana AADel min = refl
    min-fixed-ana AAConAsc min = refl
    min-fixed-ana (AAConVar x₁ p) min = refl
    min-fixed-ana (AAConLam1 x₁ x₂) min = refl
    min-fixed-ana (AAConLam2 x₁ x₂) min = refl
    min-fixed-ana (AAConNumlit x) min = refl
    min-fixed-ana (AAFinish x) min = refl
    min-fixed-ana (AAZipLam x₁ x₂ d) min with min-fixed-ana d min
    ... | qq with min-ana d
    ... | (e'' , _ , _) = ap1 (λ q → ·λ _ q) qq
    min-fixed-ana (AASubsume x x₁ SAConInl x₃) min = abort min
    min-fixed-ana (AASubsume x x₁ SAConInr x₃) min = abort min
    min-fixed-ana (AASubsume EETop (SAsc x₁) (SAConCase1 x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AASubsume EETop (SVar x₁) (SAConCase1 x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AASubsume EETop (SAp x₂ x₁ x₃) (SAConCase1 x₄ x₅ x₆) x₇) min = refl
    min-fixed-ana (AASubsume EETop SNum (SAConCase1 x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AASubsume EETop (SPlus x₁ x₂) (SAConCase1 x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AASubsume EETop SEHole (SAConCase1 x₃ x₄ x₅) x₆) min = abort min
    min-fixed-ana (AASubsume EETop (SNEHole x₂) (SAConCase1 x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AASubsume x₁ x₂ (SAConCase2 x₃ x₄ x₅) x₆) min = refl
    min-fixed-ana (AAConInl1 x) min = refl
    min-fixed-ana (AAConInl2 x) min = refl
    min-fixed-ana (AAConInr1 x) min = refl
    min-fixed-ana (AAConInr2 x) min = refl
    min-fixed-ana (AAConCase x₁ x₂) min = refl
    min-fixed-ana (AAZipInl x d) min with min-fixed-ana d min
    ... | qq with min-ana d
    ... | (e'' , _ , _) = ap1 inl qq
    min-fixed-ana (AAZipInr x d) min with min-fixed-ana d min
    ... | qq with min-ana d
    ... | (e'' , _ , _) = ap1 inr qq
    min-fixed-ana (AAZipCase1 x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) min with min-fixed-synth x₅ min
    ... | qq with min-synth x₅
    ... | (e'' , _ , _) = ap1 (λ q → case₁ q _ _ _ _) qq
    min-fixed-ana (AAZipCase2 x₁ x₂ x₃ x₄ d) min with min-fixed-ana d min
    ... | qq with min-ana d
    ... | (e'' , _ , _) = ap1 (λ q → case₂ _ _ q _ _) qq
    min-fixed-ana (AAZipCase3 x₁ x₂ x₃ x₄ d) min with min-fixed-ana d min
    ... | qq with min-ana d
    ... | (e'' , _ , _) = ap1 (λ q → case₃ _ _ _ _ q) qq
    min-fixed-ana (AASubsume EETop SEHole SAConProd x₃) min = abort min
    min-fixed-ana (AAConProd1 x) min = refl
    min-fixed-ana (AAConProd2 x) min = refl
    min-fixed-ana (AAZipProdL x x₁) min with min-fixed-ana x₁ min
    ... | qq with min-ana x₁
    ... | (e'' , _ , _) = ap1 (λ q → ⟨ q , _ ⟩₁) qq
    min-fixed-ana (AAZipProdR x x₁) min with min-fixed-ana x₁ min
    ... | qq with min-ana x₁
    ... | (e'' , _ , _) = ap1 (λ q → ⟨ _ , q ⟩₂) qq
  

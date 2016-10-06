open import Nat
open import Prelude
open import core

module declarative where
   -- declarative type checking judgement for ė
  data _⊢_::_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
     DVar    : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                (n , t) ∈ Γ →
                Γ ⊢ X n :: t
     DAp     : {Γ : ·ctx} {e1 e2 : ė} {t t2 t' : τ̇} →
                Γ ⊢ e1 :: t →
                t ▸arr (t2 ==> t') →
                Γ ⊢ e2 :: t2 →
                Γ ⊢ (e1 ∘ e2) :: t'
     DNum    :  {Γ : ·ctx} {n : Nat} →
                Γ ⊢ N n :: num
     DPlus   : {Γ : ·ctx} {e1 e2 : ė}  →
                Γ ⊢ e1 :: num →
                Γ ⊢ e2 :: num →
                Γ ⊢ (e1 ·+ e2) :: num
     DEHole  : {Γ : ·ctx} → Γ ⊢ <||> :: <||>
     DNEHole  : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ e :: t →
                Γ ⊢ <| e |> :: <||>
     DLam : {Γ : ·ctx} {e : ė} {t t1 t2 : τ̇} {n : Nat} →
                n # Γ →
                t ▸arr (t1 ==> t2) →
                (Γ ,, (n , t1)) ⊢ e :: t2 →
                Γ ⊢ (·λ n e) :: t
     DSubsume : ∀{ Γ e a b } → Γ ⊢ e :: b → a ~ b → Γ ⊢ e :: a

  dex1 : ∅ ⊢ <||> ·+ <||> :: num
  dex1 = DPlus (DSubsume DEHole TCHole1) (DSubsume DEHole TCHole1)

  dex2 : ∅ ⊢ (N 3) ∘ (N 4) :: <||>
  dex2 = DAp (DSubsume (DSubsume DNum TCHole2) TCHole1) MAArr DNum

  -- erasure of ascriptions
  data er-asc : ė → ė → Set where
     ERAAsc : ∀{e t e'} →
              er-asc e e' →
              er-asc (e ·: t) e'
     ERAVar : ∀{n} → er-asc (X n) (X n)
     ERALam : ∀{x e e'} → er-asc e e' → er-asc (·λ x e) (·λ x e')
     ERANum : ∀{n} → er-asc (N n) (N n)
     ERAPlus : ∀{e1 e2 e1' e2'} →
              er-asc e1 e1' →
              er-asc e2 e2' →
              er-asc (e1 ·+ e2) (e1' ·+ e2')
     ERAEHole : er-asc <||> <||>
     ERANEHole : ∀{e e'} →
              er-asc e e' →
              er-asc <| e |> <| e' |>
     ERAAp : ∀{e1 e2 e1' e2'} →
              er-asc e1 e1' →
              er-asc e2 e2' →
              er-asc (e1 ∘ e2) (e1' ∘ e2')


  bidirdec : {Γ : ·ctx} {e e' : ė} {t : τ̇}
                → (Γ ⊢ e => t) + (Γ ⊢ e <= t)
                → er-asc e e'
                → Γ ⊢ e' :: t
    -- synthesis cases
  bidirdec (Inl (SAsc x)) (ERAAsc er) = bidirdec (Inr x) er
  bidirdec (Inl (SVar x)) ERAVar = DVar x
  bidirdec (Inl (SAp x x₁ x₂)) (ERAAp er er₁) = DAp (bidirdec (Inl x) er) x₁ (bidirdec (Inr x₂) er₁)
  bidirdec (Inl SNum) ERANum = DNum
  bidirdec (Inl (SPlus x x₁)) (ERAPlus er er₁) = DPlus (bidirdec (Inr x) er) (bidirdec (Inr x₁) er₁)
  bidirdec (Inl SEHole) ERAEHole = DEHole
  bidirdec (Inl (SNEHole x)) (ERANEHole er) = DNEHole (bidirdec (Inl x) er)

  bidirdec (Inr (ASubsume x x₁)) er = DSubsume (bidirdec (Inl x) er) x₁
  bidirdec (Inr (ALam x₁ x₂ x₃)) (ERALam er) = DLam x₁ x₂ (bidirdec (Inr x₃) er)

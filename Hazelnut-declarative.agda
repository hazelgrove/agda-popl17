open import Nat
open import Prelude
open import Hazelnut-core

module Hazelnut-declarative where
   -- declarative type checking judgement for ė
  data _⊢_::_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
     DVar    : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                (n , t) ∈ Γ →
                Γ ⊢ X n :: t
     DAp     : {Γ : ·ctx} {e1 e2 : ė} {t t2 : τ̇} →
                Γ ⊢ e1 :: (t2 ==> t) →
                Γ ⊢ e2 :: t2 →
                Γ ⊢ (e1 ∘ e2) :: t
     DNum    :  {Γ : ·ctx} {n : Nat} →
                Γ ⊢ N n :: num
     DPlus   : {Γ : ·ctx} {e1 e2 : ė}  →
                Γ ⊢ e1 :: num →
                Γ ⊢ e2 :: num →
                Γ ⊢ (e1 ·+ e2) :: num
     DEHole  : {Γ : ·ctx} → Γ ⊢ <||> :: <||>
     DFHole  : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ e :: t →
                Γ ⊢ <| e |> :: <||>
     DApHole : {Γ : ·ctx} {e1 e2 : ė} →
                Γ ⊢ e1 :: <||> →
                Γ ⊢ e2 :: <||> →
                Γ ⊢ (e1 ∘ e2) :: <||>
     DLam : {Γ : ·ctx} {e : ė} {t1 t2 : τ̇} {n : Nat} →
                n # Γ →
                (Γ ,, (n , t1)) ⊢ e :: t2 →
                Γ ⊢ (·λ n e) :: (t1 ==> t2)
     DSubsume : ∀{ Γ e a b } → Γ ⊢ e :: a → a ~ b → Γ ⊢ e :: b

  dex1 : ∅ ⊢ <||> ·+ <||> :: num
  dex1 = DPlus (DSubsume DEHole TCHole2) (DSubsume DEHole TCHole2)

  dex2 : ∅ ⊢ (N 3) ∘ (N 4) :: <||>
  dex2 = DAp (DSubsume (DSubsume DNum TCHole1) TCHole2) DNum

  -- erasure of ascriptions, following the 312 notes.
  data ||_|| : {e : ė} → ė → Set where
     -- EraseAsc : {e : ė} {x : Nat} →
  -- ||_|| : ė → ė
  -- || e ·: x ||   = || e ||
  -- || X x ||      = X x
  -- || ·λ x e ||   = ·λ x || e ||
  -- || N n ||      = N n
  -- || e1 ·+ e2 || = || e1 || ·+ || e2 ||
  -- || <||> ||     = <||>
  -- || <| e |> ||  = <| || e || |>
  -- || e1 ∘ e2 ||  = || e1 || ∘ || e2 ||

  -- decbidir : {Γ : ·ctx} {e : ė} {t : τ̇}
  --               → Γ ⊢ e :: t
  --               → (Γ ⊢ e => t) + (Γ ⊢ e <= t)
  --   -- synthesis cases
  -- decbidir (DVar x) = Inl (SVar x)
  -- decbidir (DAp d1 d2) with decbidir d1 | decbidir d2
  -- ... | Inl s1 | Inl s2 = Inl (SAp s1 (ASubsume s2 TCRefl))
  -- ... | Inl s1 | Inr a2 = Inl (SAp s1 a2)
  -- ... | Inr a1 | Inl s2 = Inl (SAp {!!} (ASubsume s2 TCRefl))
  -- ... | Inr a1 | Inr a2 = Inl (SAp {!!} a2)
  -- decbidir DNum = Inl SNum
  -- decbidir (DPlus d1 d2) with decbidir d1 | decbidir d2
  -- ... | Inl s1 | Inl s2 = Inl (SPlus (ASubsume s1 TCRefl) (ASubsume s2 TCRefl))
  -- ... | Inl s1 | Inr a2 = Inl (SPlus (ASubsume s1 TCRefl) a2)
  -- ... | Inr a1 | Inl s1 = Inl (SPlus a1                   (ASubsume s1 TCRefl))
  -- ... | Inr a1 | Inr a2 = Inl (SPlus a1                   a2)
  -- decbidir DEHole = Inl SEHole
  -- decbidir (DFHole d) with decbidir d
  -- ... | Inl synth = Inl (SFHole synth)
  -- ... | Inr (ASubsume d' _) = Inl (SFHole d')
  -- ... | Inr (ALam x ana) = Inl {!!}
  -- decbidir (DApHole d1 d2)  with decbidir d1 | decbidir d2
  -- ... | Inl s1 | Inl s2 = Inl (SApHole s1 (ASubsume s2 TCRefl))
  -- ... | Inl s1 | Inr a2 = Inl (SApHole s1 a2)
  -- ... | Inr a1 | Inl s2 = Inl (SApHole {!!} (ASubsume s2 TCRefl))
  -- ... | Inr a1 | Inr a2 = Inl (SApHole {!!} a2)
  --   -- analysis case
  -- decbidir (DLam x d) = Inr (ALam {!!} {!!})


  -- bidirdec : {Γ : ·ctx} {e : ė} {t : τ̇}
  --               → (Γ ⊢ e => t) + (Γ ⊢ e <= t)
  --               → Γ ⊢ e :: t
  --   -- synthesis cases
  -- bidirdec (Inl (SAsc d)) = {!!}
  -- bidirdec (Inl (SVar x)) = DVar x
  -- bidirdec (Inl (SAp d1 d2)) = DAp (bidirdec (Inl d1)) (bidirdec (Inr d2))
  -- bidirdec (Inl SNum) = DNum
  -- bidirdec (Inl (SPlus d1 d2)) = DPlus (bidirdec (Inr d1)) (bidirdec (Inr d2))
  -- bidirdec (Inl SEHole) = DEHole
  -- bidirdec (Inl (SFHole d)) = DFHole (bidirdec (Inl d))
  -- bidirdec (Inl (SApHole d1 d2)) = DApHole (bidirdec (Inl d1)) (bidirdec (Inr d2))
  --   --analysis cases
  -- bidirdec (Inr (ASubsume x x₁)) = {!synthunicity!}
  -- bidirdec (Inr (ALam x d)) = DLam x (bidirdec (Inr d))

  -- -- to be an isomoprhism you have to preserve structure.
  -- -- to : {Γ : ·ctx} {e : ė} {t : τ̇} →
  -- --        (d : Γ ⊢ e :: t) →
  -- --        (bidirdec (decbidir d)) == d
  -- -- to d = {!!}

  -- -- from : {Γ : ·ctx} {e : ė} {t : τ̇} →
  -- --        (dd : (Γ ⊢ e => t) + (Γ ⊢ e <= t)) →
  -- --        (decbidir (bidirdec dd)) == dd
  -- -- from dd = {!!}

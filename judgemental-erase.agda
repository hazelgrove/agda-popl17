open import Nat
open import Prelude
open import List
open import core

module judgemental-erase where
  data erase-t : τ̂ → τ̇ → Set where
    ETTop  : ∀{t} → erase-t (▹ t ◃) t
    ETArrL : ∀{t1 t1' t2} → erase-t t1 t1' → erase-t (t1 ==>₁ t2) (t1' ==> t2)
    ETArrR : ∀{t1 t2 t2'} → erase-t t2 t2' → erase-t (t1 ==>₂ t2) (t1 ==> t2')

  data erase-e : ê → ė → Set where
    EETop   : ∀{x}         → erase-e (▹ x ◃) x
    EEAscL  : ∀{e e' t}    → erase-e e e'   → erase-e (e ·:₁ t) (e' ·: t)
    EEAscR  : ∀{e t t'}    → erase-t t t'   → erase-e (e ·:₂ t) (e ·: t')
    EELam   : ∀{x e e'}    → erase-e e e'   → erase-e (·λ x e) (·λ x e')
    EEApL   : ∀{e1 e1' e2} → erase-e e1 e1' → erase-e (e1 ∘₁ e2) (e1' ∘ e2)
    EEApR   : ∀{e1 e2 e2'} → erase-e e2 e2' → erase-e (e1 ∘₂ e2) (e1 ∘ e2')
    EEPlusL : ∀{e1 e1' e2} → erase-e e1 e1' → erase-e (e1 ·+₁ e2) (e1' ·+ e2)
    EEPlusR : ∀{e1 e2 e2'} → erase-e e2 e2' → erase-e (e1 ·+₂ e2) (e1 ·+ e2')
    EEFHole : ∀{e e'}      → erase-e e e'   → erase-e <| e |>  <| e' |>

  -- this judgemental form really does agree with the function, that is to
  -- say that there's an isomorphism between them.
  erase-t◆ : {t : τ̂} {tr : τ̇} → (erase-t t tr) → (t ◆t == tr)
  erase-t◆ ETTop       = refl
  erase-t◆ (ETArrL p)  = ap1 (λ x → x ==> _) (erase-t◆ p)
  erase-t◆ (ETArrR p)  = ap1 (λ x → _ ==> x) (erase-t◆ p)

  erase-e◆ : {e : ê} {er : ė} → (erase-e e er) → (e ◆e == er)
  erase-e◆ EETop       = refl
  erase-e◆ (EEAscL p)  = ap1 (λ x → x ·: _)  (erase-e◆ p)
  erase-e◆ (EEAscR p)  = ap1 (λ x → _ ·: x)  (erase-t◆ p)
  erase-e◆ (EELam p)   = ap1 (λ e → ·λ _ e)  (erase-e◆ p)
  erase-e◆ (EEApL p)   = ap1 (λ x → x ∘ _)   (erase-e◆ p)
  erase-e◆ (EEApR p)   = ap1 (λ x → _ ∘ x)   (erase-e◆ p)
  erase-e◆ (EEPlusL p) = ap1 (λ x → x ·+ _)  (erase-e◆ p)
  erase-e◆ (EEPlusR p) = ap1 (λ x → _ ·+ x)  (erase-e◆ p)
  erase-e◆ (EEFHole p) = ap1 (λ x → <| x |>) (erase-e◆ p)

  ◆erase-t : (t : τ̂) (tr : τ̇) → (t ◆t == tr) → (erase-t t tr)
  ◆erase-t ▹ .num ◃ num refl = ETTop
  ◆erase-t ▹ .<||> ◃ <||> refl = ETTop
  ◆erase-t ▹ .(tr ==> tr₁) ◃ (tr ==> tr₁) refl = ETTop
  ◆erase-t (t ==>₁ x) (.(t ◆t) ==> .x) refl = ETArrL (◆erase-t t (t ◆t) refl)
  ◆erase-t (x ==>₂ t) (.x ==> .(t ◆t)) refl = ETArrR (◆erase-t t (t ◆t) refl)

  ◆erase-e : (e : ê) (er : ė) → (e ◆e == er) → (erase-e e er)
  ◆erase-e ▹ x ◃ .x refl = EETop
  ◆erase-e (e ·:₁ x) .((e ◆e) ·: x) refl = EEAscL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ·:₂ x₁) .(x ·: (x₁ ◆t)) refl = EEAscR (◆erase-t x₁ (x₁ ◆t) refl)
  ◆erase-e (·λ x e) .(·λ x (e ◆e)) refl = EELam (◆erase-e e (e ◆e) refl)
  ◆erase-e (e ∘₁ x) .((e ◆e) ∘ x) refl = EEApL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ∘₂ e) .(x ∘ (e ◆e)) refl = EEApR (◆erase-e e (e ◆e) refl)
  ◆erase-e (e ·+₁ x) .((e ◆e) ·+ x) refl = EEPlusL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ·+₂ e) .(x ·+ (e ◆e)) refl = EEPlusR (◆erase-e e (e ◆e) refl)
  ◆erase-e <| e |> .(<| e ◆e |>) refl = EEFHole (◆erase-e e (e ◆e) refl)

  -- the isomorphism with a function implies that the judgement is
  -- well-moded.
  erase-e-mode : (e : ê) → Σ[ er ∈ ė ] (erase-e e er)
  erase-e-mode e = (e ◆e) , (◆erase-e e (e ◆e) refl)

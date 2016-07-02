open import Nat
open import Prelude
open import List
open import core

-- erasure of focus in the types and expressions is defined in the paper,
-- and in the core file, as a function on zexpressions. because of the
-- particular encoding of all the judgments as datatypes and the agda
-- semantics for pattern matching, it is sometimes also convenient to have
-- a judgemental form of erasure.
--
-- this file describes the obvious encoding of the view this function as a
-- jugement relating input and output as a datatype, and argues that this
-- encoding is correct by showing a isomorphism with the function. we also
-- show that as a correlary, the judgement is well moded at (∀, ∃!), which
-- is unsurprising if the jugement is written correctly.
--
-- taken together, these proofs allow us to move between the judgemental
-- form of erasure and the function form when it's convenient.
--
-- while we do not have it, the argument given here is sufficiently strong
-- to produce an equality between these things in a system with the
-- univalence axiom, as described in the homotopy type theory book and the
-- associated work done in agda.
module judgemental-erase where

  -- jugemental type erasure
  data erase-t : τ̂ → τ̇ → Set where
    ETTop  : ∀{t} → erase-t (▹ t ◃) t
    ETArrL : ∀{t1 t1' t2} → erase-t t1 t1' → erase-t (t1 ==>₁ t2) (t1' ==> t2)
    ETArrR : ∀{t1 t2 t2'} → erase-t t2 t2' → erase-t (t1 ==>₂ t2) (t1 ==> t2')

  -- judgemental expression erasure
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


  -- this pair of theorems moves from the judgmental form to the function form
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

  -- this pair of theorems moves back from judgmental form to the function form
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

  -- taken together, these two theorems demonstrate that the round-trip of
  -- one of the pairings above is stable. as a consequence of the
  -- properties of quasi-inverses, demonstrating either round trip is
  -- sufficient to show that the whole thing is an isomorphism.
  erase-trt : (t : τ̂) (tr : τ̇) → (x : t ◆t == tr)  → (erase-t◆ (◆erase-t t tr x)) == x
  erase-trt ▹ .num ◃ num refl = refl
  erase-trt ▹ .<||> ◃ <||> refl = refl
  erase-trt ▹ .(tr ==> tr₁) ◃ (tr ==> tr₁) refl = refl
  erase-trt (t ==>₁ x) (.(t ◆t) ==> .x) refl = ap1 (λ a → ap1 (λ x₁ → x₁ ==> x) a) (erase-trt t _ refl)
  erase-trt (x ==>₂ t) (.x ==> .(t ◆t)) refl = ap1 (λ a → ap1 (_==>_ x) a) (erase-trt t _ refl)

  erase-ert : (e : ê) (er : ė) → (x : e ◆e == er)  → (erase-e◆ (◆erase-e e er x)) == x
  erase-ert ▹ x ◃ .x refl = refl
  erase-ert (e ·:₁ x) .((e ◆e) ·: x) refl = ap1 (λ a → ap1 (λ x₁ → x₁ ·: x) a) (erase-ert e _ refl)
  erase-ert (x ·:₂ t) .(x ·: (t ◆t)) refl =  ap1 (λ a → ap1 (_·:_ x) a) (erase-trt t _ refl)
  erase-ert (·λ x e) .(·λ x (e ◆e)) refl = ap1 (λ a → ap1 (·λ x) a) (erase-ert e _ refl)
  erase-ert (e ∘₁ x) .((e ◆e) ∘ x) refl =  ap1 (λ a → ap1 (λ x₁ → x₁ ∘ x) a) (erase-ert e _ refl)
  erase-ert (x ∘₂ e) .(x ∘ (e ◆e)) refl = ap1 (λ a → ap1 (_∘_ x) a) (erase-ert e _ refl)
  erase-ert (e ·+₁ x) .((e ◆e) ·+ x) refl = ap1 (λ a → ap1 (λ x₁ → x₁ ·+ x) a) (erase-ert e _ refl)
  erase-ert (x ·+₂ e) .(x ·+ (e ◆e)) refl = ap1 (λ a → ap1 (_·+_ x) a) (erase-ert e _ refl)
  erase-ert <| e |> .(<| e ◆e |>) refl = ap1 (λ a → ap1 <|_|> a) (erase-ert e _ refl)

  -- this isomorphism amounts to the argument that the judgement has mode
  -- (∀, !∃), where uniqueness comes from erase-e◆.
  erase-e-mode : (e : ê) → Σ[ er ∈ ė ] (erase-e e er)
  erase-e-mode e = (e ◆e) , (◆erase-e e (e ◆e) refl)

open import Nat
open import Prelude
open import List
open import core

-- erasure of cursor in the types and expressions is defined in the paper,
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

  --cursor erasure for types, as written in the paper
  _◆t : τ̂ → τ̇
  ▹ t ◃ ◆t =  t
  (t1 ==>₁ t2) ◆t = (t1 ◆t) ==> t2
  (t1 ==>₂ t2) ◆t = t1 ==> (t2 ◆t)
  (t1 ⊕₁ t2) ◆t = (t1 ◆t) ⊕ t2
  (t1 ⊕₂ t2) ◆t = t1 ⊕ (t2 ◆t)

  --cursor erasure for expressions, as written in the paper
  _◆e : ê → ė
  ▹ x ◃ ◆e       = x
  (e ·:₁ t) ◆e   = (e ◆e) ·: t
  (e ·:₂ t) ◆e   = e      ·: (t ◆t)
  ·λ x e ◆e      = ·λ x (e ◆e)
  (e1 ∘₁ e2) ◆e  = (e1 ◆e) ∘ e2
  (e1 ∘₂ e2) ◆e  = e1      ∘ (e2 ◆e)
  (e1 ·+₁ e2) ◆e = (e1 ◆e) ·+ e2
  (e1 ·+₂ e2) ◆e = e1      ·+ (e2 ◆e)
  <| e |> ◆e     = <| e ◆e |>
  (inl e) ◆e     = inl (e ◆e)
  (inr e) ◆e     = inr (e ◆e)
  (case₁ e x e1 y e2) ◆e = case (e ◆e) x e1 y e2
  (case₂ e x e1 y e2) ◆e = case e x (e1 ◆e) y e2
  (case₃ e x e1 y e2) ◆e = case e x e1 y (e2 ◆e)

  -- this pair of theorems moves from the judgmental form to the function form
  erase-t◆ : {t : τ̂} {tr : τ̇} → (erase-t t tr) → (t ◆t == tr)
  erase-t◆ ETTop       = refl
  erase-t◆ (ETArrL p)  = ap1 (λ x → x ==> _) (erase-t◆ p)
  erase-t◆ (ETArrR p)  = ap1 (λ x → _ ==> x) (erase-t◆ p)
  erase-t◆ (ETPlusL p) = ap1 (λ x → x ⊕ _) (erase-t◆ p)
  erase-t◆ (ETPlusR p) = ap1 (λ x → _ ⊕ x) (erase-t◆ p)

  erase-e◆ : {e : ê} {er : ė} → (erase-e e er) → (e ◆e == er)
  erase-e◆ EETop       = refl
  erase-e◆ (EEAscL p)  = ap1 (λ x → x ·: _)  (erase-e◆ p)
  erase-e◆ (EEAscR p)  = ap1 (λ x → _ ·: x)  (erase-t◆ p)
  erase-e◆ (EELam p)   = ap1 (λ e → ·λ _ e)  (erase-e◆ p)
  erase-e◆ (EEApL p)   = ap1 (λ x → x ∘ _)   (erase-e◆ p)
  erase-e◆ (EEApR p)   = ap1 (λ x → _ ∘ x)   (erase-e◆ p)
  erase-e◆ (EEPlusL p) = ap1 (λ x → x ·+ _)  (erase-e◆ p)
  erase-e◆ (EEPlusR p) = ap1 (λ x → _ ·+ x)  (erase-e◆ p)
  erase-e◆ (EENEHole p) = ap1 (λ x → <| x |>) (erase-e◆ p)
  erase-e◆ (EEInl p)    = ap1 inl (erase-e◆ p)
  erase-e◆ (EEInr p)    = ap1 inr (erase-e◆ p)
  erase-e◆ (EECase1 p)  = ap1 (λ x → case x _ _ _ _) (erase-e◆ p)
  erase-e◆ (EECase2 p)  = ap1 (λ x → case _ _ x _ _) (erase-e◆ p)
  erase-e◆ (EECase3 p)  = ap1 (λ x → case _ _ _ _ x) (erase-e◆ p)

  -- this pair of theorems moves back from judgmental form to the function form
  ◆erase-t : (t : τ̂) (tr : τ̇) → (t ◆t == tr) → (erase-t t tr)
  ◆erase-t ▹ .num ◃ num refl = ETTop
  ◆erase-t ▹ .<||> ◃ <||> refl = ETTop
  ◆erase-t ▹ .(tr ==> tr₁) ◃ (tr ==> tr₁) refl = ETTop
  ◆erase-t ▹ .(t1 ⊕ t2) ◃ (t1 ⊕ t2) refl = ETTop
  ◆erase-t (t ==>₁ x) (.(t ◆t) ==> .x) refl = ETArrL (◆erase-t t (t ◆t) refl)
  ◆erase-t (x ==>₂ t) (.x ==> .(t ◆t)) refl = ETArrR (◆erase-t t (t ◆t) refl)
  ◆erase-t (t1 ⊕₁ t2) (.(t1 ◆t) ⊕ .t2) refl = ETPlusL (◆erase-t t1 (t1 ◆t) refl)
  ◆erase-t (t1 ⊕₂ t2) (.t1 ⊕ .(t2 ◆t)) refl = ETPlusR (◆erase-t t2 (t2 ◆t) refl)

  ◆erase-e : (e : ê) (er : ė) → (e ◆e == er) → (erase-e e er)
  ◆erase-e ▹ x ◃ .x refl = EETop
  ◆erase-e (e ·:₁ x) .((e ◆e) ·: x) refl = EEAscL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ·:₂ x₁) .(x ·: (x₁ ◆t)) refl = EEAscR (◆erase-t x₁ (x₁ ◆t) refl)
  ◆erase-e (·λ x e) .(·λ x (e ◆e)) refl = EELam (◆erase-e e (e ◆e) refl)
  ◆erase-e (e ∘₁ x) .((e ◆e) ∘ x) refl = EEApL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ∘₂ e) .(x ∘ (e ◆e)) refl = EEApR (◆erase-e e (e ◆e) refl)
  ◆erase-e (e ·+₁ x) .((e ◆e) ·+ x) refl = EEPlusL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ·+₂ e) .(x ·+ (e ◆e)) refl = EEPlusR (◆erase-e e (e ◆e) refl)
  ◆erase-e <| e |> .(<| e ◆e |>) refl = EENEHole (◆erase-e e (e ◆e) refl)
  ◆erase-e (inl e) ._ refl = EEInl (◆erase-e e (e ◆e) refl)
  ◆erase-e (inr e) ._ refl = EEInr (◆erase-e e (e ◆e) refl)
  ◆erase-e (case₁ e _ _ _ _) ._ refl = EECase1 (◆erase-e e (e ◆e) refl)
  ◆erase-e (case₂ _ _ e _ _) ._ refl = EECase2 (◆erase-e e (e ◆e) refl)
  ◆erase-e (case₃ _ _ _ _ e) ._ refl = EECase3 (◆erase-e e (e ◆e) refl)

  -- taken together, these two theorems demonstrate that the round-trip of
  -- one of the pairings above is stable. as a consequence of the
  -- properties of quasi-inverses, demonstrating either round trip is
  -- sufficient to show that the whole thing is an isomorphism.
  erase-trt : (t : τ̂) (tr : τ̇) → (x : t ◆t == tr)  → (erase-t◆ (◆erase-t t tr x)) == x
  erase-trt ▹ .num ◃ num refl = refl
  erase-trt ▹ .<||> ◃ <||> refl = refl
  erase-trt ▹ .(tr ==> tr₁) ◃ (tr ==> tr₁) refl = refl
  erase-trt ▹ .(tr ⊕ tr₁) ◃ (tr ⊕ tr₁) refl = refl
  erase-trt (t ==>₁ x) (.(t ◆t) ==> .x) refl = ap1 (λ a → ap1 (λ x₁ → x₁ ==> x) a) (erase-trt t _ refl)
  erase-trt (x ==>₂ t) (.x ==> .(t ◆t)) refl = ap1 (λ a → ap1 (_==>_ x) a) (erase-trt t _ refl)
  erase-trt (t ⊕₁ x) (.(t ◆t) ⊕ .x) refl = ap1 (λ a → ap1 (λ x₁ → x₁ ⊕ x) a) (erase-trt t _ refl)
  erase-trt (x ⊕₂ t) (.x ⊕ .(t ◆t)) refl = ap1 (λ a → ap1 (_⊕_ x) a) (erase-trt t _ refl)

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
  erase-ert (inl e) ._ refl = ap1 (ap1 inl) (erase-ert e (e ◆e) refl)
  erase-ert (inr e) ._ refl = ap1 (ap1 inr) (erase-ert e (e ◆e) refl)
  erase-ert (case₁ e _ _ _ _) ._ refl = ap1 (ap1 (λ x → case x _ _ _ _)) (erase-ert e (e ◆e) refl)
  erase-ert (case₂ _ _ e _ _) ._ refl = ap1 (ap1 (λ x → case _ _ x _ _)) (erase-ert e (e ◆e) refl)
  erase-ert (case₃ _ _ _ _ e) ._ refl = ap1 (ap1 (λ x → case _ _ _ _ x)) (erase-ert e (e ◆e) refl)

  -- this isomorphism amounts to the argument that the judgement has mode
  -- (∀, !∃), where uniqueness comes from erase-e◆.
  erase-e-mode : (e : ê) → Σ[ er ∈ ė ] (erase-e e er)
  erase-e-mode e = (e ◆e) , (◆erase-e e (e ◆e) refl)

  -- some translations. these are not needed to show that this is an ok
  -- encoding pair, but they are helpful when actually using it.

  -- even more specifically, the relation relates an expression to its
  -- functional erasure.
  rel◆t : (t : τ̂) → (erase-t t (t ◆t))
  rel◆t t = ◆erase-t t (t ◆t) refl

  rel◆ : (e : ê) → (erase-e e (e ◆e))
  rel◆ e = ◆erase-e e (e ◆e) refl

  lem-erase-ana : ∀{e e' Γ t} → erase-e e e' → Γ ⊢ e' <= t → Γ ⊢ (e ◆e) <= t
  lem-erase-ana er wt = tr (λ x → _ ⊢ x <= _) (! (erase-e◆ er)) wt

  lem-erase-synth : ∀{e e' Γ t} → erase-e e e' → Γ ⊢ e' => t → Γ ⊢ (e ◆e) => t
  lem-erase-synth er wt = tr (λ x → _ ⊢ x => _) (! (erase-e◆ er)) wt

  lem-synth-erase : ∀{Γ e t e' } → Γ ⊢ e ◆e => t → erase-e e e' → Γ ⊢ e' => t
  lem-synth-erase d1 d2 with erase-e◆ d2
  ... | refl = d1

  eraset-det : ∀{t t' t''} → erase-t t t' → erase-t t t'' → t' == t''
  eraset-det e1 e2 with erase-t◆ e1
  ... | refl = erase-t◆ e2

  erasee-det : ∀{e e' e''} → erase-e e e' → erase-e e e'' → e' == e''
  erasee-det e1 e2 with erase-e◆ e1
  ... | refl = erase-e◆ e2

  erase-in-hole : ∀ {e e'} → erase-e e e' → erase-e <| e |> <| e' |>
  erase-in-hole (EENEHole er) = EENEHole (erase-in-hole er)
  erase-in-hole x = EENEHole x

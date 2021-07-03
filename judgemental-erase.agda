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
  (t1 ⊠₁ t2) ◆t = (t1 ◆t) ⊠ t2
  (t1 ⊠₂ t2) ◆t = t1 ⊠ (t2 ◆t)
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
  ⦇⌜ e ⌟⦈ ◆e     = ⦇⌜ e ◆e ⌟⦈
  (inl e) ◆e     = inl (e ◆e)
  (inr e) ◆e     = inr (e ◆e)
  (case₁ e x e1 y e2) ◆e = case (e ◆e) x e1 y e2
  (case₂ e x e1 y e2) ◆e = case e x (e1 ◆e) y e2
  (case₃ e x e1 y e2) ◆e = case e x e1 y (e2 ◆e)
  ⟨ e1 , e2 ⟩₁ ◆e = ⟨ e1 ◆e , e2 ⟩
  ⟨ e1 , e2 ⟩₂ ◆e = ⟨ e1 , e2 ◆e ⟩
  

  -- this pair of theorems moves from the judgmental form to the function form
  erase-t◆ : {t : τ̂} {tr : τ̇} → (erase-t t tr) → (t ◆t == tr)
  erase-t◆ ETTop       = refl
  erase-t◆ (ETArrL p)  = ap1 (λ x → x ==> _) (erase-t◆ p)
  erase-t◆ (ETArrR p)  = ap1 (λ x → _ ==> x) (erase-t◆ p)
  erase-t◆ (ETPlusL p) = ap1 (λ x → x ⊕ _) (erase-t◆ p)
  erase-t◆ (ETPlusR p) = ap1 (λ x → _ ⊕ x) (erase-t◆ p)
  erase-t◆ (ETProdL p) = ap1 (λ x → x ⊠ _) (erase-t◆ p)
  erase-t◆ (ETProdR p) = ap1 (λ x → _ ⊠ x) (erase-t◆ p)
  
  erase-e◆ : {e : ê} {er : ė} → (erase-e e er) → (e ◆e == er)
  erase-e◆ EETop       = refl
  erase-e◆ (EEAscL p)  with erase-e◆ p
  erase-e◆ (EEAscL p) | refl = refl -- ap1 (λ x → x ·: _)  (erase-e◆ p)
  erase-e◆ (EEAscR p)  = ap1 (λ x → _ ·: x)  (erase-t◆ p)
  erase-e◆ (EELam p)   = ap1 (λ e → ·λ _ e)  (erase-e◆ p)
  erase-e◆ (EEApL p)   = ap1 (λ x → x ∘ _)   (erase-e◆ p)
  erase-e◆ (EEApR p)   = ap1 (λ x → _ ∘ x)   (erase-e◆ p)
  erase-e◆ (EEPlusL p) = ap1 (λ x → x ·+ _)  (erase-e◆ p)
  erase-e◆ (EEPlusR p) = ap1 (λ x → _ ·+ x)  (erase-e◆ p)
  erase-e◆ (EENEHole p) = ap1 (λ x → ⦇⌜ x ⌟⦈) (erase-e◆ p)
  erase-e◆ (EEInl p)    = ap1 inl (erase-e◆ p)
  erase-e◆ (EEInr p)    = ap1 inr (erase-e◆ p)
  erase-e◆ (EECase1 p)  = ap1 (λ x → case x _ _ _ _) (erase-e◆ p)
  erase-e◆ (EECase2 p)  = ap1 (λ x → case _ _ x _ _) (erase-e◆ p)
  erase-e◆ (EECase3 p)  = ap1 (λ x → case _ _ _ _ x) (erase-e◆ p)
  erase-e◆ (EEProdL p)  = ap1 (λ x → ⟨ x , _ ⟩ )  (erase-e◆ p)
  erase-e◆ (EEProdR p)  = ap1 (λ x → ⟨ _ , x ⟩ )  (erase-e◆ p)
  
  -- this pair of theorems moves back from judgmental form to the function form
  ◆erase-t : (t : τ̂) (tr : τ̇) → (t ◆t == tr) → (erase-t t tr)
  ◆erase-t ▹ x ◃ .x refl = ETTop
  ◆erase-t (t ==>₁ x) (.(t ◆t) ==> .x) refl with ◆erase-t t (t ◆t) refl
  ... | ih = ETArrL ih
  ◆erase-t (x ==>₂ t) (.x ==> .(t ◆t)) refl with ◆erase-t t (t ◆t) refl
  ... | ih = ETArrR ih
  ◆erase-t (t1 ⊕₁ t2) (.(t1 ◆t) ⊕ .t2) refl = ETPlusL (◆erase-t t1 (t1 ◆t) refl)
  ◆erase-t (t1 ⊕₂ t2) (.t1 ⊕ .(t2 ◆t)) refl = ETPlusR (◆erase-t t2 (t2 ◆t) refl)
  ◆erase-t (t1 ⊠₁ t2) (.(t1 ◆t) ⊠ .t2) refl = ETProdL (◆erase-t t1 (t1 ◆t) refl)
  ◆erase-t (t1 ⊠₂ t2) (.t1 ⊠ .(t2 ◆t)) refl = ETProdR (◆erase-t t2 (t2 ◆t) refl)
  
  ◆erase-e : (e : ê) (er : ė) → (e ◆e == er) → (erase-e e er)
  ◆erase-e ▹ x ◃ .x refl = EETop
  ◆erase-e (e ·:₁ x) .((e ◆e) ·: x) refl with ◆erase-e e (e ◆e) refl
  ... | ih = EEAscL ih
  ◆erase-e (x ·:₂ x₁) .(x ·: (x₁ ◆t)) refl = EEAscR (◆erase-t x₁ (x₁ ◆t) refl)
  ◆erase-e (·λ x e) .(·λ x (e ◆e)) refl = EELam (◆erase-e e (e ◆e) refl)
  ◆erase-e (e ∘₁ x) .((e ◆e) ∘ x) refl = EEApL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ∘₂ e) .(x ∘ (e ◆e)) refl = EEApR (◆erase-e e (e ◆e) refl)
  ◆erase-e (e ·+₁ x) .((e ◆e) ·+ x) refl = EEPlusL (◆erase-e e (e ◆e) refl)
  ◆erase-e (x ·+₂ e) .(x ·+ (e ◆e)) refl = EEPlusR (◆erase-e e (e ◆e) refl)
  ◆erase-e ⦇⌜ e ⌟⦈ .(⦇⌜ e ◆e ⌟⦈) refl = EENEHole (◆erase-e e (e ◆e) refl)
  ◆erase-e (inl e) ._ refl = EEInl (◆erase-e e (e ◆e) refl)
  ◆erase-e (inr e) ._ refl = EEInr (◆erase-e e (e ◆e) refl)
  ◆erase-e (case₁ e _ _ _ _) ._ refl = EECase1 (◆erase-e e (e ◆e) refl)
  ◆erase-e (case₂ _ _ e _ _) ._ refl = EECase2 (◆erase-e e (e ◆e) refl)
  ◆erase-e (case₃ _ _ _ _ e) ._ refl = EECase3 (◆erase-e e (e ◆e) refl)
  ◆erase-e ⟨ e , x ⟩₁ .(⟨ (e ◆e) , x ⟩) refl = EEProdL (◆erase-e e (e ◆e) refl)
  ◆erase-e ⟨ x , e ⟩₂ .(⟨ x , (e ◆e) ⟩) refl = EEProdR (◆erase-e e (e ◆e) refl)
  
  -- jugemental erasure for both types and terms only has one proof for
  -- relating the a term to its non-judgemental erasure
  t-contr : (t : τ̂) → (x y : erase-t t (t ◆t)) → x == y
  t-contr ▹ x ◃ ETTop ETTop = refl
  t-contr (t ==>₁ x) (ETArrL y) (ETArrL z) = ap1 ETArrL (t-contr t y z)
  t-contr (x ==>₂ t) (ETArrR y) (ETArrR z) = ap1 ETArrR (t-contr t y z)
  t-contr (x ⊕₁ x₁) (ETPlusL y) (ETPlusL z) = ap1 ETPlusL (t-contr x y z)
  t-contr (x₁ ⊕₂ x) (ETPlusR y) (ETPlusR z) = ap1 ETPlusR (t-contr x y z)
  t-contr (x ⊠₁ x₁) (ETProdL y) (ETProdL z) = ap1 ETProdL (t-contr x y z)
  t-contr (x₁ ⊠₂ x) (ETProdR y) (ETProdR z) = ap1 ETProdR (t-contr x y z)
  
  e-contr : (e : ê) → (x y : erase-e e (e ◆e)) → x == y
  e-contr ▹ x ◃ EETop EETop = refl
  e-contr (e ·:₁ x) (EEAscL x₁) (EEAscL y) = ap1 EEAscL (e-contr e x₁ y)
  e-contr (x₁ ·:₂ x) (EEAscR x₂) (EEAscR x₃) = ap1 EEAscR (t-contr x x₂ x₃)
  e-contr (·λ x e) (EELam x₁) (EELam y) = ap1 EELam (e-contr e x₁ y)
  e-contr (e ∘₁ x) (EEApL x₁) (EEApL y) = ap1 EEApL (e-contr e x₁ y)
  e-contr (x ∘₂ e) (EEApR x₁) (EEApR y) = ap1 EEApR (e-contr e x₁ y)
  e-contr (e ·+₁ x) (EEPlusL x₁) (EEPlusL y) = ap1 EEPlusL (e-contr e x₁ y)
  e-contr (x ·+₂ e) (EEPlusR x₁) (EEPlusR y) = ap1 EEPlusR (e-contr e x₁ y)
  e-contr ⦇⌜ e ⌟⦈ (EENEHole x) (EENEHole y) = ap1 EENEHole (e-contr e x y)
  e-contr (inl x) (EEInl y) (EEInl z) = ap1 EEInl (e-contr x y z)
  e-contr (inr x) (EEInr y) (EEInr z) = ap1 EEInr (e-contr x y z)
  e-contr (case₁ x x₁ x₂ x₃ x₄) (EECase1 y) (EECase1 z) = ap1 EECase1 (e-contr x y z)
  e-contr (case₂ x₁ x₂ x x₃ x₄) (EECase2 y) (EECase2 z) = ap1 EECase2 (e-contr x y z)
  e-contr (case₃ x₁ x₂ x₃ x₄ x) (EECase3 y) (EECase3 z) = ap1 EECase3 (e-contr x y z)
  e-contr ⟨ e , x ⟩₁ (EEProdL x₁) (EEProdL y) = ap1 EEProdL (e-contr e x₁ y)
  e-contr ⟨ x , e ⟩₂ (EEProdR x₁) (EEProdR y) = ap1 EEProdR (e-contr e x₁ y)
  
  -- taken together, these four theorems demonstrate that both round-trips
  -- of the above functions are stable up to ==
  erase-trt1 : (t : τ̂) (tr : τ̇) → (x : t ◆t == tr) → (erase-t◆ (◆erase-t t tr x)) == x
  erase-trt1 ▹ x ◃ .x refl = refl
  erase-trt1 (t ==>₁ x) (.(t ◆t) ==> .x) refl with erase-t◆ (◆erase-t t (t ◆t) refl)
  erase-trt1 (t ==>₁ x) (.(t ◆t) ==> .x) refl | refl = refl
  erase-trt1 (x ==>₂ t) (.x ==> .(t ◆t)) refl with erase-t◆ (◆erase-t t (t ◆t) refl)
  erase-trt1 (x ==>₂ t) (.x ==> .(t ◆t)) refl | refl = refl
  erase-trt1 (x ⊕₁ x₁) .((x ◆t) ⊕ x₁) refl with erase-t◆ (◆erase-t x (x ◆t) refl)
  erase-trt1 (x ⊕₁ x₁) .((x ◆t) ⊕ x₁) refl | refl = refl
  erase-trt1 (x ⊕₂ x₁) .(x ⊕ (x₁ ◆t)) refl with erase-t◆ (◆erase-t x₁ (x₁ ◆t) refl)
  erase-trt1 (x ⊕₂ x₁) .(x ⊕ (x₁ ◆t)) refl | refl = refl
  erase-trt1 (x ⊠₁ x₁) .((x ◆t) ⊠ x₁) refl with erase-t◆ (◆erase-t x (x ◆t) refl)
  erase-trt1 (x ⊠₁ x₁) .((x ◆t) ⊠ x₁) refl | refl = refl
  erase-trt1 (x ⊠₂ x₁) .(x ⊠ (x₁ ◆t)) refl with erase-t◆ (◆erase-t x₁ (x₁ ◆t) refl)
  erase-trt1 (x ⊠₂ x₁) .(x ⊠ (x₁ ◆t)) refl | refl = refl
  
  erase-trt2 : (t : τ̂) (tr : τ̇) → (x : erase-t t tr) → ◆erase-t t tr (erase-t◆ x) == x
  erase-trt2 .(▹ tr ◃) tr ETTop = refl
  erase-trt2 _ _ (ETArrL ETTop) = refl
  erase-trt2 (t1 ==>₁ t2) _ (ETArrL x) with erase-t◆ x
  erase-trt2 (t1 ==>₁ t2) _ (ETArrL x) | refl = ap1 ETArrL (t-contr _ (◆erase-t t1 (t1 ◆t) refl) x)
  erase-trt2 (t1 ==>₂ t2) _ (ETArrR x) with erase-t◆ x
  erase-trt2 (t1 ==>₂ t2) _ (ETArrR x) | refl = ap1 ETArrR (t-contr _ (◆erase-t t2 (t2 ◆t) refl) x)
  erase-trt2 (t1 ⊕₁ t2) _ (ETPlusL x) with erase-t◆ x
  erase-trt2 (t1 ⊕₁ t2) _ (ETPlusL x) | refl = ap1 ETPlusL (t-contr _ (◆erase-t t1 (t1 ◆t) refl) x)
  erase-trt2 (t1 ⊕₂ t2) _ (ETPlusR x) with erase-t◆ x
  erase-trt2 (t1 ⊕₂ t2) _ (ETPlusR x) | refl = ap1 ETPlusR (t-contr _ (◆erase-t t2 (t2 ◆t) refl) x)
  erase-trt2 (t1 ⊠₁ t2) _ (ETProdL x) with erase-t◆ x
  erase-trt2 (t1 ⊠₁ t2) _ (ETProdL x) | refl = ap1 ETProdL (t-contr _ (◆erase-t t1 (t1 ◆t) refl) x)
  erase-trt2 (t1 ⊠₂ t2) _ (ETProdR x) with erase-t◆ x
  erase-trt2 (t1 ⊠₂ t2) _ (ETProdR x) | refl = ap1 ETProdR (t-contr _ (◆erase-t t2 (t2 ◆t) refl) x)

  erase-ert1 : (e : ê) (er : ė) → (x : e ◆e == er) → (erase-e◆ (◆erase-e e er x)) == x
  erase-ert1 ▹ x ◃ .x refl = refl
  erase-ert1 (e ·:₁ x) .((e ◆e) ·: x) refl with erase-e◆ (◆erase-e e (e ◆e) refl)
  erase-ert1 (e ·:₁ x) .((e ◆e) ·: x) refl | refl = refl
  erase-ert1 (x ·:₂ t) .(x ·: (t ◆t)) refl =  ap1 (λ a → ap1 (_·:_ x) a) (erase-trt1 t _ refl)
  erase-ert1 (·λ x e) .(·λ x (e ◆e)) refl = ap1 (λ a → ap1 (·λ x) a) (erase-ert1 e _ refl)
  erase-ert1 (e ∘₁ x) .((e ◆e) ∘ x) refl =  ap1 (λ a → ap1 (λ x₁ → x₁ ∘ x) a) (erase-ert1 e _ refl)
  erase-ert1 (x ∘₂ e) .(x ∘ (e ◆e)) refl = ap1 (λ a → ap1 (_∘_ x) a) (erase-ert1 e _ refl)
  erase-ert1 (e ·+₁ x) .((e ◆e) ·+ x) refl = ap1 (λ a → ap1 (λ x₁ → x₁ ·+ x) a) (erase-ert1 e _ refl)
  erase-ert1 (x ·+₂ e) .(x ·+ (e ◆e)) refl = ap1 (λ a → ap1 (_·+_ x) a) (erase-ert1 e _ refl)
  erase-ert1 ⦇⌜ e ⌟⦈ .(⦇⌜ e ◆e ⌟⦈) refl = ap1 (λ a → ap1 ⦇⌜_⌟⦈ a) (erase-ert1 e _ refl)
  erase-ert1 (inl x) .(inl (x ◆e)) refl = ap1 (λ a → ap1 inl a) (erase-ert1 x _ refl)
  erase-ert1 (inr x) .(inr (x ◆e)) refl = ap1 (λ a → ap1 inr a) (erase-ert1 x _ refl)
  erase-ert1 (case₁ x x₁ x₂ x₃ x₄) .(case (x ◆e) x₁ x₂ x₃ x₄) refl = ap1 (ap1 (λ a → case a x₁ x₂ x₃ x₄)) (erase-ert1 x _ refl)
  erase-ert1 (case₂ x x₁ x₂ x₃ x₄) .(case x x₁ (x₂ ◆e) x₃ x₄) refl = ap1 (ap1 (λ a → case x x₁ a x₃ x₄)) (erase-ert1 x₂ _ refl)
  erase-ert1 (case₃ x x₁ x₂ x₃ x₄) .(case x x₁ x₂ x₃ (x₄ ◆e)) refl = ap1 (ap1 (λ a → case x x₁ x₂ x₃ a)) (erase-ert1 x₄ _ refl)
  erase-ert1 ⟨ e , x ⟩₁ .(⟨ (e ◆e) , x ⟩) refl = ap1 (λ a → ap1 (λ x₁ → ⟨ x₁ , x ⟩) a) (erase-ert1 e _ refl)
  erase-ert1 ⟨ x , e ⟩₂ .(⟨ x , (e ◆e) ⟩) refl = ap1 (λ a → ap1 (⟨_,_⟩ x) a) (erase-ert1 e _ refl)
  
  erase-ert2 : (e : ê) (er : ė) → (b : erase-e e er) → ◆erase-e e er (erase-e◆ b) == b
  erase-ert2 .(▹ er ◃) er EETop = refl
  erase-ert2 (e ·:₁ x) _ (EEAscL b) with erase-e◆ b
  erase-ert2 (e ·:₁ x) _ (EEAscL b) | refl = ap1 EEAscL (e-contr _ (◆erase-e e (e ◆e) refl) b)
  erase-ert2 (e ·:₂ x) _ (EEAscR b) with erase-t◆ b
  erase-ert2 (e ·:₂ x) .(e ·: (x ◆t)) (EEAscR b) | refl = ap1 EEAscR (t-contr _ (◆erase-t x (x ◆t) refl) b)
  erase-ert2 (·λ x e) _ (EELam b) with erase-e◆ b
  erase-ert2 (·λ x e) .(·λ x (e ◆e)) (EELam b) | refl = ap1 EELam (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 (e ∘₁ x) _ (EEApL b) with erase-e◆ b
  erase-ert2 (e ∘₁ x) .((e ◆e) ∘ x) (EEApL b) | refl = ap1 EEApL (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 (e1 ∘₂ e) _ (EEApR b) with erase-e◆ b
  erase-ert2 (e1 ∘₂ e) .(e1 ∘ (e ◆e)) (EEApR b) | refl = ap1 EEApR (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 (e ·+₁ x) _ (EEPlusL b) with erase-e◆ b
  erase-ert2 (e ·+₁ x) .((e ◆e) ·+ x) (EEPlusL b) | refl = ap1 EEPlusL (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 (e1 ·+₂ e) _ (EEPlusR b) with erase-e◆ b
  erase-ert2 (e1 ·+₂ e) .(e1 ·+ (e ◆e)) (EEPlusR b) | refl = ap1 EEPlusR (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 ⦇⌜ e ⌟⦈ _ (EENEHole b) with erase-e◆ b
  erase-ert2 ⦇⌜ e ⌟⦈ .(⦇⌜ e ◆e ⌟⦈) (EENEHole b) | refl = ap1 EENEHole (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 (inl x) _ (EEInl z) with erase-e◆ z
  erase-ert2 (inl x) .(inl (x ◆e)) (EEInl z) | refl = ap1 EEInl (e-contr x _ z)
  erase-ert2 (inr x) _ (EEInr z) with erase-e◆ z
  erase-ert2 (inr x) .(inr (x ◆e)) (EEInr z) | refl = ap1 EEInr (e-contr x _ z)
  erase-ert2 (case₁ x x₁ x₂ x₃ x₄) _ (EECase1 z) with erase-e◆ z
  erase-ert2 (case₁ x x₁ x₂ x₃ x₄) .(case (x ◆e) x₁ x₂ x₃ x₄) (EECase1 z) | refl = ap1 EECase1 (e-contr x _ z)
  erase-ert2 (case₂ e x₁ x₂ x₃ x₄) _ (EECase2 z) with erase-e◆ z
  erase-ert2 (case₂ e x₁ x₂ x₃ x₄) .(case e x₁ (x₂ ◆e) x₃ x₄) (EECase2 z) | refl = ap1 EECase2 (e-contr x₂ _ z)
  erase-ert2 (case₃ e x₁ x₂ x₃ x₄) _ (EECase3 z) with erase-e◆ z
  erase-ert2 (case₃ e x₁ x₂ x₃ x₄) .(case e x₁ x₂ x₃ (x₄ ◆e)) (EECase3 z) | refl = ap1 EECase3 (e-contr x₄ _ z)
  erase-ert2 ⟨ e , x ⟩₁ _ (EEProdL b) with erase-e◆ b
  erase-ert2 ⟨ e , x ⟩₁ .(⟨ (e ◆e) , x ⟩) (EEProdL b) | refl = ap1 EEProdL (e-contr e (◆erase-e e (e ◆e) refl) b)
  erase-ert2 ⟨ e1 , e ⟩₂ _ (EEProdR b) with erase-e◆ b
  erase-ert2 ⟨ e1 , e ⟩₂ .(⟨ e1 , (e ◆e) ⟩) (EEProdR b) | refl = ap1 EEProdR (e-contr e (◆erase-e e (e ◆e) refl) b)
  
  -- since both round trips are stable, these functions demonstrate
  -- isomorphisms between the jugemental and non-judgemental definitions of
  -- erasure
  erase-e-iso : (e : ê) (er : ė) → (e ◆e == er) ≃ (erase-e e er)
  erase-e-iso e er = (◆erase-e e er) , (erase-e◆ , erase-ert1 e er , erase-ert2 e er)

  erase-t-iso : (t : τ̂) (tr : τ̇) → (t ◆t == tr) ≃ (erase-t t tr)
  erase-t-iso t tr = (◆erase-t t tr) , (erase-t◆ , erase-trt1 t tr , erase-trt2 t tr)

  -- this isomorphism supplies the argument that the judgement has mode (∀,
  -- !∃), where uniqueness comes from erase-e◆.
  erase-e-mode : (e : ê) → Σ[ er ∈ ė ] (erase-e e er)
  erase-e-mode e = (e ◆e) , (◆erase-e e (e ◆e) refl)

  -- some translations and lemmas to move between the different
  -- forms. these are not needed to show that this is an ok encoding pair,
  -- but they are helpful when actually using it.

  -- even more specifically, the relation relates an expression to its
  -- functional erasure.
  rel◆t : (t : τ̂) → (erase-t t (t ◆t))
  rel◆t t = ◆erase-t t (t ◆t) refl

  rel◆ : (e : ê) → (erase-e e (e ◆e))
  rel◆ e = ◆erase-e e (e ◆e) refl

  lem-erase-synth : ∀{e e' Γ t} → erase-e e e' → Γ ⊢ e' => t → Γ ⊢ (e ◆e) => t
  lem-erase-synth er wt = tr (λ x → _ ⊢ x => _) (! (erase-e◆ er)) wt

  lem-erase-ana : ∀{e e' Γ t} → erase-e e e' → Γ ⊢ e' <= t → Γ ⊢ (e ◆e) <= t
  lem-erase-ana er wt = tr (λ x → _ ⊢ x <= _) (! (erase-e◆ er)) wt

  lem-synth-erase : ∀{Γ e t e' } → Γ ⊢ e ◆e => t → erase-e e e' → Γ ⊢ e' => t
  lem-synth-erase d1 d2 with erase-e◆ d2
  ... | refl = d1

  eraset-det : ∀{t t' t''} → erase-t t t' → erase-t t t'' → t' == t''
  eraset-det e1 e2 with erase-t◆ e1
  ... | refl = erase-t◆ e2

  erasee-det : ∀{e e' e''} → erase-e e e' → erase-e e e'' → e' == e''
  erasee-det e1 e2 with erase-e◆ e1
  ... | refl = erase-e◆ e2

  erase-in-hole : ∀ {e e'} → erase-e e e' → erase-e ⦇⌜ e ⌟⦈ ⦇⌜ e' ⌟⦈
  erase-in-hole (EENEHole er) = EENEHole (erase-in-hole er)
  erase-in-hole x = EENEHole x

  eq-er-trans : ∀{e e◆ e'} →
                    (e ◆e) == (e' ◆e) →
                    erase-e e e◆ →
                    erase-e e' e◆
  eq-er-trans {e} {e◆} {e'} eq er = tr (λ f → erase-e e' f) (erasee-det (◆erase-e e (e' ◆e) eq) er) (rel◆ e')

  eq-ert-trans : ∀{t t' t1 t2} →
                (t ◆t) == (t' ◆t) →
                erase-t t t1 →
                erase-t t' t2 →
                t1 == t2
  eq-ert-trans eq er1 er2 = ! (erase-t◆ er1) · (eq · (erase-t◆ er2))

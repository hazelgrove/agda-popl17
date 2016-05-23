open import Nat
open import Prelude
open import Hazelnut-core

-- the obvious small step dynamics for complete expressions.
module Hazelnut-complete-dynamics where
  value : (e : ė) (p : ecomplete e) (t : τ̇) (q : ∅ ⊢ e => t) → Set
  value ._ _ _ (SAsc _) = ⊥
  value ._ _ _ (SVar x) with x
  ... | ()
  value ._ _ _ (SAp _ _) = ⊥
  value ._ _ .num SNum = ⊤
  value ._ _ .num (SPlus _ _) = ⊥
  value .<||> () .<||> SEHole
  value ._ () .<||> (SFHole _)
  value ._ _ .<||> (SApHole _ _) = ⊥

  -- "substitute e1 for x in e2". note that this only works on well typed
  -- terms because of barendrecht's convention. that's a theorem we need to
  -- prove. on non well typed terms, this is not correct.
  [_/_]_ : ė → Nat → ė → ė
  [ e1 / x ] (e2 ·: y)  = ([ e1 / x ] e2) ·: y
  [ e1 / x ] X y with natEQ x y
  ... | Inl p           = e1
  ... | Inr _           = X y
  [ e1 / x ] ·λ y e2    = ·λ y ([ e1 / x ] e2)
  [ e1 / x ] N n        = N n
  [ e1 / x ] (e2 ·+ e3) = ([ e1 / x ] e2) ·+ ([ e1 / x ] e3)
  [ e1 / x ] <||>       = <||>
  [ e1 / x ] <| e2 |>   = <| [ e1 / x ] e2 |>
  [ e1 / x ] (e2 ∘ e3)  = ([ e1 / x ] e2) ∘ ([ e1 / x ] e3)

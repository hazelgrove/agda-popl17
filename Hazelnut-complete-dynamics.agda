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

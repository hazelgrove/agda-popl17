open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks

module future-work where
  -- there is no list of actions that can be preformed in sequence that
  -- renders a complete term from (3 : <||>) 4. this is part of the argu
  ex5 : ∀{Γ e' t'} →
          Σ[ L ∈ List action ]
             ((runsynth Γ (((N 3) ·:₂ ▹ <||> ◃) ∘₁ (N 4)) <||> L e' t')
               × ecomplete (e' ◆e))
          → ⊥
  ex5 (._ , DoRefl , (_ , notcomp ) , _) = notcomp
  ex5 (._ , DoSynth Γ ._ ._ α e' e'' t' t'' L x p1 , p2) = {!!}

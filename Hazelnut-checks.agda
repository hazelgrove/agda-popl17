open import Nat
open import Prelude
open import List
open import Hazelnut-core

module Hazelnut-checks where
  -----------------------------------------------------------------------------

  -- these theorems aren't listed in the draft, but have been discussed
  -- since submission. broadly speaking, they act as sanity checks on the
  -- rules. if these properties can't be proven for any extensions to the
  -- language, then the rules are not good.

  -----------------------------------------------------------------------------

  -- movement doesn't change the term other than moving the focus around.
  moveerase : {e e' : ê} {δ : direction} {t : τ̇} →
            (e + move δ +>e e') →
            (e ◆e) == (e' ◆e)
  moveerase EMAscFirstChild = refl
  moveerase EMAscParent1 = refl
  moveerase EMAscParent2 = refl
  moveerase EMAscNextSib = refl
  moveerase EMAscPrevSib = refl
  moveerase EMLamFirstChild = refl
  moveerase EMLamParent = refl
  moveerase EMPlusFirstChild = refl
  moveerase EMPlusParent1 = refl
  moveerase EMPlusParent2 = refl
  moveerase EMPlusNextSib = refl
  moveerase EMPlusPrevSib = refl
  moveerase EMApFirstChild = refl
  moveerase EMApParent1 = refl
  moveerase EMApParent2 = refl
  moveerase EMApNextSib = refl
  moveerase EMApPrevSib = refl
  moveerase EMFHoleFirstChild = refl
  moveerase EMFHoleParent = refl

  -- describes lists of action whose semantics are composable
  data iterok : Set where

  -- iterates a list of actions that can be composed
  data iterate : iterok → ê → ê → Set where

  --constructability
  mutual
    constructable1 : {Γ : ·ctx} {e : ê} {t : τ̇} →
                     (wt : Γ ⊢ (e ◆e) => t) →
                      Σ[ αs ∈ iterok ]
                        (Σ[ e' ∈ ê ] ((iterate αs (▹ <||> ◃) e') ×
                                       ((e ◆e) == (e' ◆e))))
    constructable1 = {!!}

    constructable2 : {Γ : ·ctx} {e : ê} {t : τ̇} →
                     (wt : Γ ⊢ (e ◆e) <= t) →
                      Σ[ αs ∈ iterok ]
                        (Σ[ e' ∈ ê ] ((iterate αs (▹ <||> ◃) e') ×
                                       ((e ◆e) == (e' ◆e))))
    constructable2 = {!!}

  --reachability
  mutual
    reachable1 : {Γ : ·ctx} {e e' : ê} {t : τ̇}
                 (wt  : Γ ⊢ (e ◆e) <= t) →
                 (wt' : Γ ⊢ (e' ◆e) <= t) →
                 (p : (e ◆e) == (e' ◆e)) →
                 Σ[ αs ∈ iterok ] (iterate αs e e')
    reachable1 = {!!}

    reachable2 : {Γ : ·ctx} {e e' : ê} {t : τ̇}
                 (wt  : Γ ⊢ (e ◆e) => t) →
                 (wt' : Γ ⊢ (e' ◆e) => t) →
                 (p : (e ◆e) == (e' ◆e)) →
                 Σ[ αs ∈ iterok ] (iterate αs e e')
    reachable2 = {!!}

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

  iter : List action → ê → ê
  iter = {!!}

  -- there exists a sequence of actions that builds any W.T. e from <||>
  mutual
    constructable : {e : ê} {t : τ̇} →
                    (wt : ∅ ⊢ (e ◆e) <= t) →
                    Σ[ αs ∈ List action ] (iter αs (▹ <||> ◃) == e)
    constructable = {!!}

  -- there exists a sequence of movements that transforms any term into any
  -- other that diff ers only in focus.
  mutual
    reachable : {e e' : ê} {t : τ̇}
                (wt  : ∅ ⊢ (e ◆e) <= t) →
                (wt' : ∅ ⊢ (e' ◆e) <= t) →
                (p : (e ◆e) == (e' ◆e)) →
                Σ[ αs ∈ List action ] (iter αs e == e')
    reachable wt wt' p = {!!}

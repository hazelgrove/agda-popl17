open import Nat
open import Prelude
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

  -- there exists a sequence of actions that builds any W.T. e from <||>
  constructable : Set
  constructable = ⊤

  -- there exists a sequence of actions that transforms any term into any
  -- other that differs only in focus.
  reachable : Set
  reachable = ⊤

  -- iter : List action → ê → ê
  -- iter [] e = e
  -- iter (move x :: l) e = {!!}
  -- iter (del :: l) e = {!!}
  -- iter (construct x :: l) e = {!!}
  -- iter (finish :: l) e = {!!}

  -- reachable : (e1 e2 : ê) (t : {!!}) (same : (e1 ◆e) == (e2 ◆e)) →
  --              Σ[ αs ∈ List action ] (iter αs e1 == e2)
  -- reachable = {!!}

  -- constructable : (e : ê)

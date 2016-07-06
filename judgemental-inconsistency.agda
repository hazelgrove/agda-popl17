open import Nat
open import Prelude
open import core

module judgemental-inconsistency where
  data inconsistent : τ̇ → τ̇ → Set where
    ICR

  to~̸ : (t1 t2 : τ̇) → inconsistent t1 t2 → t1 ~̸ t2
  to~̸ t1 t2 = {!!}

  from~̸ : (t1 t2 : τ̇) → t1 ~̸ t2 → inconsistent t1 t2
  from~̸ t1 t2 = {!!}

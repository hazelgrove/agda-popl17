open import List
open import Nat
open import Prelude

module Hazelnut where
  data τ : Set where
    arr : τ → τ
    num : τ

  data ·τ : Set where
    t : τ → ·τ
    < : ·τ

  ctx : Set
  ctx = List (Nat × τ)

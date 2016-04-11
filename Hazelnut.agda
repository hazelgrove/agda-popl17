open import List
open import Nat
open import Prelude

module Hazelnut where
  -- types
  data ·τ : Set where
    num  : ·τ
    <||> : ·τ
    _to_ : ·τ → ·τ → ·τ

  -- those types without holes anywhere, the so-called complete types
  τ : ·τ → Set
  τ num = ⊤
  τ <||> = ⊥
  τ (t1 to t2) = τ t1 × τ t2

  -- expressions, prefixed with a · to distinguish name clashes with agda
  -- built-ins
  data ·e : Set where
    _·:_  : ·e → ·τ → ·e
    X     : Nat → ·e
    ·λ    : Nat → ·e → ·e
    N     : Nat → ·e
    _·+_  : ·e → ·e → ·e
    <||>  : ·e
    <|_|> : ·e → ·e

  -- similarly to the complete types, the complete expressions
  e : ·e → Set
  e (e1 ·: _) = e e1
  e (X _) = ⊤
  e (·λ _ e1) = e e1
  e (N x) = ⊤
  e (e1 ·+ e2) = e e1 × e e2
  e <||> = ⊥
  e <| e1 |> = e e1

  -- variables are named with naturals in ·e, so we represent contexts
  -- simply as lists of pairs of variable names and types
  ·ctx : Set
  ·ctx = List (Nat × ·τ)

  mutual
    data _⊢_=>_ : ·ctx → ·e → ·τ → Set where
    data _⊢_<=_ : ·ctx → ·e → ·τ → Set where

open import List
open import Nat
open import Prelude

module Hazelnut where
  -- types
  data ·τ : Set where
    num  : ·τ
    <||> : ·τ
    _==>_ : ·τ → ·τ → ·τ

  -- those types without holes anywhere, the so-called complete types
  τ : ·τ → Set
  τ num = ⊤
  τ <||> = ⊥
  τ (t1 ==> t2) = τ t1 × τ t2

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
    _∘_   : ·e → ·e → ·e

  -- similarly to the complete types, the complete expressions
  e : ·e → Set
  e (e1 ·: _) = e e1
  e (X _) = ⊤
  e (·λ _ e1) = e e1
  e (N x) = ⊤
  e (e1 ·+ e2) = e e1 × e e2
  e <||> = ⊥
  e <| e1 |> = e e1
  e (e1 ∘ e2) = e e1 × e e2

  -- variables are named with naturals in ·e, so we represent contexts
  -- simply as lists of pairs of variable names and types
  ·ctx : Set
  ·ctx = List (Nat × ·τ)

  -- this is just to be cute
  _,,_ : {A : Set} → List A → A → List A
  L ,, x = x :: L


  mutual
    -- synthesis
    data _⊢_=>_ : ·ctx → ·e → ·τ → Set where
      SAsc : {Γ : ·ctx} {e : ·e} {t : ·τ} →
                (Γ ⊢ e <= t) →
                Γ ⊢ (e ·: t) => t
      SVar : {Γ : ·ctx} {e : ·e} {t : ·τ} {n : Nat} →
                ((n , t) ∈ Γ) →
                Γ ⊢ X n => t


    -- analysis
    data _⊢_<=_ : ·ctx → ·e → ·τ → Set where
      ASubsume : {Γ : ·ctx} {e : ·e} {t t' : ·τ} →
                    (Γ ⊢ e => t') →
                    (t == t') → -- TODO: no clue if this is right
                    (Γ ⊢ e <= t)
      ALam : {Γ : ·ctx} {e : ·e} {t1 t2 : ·τ} {n : Nat} →
                    (Γ ,, (n , t1)) ⊢ e <= t2 →
                    Γ ⊢ (·λ n e) <= (t1 ==> t2)

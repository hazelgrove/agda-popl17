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

  -- type compatability.
  data _~_ : ·τ → ·τ → Set where
    TCNum : num ~ num
    TCHole : {t : ·τ} → t ~ <||>
    TCTo : {t1 t2 t1' t2' : ·τ} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')
    TCSym : {t1 t2 : ·τ} → t1 ~ t2 → t2 ~ t1

  mutual
    -- synthesis
    data _⊢_=>_ : ·ctx → ·e → ·τ → Set where
      SAsc : {Γ : ·ctx} {e : ·e} {t : ·τ} →
                (Γ ⊢ e <= t) →
                Γ ⊢ (e ·: t) => t
      SVar : {Γ : ·ctx} {e : ·e} {t : ·τ} {n : Nat} →
                ((n , t) ∈ Γ) →
                Γ ⊢ X n => t
      SAp  : {Γ : ·ctx} {e1 e2 : ·e} {t t2 : ·τ} →
                Γ ⊢ e1 => (t2 ==> t) →
                Γ ⊢ e2 <= t2 →
                Γ ⊢ (e1 ∘ e2) => t
      SNum :  {Γ : ·ctx} {n : Nat} →
                Γ ⊢ N n => num
      SPlus : {Γ : ·ctx} {e1 e2 : ·e}  →
                Γ ⊢ e1 <= num →
                Γ ⊢ e2 <= num →
                Γ ⊢ (e1 ·+ e2) => num
      SEHole : {Γ : ·ctx} → Γ ⊢ <||> => <||>
      SFHole : {Γ : ·ctx} {e : ·e} {t : ·τ} →
                  Γ ⊢ e => t →
                  Γ ⊢ <| e |> => <||>
      SApHole : {Γ : ·ctx} {e1 e2 : ·e} →
                Γ ⊢ e1 => <||> →
                Γ ⊢ e2 <= <||> →
                Γ ⊢ (e1 ∘ e2) => <||>

    -- analysis
    data _⊢_<=_ : ·ctx → ·e → ·τ → Set where
      ASubsume : {Γ : ·ctx} {e : ·e} {t t' : ·τ} →
                    (t ~ t') →
                    (Γ ⊢ e => t') →
                    (Γ ⊢ e <= t)
      ALam : {Γ : ·ctx} {e : ·e} {t1 t2 : ·τ} {n : Nat} →
                    (Γ ,, (n , t1)) ⊢ e <= t2 →
                    Γ ⊢ (·λ n e) <= (t1 ==> t2)

    -- todo: how to make hats
    data hatτ : Set where
      ▹_◃  : ·τ → hatτ -- slash t 2 and 6
      _==>₁_ : hatτ → ·τ → hatτ
      _==>₂_ : ·τ → hatτ → hatτ

    data hate : Set where
      ▹_◃   : ·e → hate -- slash t 2 and 6
      _·:₁_ : hate → ·τ → hate
      _·:₂_ : ·e → hatτ → hate
      ·λ    : Nat → hate → hate
      _∘₁_  : hate → ·e → hate
      _∘₂_  : ·e → hate → hate
      _·+₁_ : hate → ·e → hate
      _·+₂_ : ·e → hate → hate
      <|_|> : hate → hate

    --focus erasure
    _◆t : hatτ → ·τ
    ▹ t ◃ ◆t = t
    (t1 ==>₁ t2) ◆t = (t1 ◆t) ==> t2
    (t1 ==>₂ t2) ◆t = t1 ==> (t2 ◆t)

    _◆e : hate → ·e
    ▹ x ◃ ◆e       = x
    (e ·:₁ t) ◆e   = (e ◆e) ·: t
    (e ·:₂ t) ◆e   = e ·: (t ◆t)
    ·λ x e ◆e      = ·λ x (e ◆e)
    (e1 ∘₁ e2) ◆e  = (e1 ◆e) ∘ e2
    (e1 ∘₂ e2) ◆e  = e1 ∘ (e2 ◆e)
    (e1 ·+₁ e2) ◆e = (e1 ◆e) ·+ e2
    (e1 ·+₂ e2) ◆e = e1 ·+ (e2 ◆e)
    <| e |> ◆e     = <| e ◆e |>

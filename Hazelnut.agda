open import List
open import Nat
open import Prelude

module Hazelnut where
  -- types
  data τ̇ : Set where
    num  : τ̇
    <||> : τ̇
    _==>_ : τ̇ → τ̇ → τ̇

  -- those types without holes anywhere
  tcomplete : τ̇ → Set
  tcomplete num = ⊤
  tcomplete <||> = ⊥
  tcomplete (t1 ==> t2) = (tcomplete t1) × (tcomplete t2)

  -- expressions, prefixed with a · to distinguish name clashes with agda
  -- built-ins
  data ė : Set where
    _·:_  : ė → τ̇ → ė
    X     : Nat → ė
    ·λ    : Nat → ė → ė
    N     : Nat → ė
    _·+_  : ė → ė → ė
    <||>  : ė
    <|_|> : ė → ė
    _∘_   : ė → ė → ė

  -- similarly to the complete types, the complete expressions
  ecomplete : ė → Set
  ecomplete (e1 ·: _) = ecomplete e1
  ecomplete (X _) = ⊤
  ecomplete (·λ _ e1) = ecomplete e1
  ecomplete (N x) = ⊤
  ecomplete (e1 ·+ e2) = ecomplete e1 × ecomplete e2
  ecomplete <||> = ⊥
  ecomplete <| e1 |> = ecomplete e1
  ecomplete (e1 ∘ e2) = ecomplete e1 × ecomplete e2

  -- variables are named with naturals in ė, so we represent contexts
  -- simply as lists of pairs of variable names and types
  ·ctx : Set
  ·ctx = List (Nat × τ̇)

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : Nat → ·ctx → Set
  x # [] = ⊤
  x # (v , _) :: Γ with nateq x v
  ... | Inl <> = ⊥
  ... | Inr <> = x # Γ

  -- this is syntax for cons to make the rules look nicer below
  _,,_ : {A : Set} → List A → A → List A
  L ,, x = x :: L

  -- type compatability.
  data _~_ : τ̇ → τ̇ → Set where
    TCNum : num ~ num
    TCHole : {t : τ̇} → t ~ <||>
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')
    TCSym : {t1 t2 : τ̇} → t1 ~ t2 → t2 ~ t1

  -- type incompatability; using this encoding rather than explicit
  -- constructors is equivalent to the one in the text but more convenient
  _~̸_ : τ̇ → τ̇ → Set
  t1 ~̸ t2 = (t1 ~ t2) → ⊥

  mutual
    -- synthesis
    data _⊢_=>_ : ·ctx → ė → τ̇ → Set where
      SAsc : {Γ : ·ctx} {e : ė} {t : τ̇} →
                (Γ ⊢ e <= t) →
                Γ ⊢ (e ·: t) => t
      SVar : {Γ : ·ctx} {e : ė} {t : τ̇} {n : Nat} →
                ((n , t) ∈ Γ) →
                Γ ⊢ X n => t
      SAp  : {Γ : ·ctx} {e1 e2 : ė} {t t2 : τ̇} →
                Γ ⊢ e1 => (t2 ==> t) →
                Γ ⊢ e2 <= t2 →
                Γ ⊢ (e1 ∘ e2) => t
      SNum :  {Γ : ·ctx} {n : Nat} →
                Γ ⊢ N n => num
      SPlus : {Γ : ·ctx} {e1 e2 : ė}  →
                Γ ⊢ e1 <= num →
                Γ ⊢ e2 <= num →
                Γ ⊢ (e1 ·+ e2) => num
      SEHole : {Γ : ·ctx} → Γ ⊢ <||> => <||>
      SFHole : {Γ : ·ctx} {e : ė} {t : τ̇} →
                  Γ ⊢ e => t →
                  Γ ⊢ <| e |> => <||>
      SApHole : {Γ : ·ctx} {e1 e2 : ė} →
                Γ ⊢ e1 => <||> →
                Γ ⊢ e2 <= <||> →
                Γ ⊢ (e1 ∘ e2) => <||>

    -- analysis
    data _⊢_<=_ : ·ctx → ė → τ̇ → Set where
      ASubsume : {Γ : ·ctx} {e : ė} {t t' : τ̇} →
                    (t ~ t') →
                    (Γ ⊢ e => t') →
                    (Γ ⊢ e <= t)
      ALam : {Γ : ·ctx} {e : ė} {t1 t2 : τ̇} {n : Nat} →
                -- todo: check that this implements barendregt's convention
                    (n # Γ) →
                    (Γ ,, (n , t1)) ⊢ e <= t2 →
                    Γ ⊢ (·λ n e) <= (t1 ==> t2)

  data τ̂ : Set where
    ▹_◃  : τ̇ → τ̂ -- slash t 2 and 6
    _==>₁_ : τ̂ → τ̇ → τ̂
    _==>₂_ : τ̇ → τ̂ → τ̂

  data ê : Set where
    ▹_◃   : ė → ê -- slash t 2 and 6
    _·:₁_ : ê → τ̇ → ê
    _·:₂_ : ė → τ̂ → ê
    ·λ    : Nat → ê → ê
    _∘₁_  : ê → ė → ê
    _∘₂_  : ė → ê → ê
    _·+₁_ : ê → ė → ê
    _·+₂_ : ė → ê → ê
    <|_|> : ê → ê

  --focus erasure for types
  _◆t : τ̂ → τ̇
  ▹ t ◃ ◆t = t
  (t1 ==>₁ t2) ◆t = (t1 ◆t) ==> t2
  (t1 ==>₂ t2) ◆t = t1 ==> (t2 ◆t)

  --focus erasure for expressions
  _◆e : ê → ė
  ▹ x ◃ ◆e       = x
  (e ·:₁ t) ◆e   = (e ◆e) ·: t
  (e ·:₂ t) ◆e   = e ·: (t ◆t)
  ·λ x e ◆e      = ·λ x (e ◆e)
  (e1 ∘₁ e2) ◆e  = (e1 ◆e) ∘ e2
  (e1 ∘₂ e2) ◆e  = e1 ∘ (e2 ◆e)
  (e1 ·+₁ e2) ◆e = (e1 ◆e) ·+ e2
  (e1 ·+₂ e2) ◆e = e1 ·+ (e2 ◆e)
  <| e |> ◆e     = <| e ◆e |>

  data direction : Set where
    firstChild : direction
    parent : direction
    nextSib : direction
    prevSib : direction

  data shape : Set where
    arr : shape
    num : shape
    asc : shape
    var : Nat → shape
    lam : Nat → shape
    ap  : shape
    arg : shape
    numlit : Nat → shape
    plus : shape

  data action : Set where
    move : direction → action
    del : action
    construct : shape → action
    finish : action

  -- type movement
  data _+_+>_ : τ̂ → action → τ̂ → Set where
    TMFirstChild : {t1 t2 : τ̇} →
               ▹ t1 ==> t2 ◃ + move firstChild +> (▹ t1 ◃ ==>₁ t2)
    TMParent1 : {t1 t2 : τ̇} →
               (▹ t1 ◃ ==>₁ t2) + move parent +> ▹ t1 ==> t2 ◃
    TMParent2 : {t1 t2 : τ̇} →
               (t1 ==>₂ ▹ t2 ◃) + move parent +> ▹ t1 ==> t2 ◃
    TMNextSib : {t1 t2 : τ̇} →
               (▹ t1 ◃ ==>₁ t2) + move nextSib +> (t1 ==>₂ ▹ t2 ◃)
    TMPrevSib : {t1 t2 : τ̇} →
               (t1 ==>₂ ▹ t2 ◃) + move prevSib +> (▹ t1 ◃ ==>₁ t2)

  data _⊢_=>_~_~>_=>_ : ·ctx → ê → τ̇ → action → ê → τ̇ → Set where

  data _⊢_~_~>_⇐_ : ·ctx → ê → action → ê → τ̇ → Set where

  -- theorem 1
  actsense1 : (Γ : ·ctx) (e e' : ê) (t t' : τ̇) (α : action) →
              (Γ ⊢ e => t ~ α ~> e' => t') →
              (Γ ⊢ (e  ◆e) => t) →
              (Γ ⊢ (e' ◆e) => t')
  actsense1 Γ e e1 t t' α D1 D2 = {!!}

  actsense2  : (Γ : ·ctx) (e e' : ê) (t : τ̇) (α : action) →
                (Γ ⊢ e ~ α ~> e' ⇐ t) →
                (Γ ⊢ (e ◆e) <= t) →
                (Γ ⊢ (e' ◆e) <= t)
  actsense2 Γ e e' t α D1 D2 = {!!}

  -- theorem 2
  actdet1 : (Γ : ·ctx) (e e' e'' : ê) (t t' t'' : τ̇) (α : action) →
            (Γ ⊢ (e ◆e) => t) →
            (Γ ⊢ e => t ~ α ~> e'  => t') →
            (Γ ⊢ e => t ~ α ~> e'' => t'') →
            (e' == e'' × t' == t'') -- todo: maybe 1a and 1b?
  actdet1 Γ e e' e'' t t' t'' α D1 D2 D3 = {!!}

  actdet2 : (Γ : ·ctx) (e e' e'' : ê) (t t' : τ̇) (α : action) →
             (Γ ⊢ (e ◆e) => t) →
             (Γ ⊢ e => t ~ α ~> e' => t') →
             (t ~ t') →
             ((Γ ⊢ e ~ α ~> e'' ⇐ t) + (Γ ⊢ e ~ α ~> e'' ⇐ t')) →
             (e' == e'')
  actdet2 Γ e e' e'' t t' α D1 D2 D3 D45 = {!D3!}

  actdet3 : (Γ : ·ctx) (e e' e'' : ê) (t : τ̇) (α : action) →
            (Γ ⊢ (e ◆e) <= t) →
            (Γ ⊢ e ~ α ~> e' ⇐ t) →
            (Γ ⊢ e ~ α ~> e'' ⇐ t) →
            (e' == e'')
  actdet3 Γ e e' e'' t α D1 D2 D3 = {!!}

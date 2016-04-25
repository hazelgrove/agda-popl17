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
  tcomplete num         = ⊤
  tcomplete <||>        = ⊥
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
  ecomplete (e1 ·: t)  = ecomplete e1 × tcomplete t
  ecomplete (X _)      = ⊤
  ecomplete (·λ _ e1)  = ecomplete e1
  ecomplete (N x)      = ⊤
  ecomplete (e1 ·+ e2) = ecomplete e1 × ecomplete e2
  ecomplete <||>       = ⊥
  ecomplete <| e1 |>   = ⊥
  ecomplete (e1 ∘ e2)  = ecomplete e1 × ecomplete e2

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
                -- todo: double check that this correctly implements
                -- barendregt's convention
                    (n # Γ) →
                    (Γ ,, (n , t1)) ⊢ e <= t2 →
                    Γ ⊢ (·λ n e) <= (t1 ==> t2)

  -- the zippered form of types
  data τ̂ : Set where
    ▹_◃  : τ̇ → τ̂
    _==>₁_ : τ̂ → τ̇ → τ̂
    _==>₂_ : τ̇ → τ̂ → τ̂

  -- the zippered form of expressions
  data ê : Set where
    ▹_◃   : ė → ê
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
  ▹ t ◃ ◆t =  t
  (t1 ==>₁ t2) ◆t = (t1 ◆t) ==> t2
  (t1 ==>₂ t2) ◆t = t1 ==> (t2 ◆t)

  --focus erasure for expressions
  _◆e : ê → ė
  ▹ x ◃ ◆e       = x
  (e ·:₁ t) ◆e   = (e ◆e) ·: t
  (e ·:₂ t) ◆e   = e      ·: (t ◆t)
  ·λ x e ◆e      = ·λ x (e ◆e)
  (e1 ∘₁ e2) ◆e  = (e1 ◆e) ∘ e2
  (e1 ∘₂ e2) ◆e  = e1      ∘ (e2 ◆e)
  (e1 ·+₁ e2) ◆e = (e1 ◆e) ·+ e2
  (e1 ·+₂ e2) ◆e = e1      ·+ (e2 ◆e)
  <| e |> ◆e     = <| e ◆e |>

  -- the three grammars that define actions
  data direction : Set where
    firstChild : direction
    parent : direction
    nextSib : direction
    prevSib : direction

  data shape : Set where
    arrow : shape
    num   : shape
    asc   : shape
    var   : Nat → shape
    lam   : Nat → shape
    ap    : shape
    arg   : shape
    numlit : Nat → shape
    plus  : shape

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
    TMDel     : {t : τ̇} →
                (▹ t ◃) + del +> (▹ <||> ◃)
    TMConArr  : {t : τ̇} →
                (▹ t ◃) + construct arrow +> (t ==>₂ ▹ <||> ◃)
    TMConNum  : (▹ <||> ◃) + construct num +> (▹ num ◃)
    TMZip1 : {t1 t1' : τ̂} {t2 : τ̇} {α : action} →
                (t1 + α +> t1') →
                ((t1 ==>₁ t2) + α +> (t1' ==>₁ t2))
    TMZip2 : {t2 t2' : τ̂} {t1 : τ̇} {α : action} →
                (t2 + α +> t2') →
                ((t1 ==>₂ t2) + α +> (t1 ==>₂ t2'))


  -- expression movement

  -- this describes when two 2-ary constructors in zexps describe halves of
  -- the same hexp
  cohere : (e1 e2 : ė) → (ê → ė → ê) → (ė → ê → ê) → (ė → ė → ė) → Set
  cohere e1 e2 _Cl_ _Cr_ _C_ =
         ((▹ e1 ◃ Cl e2) ◆e == (e1 C e2)) ×
         ((e1 Cr ▹ e2 ◃) ◆e == (e1 C e2))
           -- todo: this is kind of wrong; that e1 and e2 is kind of a red
           -- herring. maybe Matched, below, is better?


  data Matched : (ê → ė → ê) →  (ė → ê → ê) → (ė → ė → ė) → Set where
    Match+ : Matched _·+₁_ _·+₂_ _·+_
    Match∘ : Matched _∘₁_  _∘₂_  _∘_

  -- todo: want this action to be direction, since they're all move?
  data _+_+>e_ : ê → action → ê → Set where
    -- rules for ascriptions
    EMAscFirstChild : {e : ė} {t : τ̇} →
              (▹ e ·: t ◃) + move firstChild +>e (▹ e ◃ ·:₁ t)
    EMAscParent1 : {e : ė} {t : τ̇} →
              (▹ e ◃ ·:₁ t) + move parent +>e (▹ e ·: t ◃)
    EMAscParent2 : {e : ė} {t : τ̇} →
              (e ·:₂ ▹ t ◃) + move parent +>e (▹ e ·: t ◃)
    EMAscNextSib : {e : ė} {t : τ̇} →
              (▹ e ◃ ·:₁ t) + move nextSib +>e (e ·:₂ ▹ t ◃)
    EMAscPrevSib : {e : ė} {t : τ̇} →
              (e ·:₂ ▹ t ◃) + move prevSib +>e (▹ e ◃ ·:₁ t)
    -- rules for lambdas
    EMLamFirstChild : {e : ė} {x : Nat} →
              ▹ (·λ x e) ◃ + move firstChild +>e ·λ x (▹ e ◃)
    EMLamParent : {e : ė} {x : Nat} →
               ·λ x (▹ e ◃) + move parent +>e ▹ (·λ x e) ◃
    -- rules for 2-ary constructors (covers both ap and plus, scales to others)
    EM2aryFirstChild : {e1 e2 : ė}
                    (_Cl_ : ê → ė → ê) →
                    (_Cr_ : ė → ê → ê) →
                    (_C_  : ė → ė → ė) →
                    (m : Matched _Cl_ _Cr_ _C_) → -- todo: which one of these?
                    -- (c : cohere e1 e2 _Cl_ _Cr_ _C_) →
               (▹ e1 C e2 ◃) + move firstChild +>e (▹ e1 ◃ Cl e2)
    EM2aryParent1 : {e1 e2 : ė}
                    (_Cl_ : ê → ė → ê) →
                    (_Cr_ : ė → ê → ê) →
                    (_C_  : ė → ė → ė) →
                    (c : cohere e1 e2 _Cl_ _Cr_  _C_) →
               (▹ e1 ◃ Cl e2) + move parent +>e (▹ e1 C e2 ◃)
    EM2aryParent2 : {e1 e2 : ė}
                    (_Cl_ : ê → ė → ê) →
                    (_Cr_ : ė → ê → ê) →
                    (_C_  : ė → ė → ė) →
                    (c : cohere e1 e2 _Cl_ _Cr_  _C_) →
               (e1 Cr ▹ e2 ◃) + move parent +>e (▹ e1 C e2 ◃)
    EM2aryNextSib : {e1 e2 : ė}
                    (_Cl_ : ê → ė → ê) →
                    (_Cr_ : ė → ê → ê) →
                    (_C_  : ė → ė → ė) →
                    (c : cohere e1 e2 _Cl_ _Cr_  _C_) →
               (▹ e1 ◃ Cl e2) + move nextSib +>e (e1 Cr ▹ e2 ◃)
    EM2aryPrevSib : {e1 e2 : ė}
                    (_Cl_ : ê → ė → ê) →
                    (_Cr_ : ė → ê → ê) →
                    (_C_  : ė → ė → ė) →
                    (c : cohere e1 e2 _Cl_ _Cr_ _C_) →
               (e1 Cr ▹ e2 ◃) + move prevSib +>e (▹ e1 ◃ Cl e2)
    -- rules for non-empty holes
    EMNEHoleFirstChild : {e : ė} →
               (▹ <| e |> ◃) + move firstChild +>e <| ▹ e ◃ |>
    EMNEHoleParent : {e : ė} →
                <| ▹ e ◃ |> + move parent +>e (▹ <| e |> ◃)

  mutual
  -- synthetic action expressions
    data _⊢_=>_~_~>_=>_ : ·ctx → ê → τ̇ → action → ê → τ̇ → Set where
      SAMove : {δ : direction} {e e' : ê} {Γ : ·ctx} {t : τ̇} →
                (e + move δ +>e e') →
                Γ ⊢ e => t ~ move δ ~> e' => t
      SADel : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ ▹ e ◃ => t ~ del ~> ▹ <||> ◃ => <||>
      SAConAsc : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ ▹ e ◃ => t ~ construct asc ~> (e ·:₂ ▹ t ◃ ) => t
      SAConVar : {Γ : ·ctx} {x : Nat} {t : τ̇} →
                (p : (x , t) ∈ Γ) → -- todo: is this right?
                Γ ⊢ ▹ <||> ◃ => <||> ~ construct (var x) ~> ▹ X x ◃ => t
      -- SAConLam : {Γ : ·ctx} {x : Nat} →
      --          -- todo: add a constraint here that x # Γ?
      --          Γ ⊢ ▹ <||> ◃ => <||> ~ construct (lam x) ~> (·λ x <||>) => <||>

    -- analytic action expressions
    data _⊢_~_~>_⇐_ : ·ctx → ê → action → ê → τ̇ → Set where
      AASubsume : {Γ : ·ctx} {e e' : ê} {t t' t'' : τ̇} {α : action} →
                  (Γ ⊢ (e ◆e) => t') →
                  (Γ ⊢ e => t' ~ α ~> e' => t'') →
                  (t ~ t'') →
                  Γ ⊢ e ~ α ~> e' ⇐ t
      AAMove : {e e' : ê} {δ : direction} {Γ : ·ctx} {t : τ̇} →
                  (e + move δ +>e e') →
                  Γ ⊢ e ~ move δ ~> e' ⇐ t
      AADel : {e : ė} {Γ : ·ctx} {t : τ̇} →
                 Γ ⊢ ▹ e ◃ ~ del ~> ▹ <||> ◃ ⇐ t
      AAConAsc : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 Γ ⊢ ▹ e ◃ ~ construct asc ~> (e ·:₂ ▹ t ◃) ⇐ t
      AAConVar : {Γ : ·ctx} {e : ė} {t t' : τ̇} {x : Nat} →
                 (t ~̸ t') →           -- todo: i don't understand this
                 (p : (x , t') ∈ Γ) → -- todo: is this right?
                 Γ ⊢ ▹ <||> ◃ ~ construct (var x) ~> <| ▹ X x ◃ |> ⇐ t
      AAConLam1 : {Γ : ·ctx} {x : Nat} {t1 t2 : τ̇} →
                  Γ ⊢ ▹ <||> ◃ ~ construct (lam x) ~> ·λ x (▹ <||> ◃) ⇐ (t1 ==> t2)
      -- AAConLam2 :
      -- AAConNumlit :
      AAFinish : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 (Γ ⊢ e <= t) →
                 Γ ⊢ ▹ <| e |> ◃ ~ finish ~> ▹ e ◃ ⇐ t
      -- AAZipLam

  -- theorem 1: action sensibility
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

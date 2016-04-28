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

  -- remove possibly multiple copies of a variable from a context
  _/_ : ·ctx → Nat → ·ctx
  [] / x = []
  ((y , t) :: Γ) / x with nateq x y
  ... | Inl <> = Γ / x
  ... | Inr <> = (y , t) :: (Γ / x)

  -- this is syntax for cons to make the rules look nicer below
  _,,_ : {A : Set} → List A → A → List A
  L ,, x = x :: L

  -- type compatability.
  data _~_ : (t1 : τ̇) → (t2 : τ̇) → Set where
    TCRefl : {t : τ̇} → t ~ t
    TCHole1 : {t : τ̇} → t ~ <||>
    TCHole2 : {t : τ̇} → <||> ~ t
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')

  -- type incompatability; using this encoding rather than explicit
  -- constructors is equivalent to the one in the text but more convenient
  _~̸_ : τ̇ → τ̇ → Set
  t1 ~̸ t2 = (t1 ~ t2) → ⊥

  lemsym : (t1 t2 : τ̇) → t1 ~ t2 → t2 ~ t1
  lemsym t1 .t1 TCRefl = TCRefl
  lemsym t1 .<||> TCHole1 = TCHole2
  lemsym .<||> t2 TCHole2 = TCHole1
  lemsym ._ ._ (TCArr p p₁) = TCArr (lemsym _ _ p) (lemsym _ _ p₁)

  lemarr1 : {t1 t2 t3 t4 : τ̇} → (t1 ==> t2) ~ (t3 ==> t4) → (t1 ~ t3 → ⊥) → ⊥
  lemarr1 TCRefl void = void TCRefl
  lemarr1 (TCArr p p₁) void = void p

  lemarr2 : {t1 t2 t3 t4 : τ̇} → (t1 ==> t2) ~ (t3 ==> t4) → (t2 ~ t4 → ⊥) → ⊥
  lemarr2 TCRefl void = void TCRefl
  lemarr2 (TCArr p p₁) void = void p₁

  ~dec : (t1 t2 : τ̇) → ((t1 ~ t2) + (t1 ~̸ t2))
  ~dec num num = Inl TCRefl
  ~dec num <||> = Inl TCHole1
  ~dec num (t2 ==> t3) = Inr (λ ())
  ~dec <||> num = Inl TCHole2
  ~dec <||> <||> = Inl TCRefl
  ~dec <||> (t2 ==> t3) = Inl TCHole2
  ~dec (t1 ==> t2) num = Inr (λ ())
  ~dec (t1 ==> t2) <||> = Inl TCHole1
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl x | Inr y = Inr (λ x₁ → lemarr2 x₁ y)
  ... | Inr x | _ = Inr (λ p → lemarr1 p x)

  ~dec1 : (t1 t2 : τ̇) → (t1 ~ t2) → (t1 ~̸ t2) → ⊥
  ~dec1 t1 .t1 TCRefl pneq = pneq TCRefl
  ~dec1 t1 .<||> TCHole1 pneq = pneq TCHole1
  ~dec1 .<||> t2 TCHole2 pneq = pneq TCHole2
  ~dec1 ._ ._ (TCArr peq peq₁) pneq = pneq (TCArr peq peq₁)

  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
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
    data _⊢_<=_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
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
  data _+_+>_ : (t : τ̂) → (α : action) → (t' : τ̂) → Set where
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

  data Matched : (CL : ê → ė → ê) → (CR : ė → ê → ê) → (C : ė → ė → ė) → Set where
    Match+ : Matched _·+₁_ _·+₂_ _·+_
    Match∘ : Matched _∘₁_  _∘₂_  _∘_

  -- todo: want this action to be direction, since they're all move?
  data _+_+>e_ : (e : ê) → (α : action) → (e' : ê) → Set where
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
    data _⊢_=>_~_~>_=>_ : (Γ : ·ctx) → (e1 : ê) → (t1 : τ̇)
                        → (α : action) → (e2 : ê) → (t2 : τ̇) → Set where
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
      SAConLam : {Γ : ·ctx} {x : Nat} →
               -- todo: add a constraint here that x # Γ?
                Γ ⊢ ▹ <||> ◃ => <||> ~ construct (lam x) ~>
                   ((·λ x <||>) ·:₂ (▹ <||> ◃ ==>₁ <||>)) => (<||> ==> <||>)
      SAConAp1 : {Γ : ·ctx} {t1 t2 : τ̇} {e : ė} →
                Γ ⊢ ▹ e ◃ => (t1 ==> t2) ~ construct ap ~> e ∘₂ ▹ <||> ◃ => t2
      SAConAp2 : {Γ : ·ctx} {e : ė} →
                Γ ⊢ ▹ e ◃ => <||> ~ construct ap ~>  e ∘₂ ▹ <||> ◃ => <||>
      SAConAp3 : {Γ : ·ctx} {t : τ̇} {e : ė} →
                (t ~̸ (<||> ==> <||>)) →
                Γ ⊢ ▹ e ◃ => t ~ construct ap ~> <| e |> ∘₂ ▹ <||> ◃ => <||>
      SAConArg : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ ▹ e ◃ => t ~ construct arg ~> ▹ <||> ◃ ∘₁ e => <||>
      SAConNumlit : {Γ : ·ctx} {e : ė} {n : Nat} →
                Γ ⊢ ▹ <||> ◃ => <||> ~ construct (numlit n) ~> ▹ N n ◃ => num
      -- todo: these ought to look like ap, no? why are there two here and
      -- three there? probably because of the induced type
      -- structure. otherwise i would try to abstract this..
      SAConPlus1 : {Γ : ·ctx} {e : ė} {t : τ̇} →
                (t ~ num) →
                Γ ⊢ ▹ e ◃ => t ~ construct plus ~> e ·+₂ ▹ <||> ◃  => num
      SAConPlus2 : {Γ : ·ctx} {e : ė} {t : τ̇} →
                (t ~̸ num) →
                Γ ⊢ ▹ e ◃ => t ~ construct plus ~> <| e |> ·+₂ ▹ <||> ◃  => num
      SAFinish : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 (Γ ⊢ e => t) →
                 Γ ⊢ ▹ <| e |> ◃ => <||> ~ finish ~> ▹ e ◃ => t
      SAZipAsc1 : {Γ : ·ctx} {e e' : ê} {α : action} {t : τ̇} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  Γ ⊢ (e ·:₁ t) => t ~ α ~> (e' ·:₁ t) => t
      SAZipAsc2 : {Γ : ·ctx} {e : ė} {α : action} {t t' : τ̂} →
                  (t + α +> t') →
                  (Γ ⊢ e <= (t' ◆t)) → -- todo: this rule seems asymmetrical
                  Γ ⊢ (e ·:₂ t) => (t ◆t) ~ α ~> (e ·:₂ t') => (t' ◆t)
      SAZipAp1 : {Γ : ·ctx} {t1 t2 t3 t4 : τ̇} {α : action} {eh eh' : ê} {e : ė} →
                 (Γ ⊢ (eh ◆e) => t2) →
                 (Γ ⊢ eh => t2 ~ α ~> eh' => (t3 ==> t4)) →
                 (Γ ⊢ e <= t3) →
                 Γ ⊢ (eh ∘₁ e) => t1 ~ α ~> (eh' ∘₁ e) => t4
      SAZipAp2 : {Γ : ·ctx} {t1 t2 : τ̇} {α : action} {eh eh' : ê} {e : ė} →
                 (Γ ⊢ (eh ◆e) => t2) →
                 (Γ ⊢ eh => t2 ~ α ~> eh' => <||>) →
                 (Γ ⊢ e <= <||>) →
                 Γ ⊢ (eh ∘₁ e) => t1 ~ α ~> (eh' ∘₁ e) => <||> -- todo: differs from text
      SAZipAp3 : {Γ : ·ctx} {t2 t : τ̇} {e : ė} {eh eh' : ê} {α : action} →
                 (Γ ⊢ e => (t2 ==> t)) →
                 (Γ ⊢ eh ~ α ~> eh' ⇐ t2) →
                 Γ ⊢ (e ∘₂ eh) => t ~ α ~> (e ∘₂ eh') => t
      SAZipAp4 : {Γ : ·ctx} {e : ė} {eh eh' : ê} {α : action} →
                 (Γ ⊢ e => <||>) →
                 (Γ ⊢ eh ~ α ~> eh' ⇐ <||>) →
                 Γ ⊢ (e ∘₂ eh) => <||> ~ α ~> (e ∘₂ eh') => <||>
      SAZipPlus1 : {Γ : ·ctx} {e : ė} {eh eh' : ê} {α : action} →
                   (Γ ⊢ eh ~ α ~> eh' ⇐ num) →
                   Γ ⊢ (eh ·+₁ e) => num ~ α ~> (eh' ·+₁ e) => num
      SAZipPlus2 : {Γ : ·ctx} {e : ė} {eh eh' : ê} {α : action} →
                   (Γ ⊢ eh ~ α ~> eh' ⇐ num) →
                   Γ ⊢ (e ·+₂ eh) => num ~ α ~> (e ·+₂ eh') => num
      SAZipHole1 : {Γ : ·ctx} {e e' : ê} {t t' : τ̇} {α : action} →
                   (Γ ⊢ (e ◆e) => t) →
                   (Γ ⊢ e => t ~ α ~> e' => t') →
                   ((e' == ▹ <||> ◃) → ⊥) → -- todo: *no* idea if this is right. what if it's an η-expanded form?
                   Γ ⊢ <| e |> => <||> ~ α ~>  <| e' |> => <||>
      SAZipHole2 : {Γ : ·ctx} {e : ê} {t : τ̇} {α : action} →
                   (Γ ⊢ (e ◆e) => t) →
                   (Γ ⊢ e => t ~ α ~> ▹ <||> ◃ => <||>) →
                   Γ ⊢ <| e |> => <||> ~ α ~> ▹ <||> ◃ => <||>


    -- analytic action expressions
    data _⊢_~_~>_⇐_ : (Γ : ·ctx) → (e : ê) → (α : action) →
                      (e' : ê) → (t : τ̇) → Set where
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
                  Γ ⊢ ▹ <||> ◃ ~ construct (lam x) ~>
                      ·λ x (▹ <||> ◃) ⇐ (t1 ==> t2)
      AAConLam2 : {Γ : ·ctx} {x : Nat} {t : τ̇} →
                  (t ~̸ (<||> ==> <||>)) →
                  Γ ⊢ ▹ <||> ◃ ~ construct (lam x) ~>
                      <| ·λ x <||> ·:₂ (▹ <||> ◃ ==>₁ <||>) |> ⇐ t
      AAConNumlit : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                    (t ~̸ num) →
                    Γ ⊢ ▹ <||> ◃ ~ construct (numlit n) ~> <| ▹ (N n) ◃ |> ⇐ t
      AAFinish : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 (Γ ⊢ e <= t) →
                 Γ ⊢ ▹ <| e |> ◃ ~ finish ~> ▹ e ◃ ⇐ t
      AAZipLam : {Γ : ·ctx} {x : Nat} {t1 t2 : τ̇} {e e' : ê} {α : action} →
                 ((x , t1) ∈ Γ) → -- todo: check this move
                 (Γ ⊢ e ~ α ~> e' ⇐ t2) →
                 (Γ / x) ⊢ (·λ x e) ~ α ~> (·λ x e') ⇐ (t1 ==> t2)

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

open import Nat
open import Prelude

module Hazelnut where
  -- types
  data τ̇ : Set where
    num  : τ̇
    <||> : τ̇
    _==>_ : τ̇ → τ̇ → τ̇

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

  -- contexts, and some operations on them

  -- variables are named with naturals in ė. therefore we represent
  -- contexts as functions from names for variables (nats) to possible
  -- bindings.
  ·ctx : Set
  ·ctx = Nat → Maybe τ̇ -- todo: (Σ[ n : Nat ] (y : Nat) → y ∈ Γ → x > y)?

  ∅ : ·ctx
  ∅ x = None

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : (n : Nat) → (Γ : ·ctx) → Set
  x # Γ = (Γ x) == None

  -- not sure if this should take a pair
  _∈_ : (p : Nat × τ̇) → (Γ : ·ctx) → Set
  (x , t) ∈ Γ = (Γ x) == Some t

  -- remove possibly multiple copies of a variable from a context
  _/_ : ·ctx → Nat → ·ctx
  (Γ / x) y with natEQ x y
  (Γ / x) .x | Inl refl = None
  (Γ / x) y  | Inr neq  = Γ y

  -- a variable is apart from a context from which it is removed
  aar : (Γ : ·ctx) (x : Nat) → x # (Γ / x)
  aar Γ x with natEQ x x
  aar Γ x | Inl refl = refl
  aar Γ x | Inr x≠x  = abort (x≠x refl)

  -- contexts give only one binding for each variable that they
  -- include. this is needed for unicity.
  ctxunicity : {Γ : ·ctx} {n : Nat} {t t' : τ̇} →
               (n , t) ∈ Γ →
               (n , t') ∈ Γ →
               t == t'
  ctxunicity {n = n} p q with natEQ n n
  ctxunicity p q | Inl refl = someinj (! p · q)
  ctxunicity _ _ | Inr x≠x = abort (x≠x refl)

  -- this adds a new binding to the context, clobbering anything that might
  -- have been there before.
  _,,_ : ·ctx → (Nat × τ̇) → ·ctx
  (Γ ,, (x , t)) y with natEQ x y
  (Γ ,, (x , t)) .x | Inl refl = Some t
  (Γ ,, (x , t)) y  | Inr neq  = Γ y

  -- type compatability
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

  -- theorem: type compatablity is symmetric
  ~sym : {t1 t2 : τ̇} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)

  lemarr1 : {t1 t2 t3 t4 : τ̇} → (t1 ~ t3 → ⊥) → (t1 ==> t2) ~ (t3 ==> t4)  → ⊥
  lemarr1 v TCRefl = v TCRefl
  lemarr1 v (TCArr p _) = v p

  lemarr2 : {t1 t2 t3 t4 : τ̇} → (t2 ~ t4 → ⊥) → (t1 ==> t2) ~ (t3 ==> t4) →  ⊥
  lemarr2 v TCRefl = v TCRefl
  lemarr2 v (TCArr _ p) = v p

  -- theorem: every pair of types is either compatable or not compatable
  ~dec : (t1 t2 : τ̇) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ <||> = Inl TCHole1
  ~dec <||> _ = Inl TCHole2
    -- num cases
  ~dec num num = Inl TCRefl
  ~dec num (t2 ==> t3) = Inr (λ ())
    -- arrow cases
  ~dec (t1 ==> t2) num = Inr (λ ())
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (lemarr2 y)
  ... | Inr x | _     = Inr (lemarr1 x)

  -- theorem: no pair of types is both compatable and not compatable. this
  -- is immediate from our encoding of the ~̸ judgement in the formalism
  -- here; in the mathematics presented in the paper, this would require
  -- induction to relate the two judgements.
  ~apart : {t1 t2 : τ̇} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart v p = v p


  -- type checking for ė
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
      SAsc : {Γ : ·ctx} {e : ė} {t : τ̇} →
                (Γ ⊢ e <= t) →
                Γ ⊢ (e ·: t) => t
      SVar : {Γ : ·ctx} {t : τ̇} {n : Nat} →
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
                    (Γ ⊢ e => t') →
                    (t ~ t') →
                    (Γ ⊢ e <= t)
      ALam : {Γ : ·ctx} {e : ė} {t1 t2 : τ̇} {n : Nat} →
                -- todo: double check that this correctly implements
                -- barendregt's convention
                    (n # Γ) →
                    (Γ ,, (n , t1)) ⊢ e <= t2 →
                    Γ ⊢ (·λ n e) <= (t1 ==> t2)

  -- a small exmaple to demonstrate how the encoding above works
  -- this is the encoding of the function (λx. x + 0).
  fn : ė
  fn = ·λ 0 (X 0 ·+ N 0)

  -- this is the derivation that it has type num ==> num
  ex1 : ∅ ⊢ ·λ 0 (X 0 ·+ N 0) <= (num ==> num)
  ex1 = ALam refl
         (ASubsume
          (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume SNum TCRefl))
          TCRefl)

  -- and the derivation that when applied to a numeric argument it produces
  -- a num.
  ex2 : ∅ ⊢ (fn ·: (num ==> num)) ∘ (N 10) => num
  ex2 = SAp (SAsc ex1) (ASubsume SNum TCRefl)

  -- eta-expanded curried addition
  ex3 : ∅ ⊢ ·λ 0 ( (·λ 1 (X 0 ·+ X 1)) ·: (num ==> num)  )
               <= (num ==> (num ==> num))
  ex3 = ALam refl (ASubsume (SAsc (ALam refl
                                    (ASubsume
                                      (SPlus (ASubsume (SVar refl) TCRefl)
                                             (ASubsume (SVar refl) TCRefl))
                                          TCRefl))) TCRefl)

  -- those types without holes anywhere
  tcomplete : τ̇ → Set
  tcomplete num         = ⊤
  tcomplete <||>        = ⊥
  tcomplete (t1 ==> t2) = (tcomplete t1) × (tcomplete t2)

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

  -- zippered form of types
  data τ̂ : Set where
    ▹_◃  : τ̇ → τ̂
    _==>₁_ : τ̂ → τ̇ → τ̂
    _==>₂_ : τ̇ → τ̂ → τ̂

  -- zippered form of expressions
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

  -- (mapreduce τ̂) (\x → x) ??

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

  -- (mapreduce ê) (\x → x) ??

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
    TMConArrow  : {t : τ̇} →
                (▹ t ◃) + construct arrow +> (t ==>₂ ▹ <||> ◃)
    TMConNum  : (▹ <||> ◃) + construct num +> (▹ num ◃)
    TMZip1 : {t1 t1' : τ̂} {t2 : τ̇} {α : action} →
                (t1 + α +> t1') →
                ((t1 ==>₁ t2) + α +> (t1' ==>₁ t2))
    TMZip2 : {t2 t2' : τ̂} {t1 : τ̇} {α : action} →
                (t2 + α +> t2') →
                ((t1 ==>₂ t2) + α +> (t1 ==>₂ t2'))

  -- expression movement
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
    -- rules for 2-ary constructors
    EMPlusFirstChild : {e1 e2 : ė} →
               (▹ e1 ·+ e2 ◃) + move firstChild +>e (▹ e1 ◃ ·+₁ e2)
    EMPlusParent1 : {e1 e2 : ė} →
               (▹ e1 ◃ ·+₁ e2) + move parent +>e (▹ e1 ·+ e2 ◃)
    EMPlusParent2 : {e1 e2 : ė} →
               (e1 ·+₂ ▹ e2 ◃) + move parent +>e (▹ e1 ·+ e2 ◃)
    EMPlusNextSib : {e1 e2 : ė} →
               (▹ e1 ◃ ·+₁ e2) + move nextSib +>e (e1 ·+₂ ▹ e2 ◃)
    EMPlusPrevSib : {e1 e2 : ė} →
               (e1 ·+₂ ▹ e2 ◃) + move prevSib +>e (▹ e1 ◃ ·+₁ e2)

    EMApFirstChild : {e1 e2 : ė} →
               (▹ e1 ∘ e2 ◃) + move firstChild +>e (▹ e1 ◃ ∘₁ e2)
    EMApParent1 : {e1 e2 : ė} →
               (▹ e1 ◃ ∘₁ e2) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMApParent2 : {e1 e2 : ė} →
               (e1 ∘₂ ▹ e2 ◃) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMApNextSib : {e1 e2 : ė} →
               (▹ e1 ◃ ∘₁ e2) + move nextSib +>e (e1 ∘₂ ▹ e2 ◃)
    EMApPrevSib : {e1 e2 : ė} →
               (e1 ∘₂ ▹ e2 ◃) + move prevSib +>e (▹ e1 ◃ ∘₁ e2)

    -- rules for non-empty holes
    EMFHoleFirstChild : {e : ė} →
               (▹ <| e |> ◃) + move firstChild +>e <| ▹ e ◃ |>
    EMFHoleParent : {e : ė} →
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
               (x # Γ) → -- todo: i added this; it doesn't appear in the text
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
                  (Γ ⊢ e <= (t' ◆t)) → -- todo: this rule seems weirdly asymmetrical
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
                 -- todo: this differs from the text
                 Γ ⊢ (eh ∘₁ e) => t1 ~ α ~> (eh' ∘₁ e) => <||>
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
                   -- todo: *no* idea if this is right. what if it's an
                   -- η-expanded form or something?
                   ((e' == ▹ <||> ◃) → ⊥) →
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
                  (x # Γ) → -- todo: i added this
                  Γ ⊢ ▹ <||> ◃ ~ construct (lam x) ~>
                      ·λ x (▹ <||> ◃) ⇐ (t1 ==> t2)
      AAConLam2 : {Γ : ·ctx} {x : Nat} {t : τ̇} →
                  (x # Γ) → -- todo: i added this
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

  synthmovelem : {Γ : ·ctx} {e e' : ê} {t : τ̇} {δ : direction} →
                 (e + move δ +>e e') →
                 (Γ ⊢ e ◆e => t) →
                 (Γ ⊢ e' ◆e => t)
  synthmovelem EMAscFirstChild d2 = d2
  synthmovelem EMAscParent1 d2 = d2
  synthmovelem EMAscParent2 d2 = d2
  synthmovelem EMAscNextSib d2 = d2
  synthmovelem EMAscPrevSib d2 = d2
  synthmovelem EMLamFirstChild d2 = d2
  synthmovelem EMLamParent d2 = d2
  synthmovelem EMPlusFirstChild d2 = d2
  synthmovelem EMPlusParent1 d2 = d2
  synthmovelem EMPlusParent2 d2 = d2
  synthmovelem EMPlusNextSib d2 = d2
  synthmovelem EMPlusPrevSib d2 = d2
  synthmovelem EMApFirstChild d2 = d2
  synthmovelem EMApParent1 d2 = d2
  synthmovelem EMApParent2 d2 = d2
  synthmovelem EMApNextSib d2 = d2
  synthmovelem EMApPrevSib d2 = d2
  synthmovelem EMFHoleFirstChild d2 = d2
  synthmovelem EMFHoleParent d2 = d2

  -- movements preserve analytic types up to erasure. this lemma seems
  -- silly because all it seems to do in each case is return the second
  -- derivation D. the pattern matching here, though, constrains what that
  -- derivation may be in each case, and is therefore actually
  -- non-trivial. it's just that most of the work is happening in the
  -- implicit arguments.
  anamovelem : {Γ : ·ctx} {δ : direction} {e e' : ê} {t : τ̇}
            (p : e + move δ +>e e') →
            (Γ ⊢ e ◆e <= t) →
            (Γ ⊢ e' ◆e <= t)
  anamovelem EMAscFirstChild d2 = d2
  anamovelem EMAscParent1 d2 = d2
  anamovelem EMAscParent2 d2 = d2
  anamovelem EMAscNextSib d2 = d2
  anamovelem EMAscPrevSib d2 = d2
  anamovelem EMLamFirstChild d2 = d2
  anamovelem EMLamParent d2 = d2
  anamovelem EMPlusFirstChild d2 = d2
  anamovelem EMPlusParent1 d2 = d2
  anamovelem EMPlusParent2 d2 = d2
  anamovelem EMPlusNextSib d2 = d2
  anamovelem EMPlusPrevSib d2 = d2
  anamovelem EMApFirstChild d2 = d2
  anamovelem EMApParent1 d2 = d2
  anamovelem EMApParent2 d2 = d2
  anamovelem EMApNextSib d2 = d2
  anamovelem EMApPrevSib d2 = d2
  anamovelem EMFHoleFirstChild d2 = d2
  anamovelem EMFHoleParent d2 = d2


  -- actions don't change under weakening the context
  weaken : {Γ : ·ctx} {e e' : ê} {t1 t2 : τ̇} {α : action} {x : Nat} →
           ((x , t1) ∈ Γ) →
           (Γ ⊢ e ~ α ~> e' ⇐ t2) →
           (((Γ / x) ,, (x , t1)) ⊢ e ~ α ~> e' ⇐ t2)
  weaken {_} {e} {e'} {t1} {t2} {α} xin =
             tr (λ g → g ⊢ e ~ α ~> e' ⇐ t2) (funext (ctxeq _ _ _ xin))
   where
      -- todo: this is messy and i don't 100% know why it has to be
      lem : (x y : Nat) → (Γ : ·ctx) → (x == y → ⊥) → Γ y == ((Γ / x) y)
      lem x y G neq with natEQ x y
      lem x₂ .x₂ G neq | Inl refl = abort (neq refl)
      lem x₂ y₁ G neq  | Inr x₃ = refl

      ctxeq : (Γ : ·ctx) (t : τ̇) (x : Nat) →
               (x , t) ∈ Γ →
               (y : Nat) → Γ y == ((Γ / x) ,, (x , t)) y
      ctxeq Γ t x xin y with natEQ x y
      ctxeq Γ t x xin .x | Inl refl = xin
      ctxeq Γ t x xin y  | Inr x₁ = lem x y Γ x₁



  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic posititions, just because we think of
  -- the type as an input
  synthunicity : {Γ : ·ctx} {e : ė} {t t' : τ̇} →
                  (Γ ⊢ e => t)
                → (Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp D1 _) (SAp D2 _) with synthunicity D1 D2
  ... | refl = refl
  synthunicity (SAp D1 _) (SApHole D2 _) with synthunicity D1 D2
  ... | ()
  synthunicity SNum SNum = refl
  synthunicity (SPlus _ _ ) (SPlus _ _ ) = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SFHole _) (SFHole _) = refl
  synthunicity (SApHole D1 _) (SAp D2 _) with synthunicity D1 D2
  ... | ()
  synthunicity (SApHole _ _) (SApHole _ _) = refl

  mutual
    -- if an action transforms an zexp in a synthetic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense1 : {Γ : ·ctx} {e e' : ê} {t t' : τ̇} {α : action} →
                (Γ ⊢ e => t ~ α ~> e' => t') →
                (Γ ⊢ (e  ◆e) => t) →
                 Γ ⊢ (e' ◆e) => t'
    actsense1 (SAMove x) D2 = synthmovelem x D2
    actsense1 SADel D2 = SEHole
    actsense1 SAConAsc D2 = SAsc (ASubsume D2 TCRefl)
    actsense1 (SAConVar p) D2 = SVar p
    actsense1 (SAConLam p) D2 = SAsc (ALam p (ASubsume SEHole TCRefl))
    actsense1 SAConAp1 D2 = SAp D2 (ASubsume SEHole TCHole1)
    actsense1 SAConAp2 D2 = SApHole D2 (ASubsume SEHole TCRefl)
    actsense1 (SAConAp3 x) D2 = SApHole (SFHole D2) (ASubsume SEHole TCRefl)
    actsense1 SAConArg D2 = SApHole SEHole (ASubsume D2 TCHole2)
    actsense1 SAConNumlit D2 = SNum
    actsense1 (SAConPlus1 TCRefl) D2 = SPlus (ASubsume D2 TCRefl) (ASubsume SEHole TCHole1)
    actsense1 (SAConPlus1 TCHole2) D2 = SPlus (ASubsume D2 TCHole1) (ASubsume SEHole TCHole1)
    actsense1 (SAConPlus2 x) D2 = SPlus (ASubsume (SFHole D2) TCHole1) (ASubsume SEHole TCHole1)
    actsense1 (SAFinish x) D2 = x
    actsense1 (SAZipAsc1 x) (SAsc D2) = SAsc (actsense2 x D2)
    actsense1 (SAZipAsc2 x x₁) _ = SAsc x₁
    actsense1 (SAZipAp1 x D1 x₁) D2 = SAp (actsense1 D1 x) x₁
    actsense1 (SAZipAp2 x D1 x₁) D2 = SApHole (actsense1 D1 x) x₁
    actsense1 (SAZipAp3 x x₁) (SAp D2 x₃)     with synthunicity x D2
    ... | refl = SAp x (actsense2 x₁ x₃)
    actsense1 (SAZipAp3 x x₁) (SApHole D2 x₂) with synthunicity x D2
    ... | ()
    actsense1 (SAZipAp4 x x₁) (SAp D2 x₂)     with synthunicity x D2
    ... | ()
    actsense1 (SAZipAp4 x x₁) (SApHole D2 x₂)  = SApHole x (actsense2 x₁ x₂)
    actsense1 (SAZipPlus1 x) (SPlus x₁ x₂) = SPlus (actsense2 x x₁) x₂
    actsense1 (SAZipPlus2 x) (SPlus x₁ x₂) = SPlus x₁ (actsense2 x x₂)
    actsense1 (SAZipHole1 x D1 x₁) D2 = SFHole (actsense1 D1 x)
    actsense1 (SAZipHole2 x D1) D2 = SEHole

    -- if an action transforms an zexp in an analytic posistion to another
    -- zexp, they have the same type up erasure of focus.
    actsense2  : {Γ : ·ctx} {e e' : ê} {t : τ̇} {α : action} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  (Γ ⊢ (e ◆e) <= t) →
                  (Γ ⊢ (e' ◆e) <= t)
    actsense2 (AASubsume x act p) D2 = ASubsume (actsense1 act x) p
    actsense2 (AAMove x) D2 = anamovelem x D2
    actsense2 AADel _ = ASubsume SEHole TCHole1
    actsense2 AAConAsc D2 = ASubsume (SAsc D2) TCRefl
    actsense2 (AAConVar x₁ p) D2 = ASubsume (SFHole (SVar p)) TCHole1
    actsense2 (AAConLam1 p) (ASubsume SEHole TCHole1) = ALam p (ASubsume SEHole TCHole1)
    actsense2 (AAConLam2 p n~) (ASubsume SEHole TCRefl) = abort (n~ TCHole2)
    actsense2 (AAConLam2 p x₁) (ASubsume SEHole TCHole1) = ASubsume (SFHole (SAsc (ALam p (ASubsume SEHole TCRefl)))) TCHole1
    actsense2 (AAConLam2 p n~) (ASubsume SEHole TCHole2) = abort (n~ TCHole2)
    actsense2 (AAConNumlit _) _ = ASubsume (SFHole SNum) TCHole1
    actsense2 (AAFinish x) _ = x
    actsense2 (AAZipLam _ _ ) (ASubsume () _)
    actsense2 (AAZipLam x₁ D1) (ALam x₂ D2) = ALam x₂ (actsense2 (weaken x₁ D1) D2)

  -- theorem 2

  -- the same action applied to the same type makes the same resultant
  -- type.
  actdet1 : {t t' t'' : τ̂} {α : action} →
            (t + α +> t') →
            (t + α +> t'') →
            (t' == t'')
  actdet1 TMFirstChild TMFirstChild = refl
  actdet1 TMParent1 TMParent1 = refl
  actdet1 TMParent1 (TMZip1 ())
  actdet1 TMParent2 TMParent2 = refl
  actdet1 TMParent2 (TMZip2 ())
  actdet1 TMNextSib TMNextSib = refl
  actdet1 TMNextSib (TMZip1 ())
  actdet1 TMPrevSib TMPrevSib = refl
  actdet1 TMPrevSib (TMZip2 ())
  actdet1 TMDel TMDel = refl
  actdet1 TMConArrow TMConArrow = refl
  actdet1 TMConNum TMConNum = refl
  actdet1 (TMZip1 ()) TMParent1
  actdet1 (TMZip1 ()) TMNextSib
  actdet1 (TMZip1 p1) (TMZip1 p2) with actdet1 p1 p2
  ... | refl = refl
  actdet1 (TMZip2 ()) TMParent2
  actdet1 (TMZip2 ()) TMPrevSib
  actdet1 (TMZip2 p1) (TMZip2 p2) with actdet1 p1 p2
  ... | refl = refl

  -- all expressions only move to one other expression
  movedet : {e e' e'' : ê} {δ : direction} →
            (e + move δ +>e e') →
            (e + move δ +>e e'') →
            e' == e''
  movedet EMAscFirstChild EMAscFirstChild = refl
  movedet EMAscParent1 EMAscParent1 = refl
  movedet EMAscParent2 EMAscParent2 = refl
  movedet EMAscNextSib EMAscNextSib = refl
  movedet EMAscPrevSib EMAscPrevSib = refl
  movedet EMLamFirstChild EMLamFirstChild = refl
  movedet EMLamParent EMLamParent = refl
  movedet EMPlusFirstChild EMPlusFirstChild = refl
  movedet EMPlusParent1 EMPlusParent1 = refl
  movedet EMPlusParent2 EMPlusParent2 = refl
  movedet EMPlusNextSib EMPlusNextSib = refl
  movedet EMPlusPrevSib EMPlusPrevSib = refl
  movedet EMApFirstChild EMApFirstChild = refl
  movedet EMApParent1 EMApParent1 = refl
  movedet EMApParent2 EMApParent2 = refl
  movedet EMApNextSib EMApNextSib = refl
  movedet EMApPrevSib EMApPrevSib = refl
  movedet EMFHoleFirstChild EMFHoleFirstChild = refl
  movedet EMFHoleParent EMFHoleParent = refl

  mutual
    actdet2 : {Γ : ·ctx} {e e' e'' : ê} {t t' t'' : τ̇} {α : action} →
              (Γ ⊢ (e ◆e) => t) →
              (Γ ⊢ e => t ~ α ~> e'  => t') →
              (Γ ⊢ e => t ~ α ~> e'' => t'') →
              (e' == e'' × t' == t'')
    actdet2 wt d1 d2 = {!!}

    -- a lemma for actdet3. an arrow type given to a hole might as well be
    -- holes itself.
    lem1 : {Γ : ·ctx} {t1 t2 : τ̇} →
           Γ ⊢ <||> <= (t1 ==> t2) →
           (t1 ==> t2) ~ (<||> ==> <||>)
    lem1 (ASubsume SEHole TCHole1) = TCArr TCHole1 TCHole1

    -- actions on analytic expressions produce the same expression
    actdet3 : {Γ : ·ctx} {e e' e'' : ê} {t : τ̇} {α : action} →
              (Γ ⊢ (e ◆e) <= t) →
              (Γ ⊢ e ~ α ~> e' ⇐ t) →
              (Γ ⊢ e ~ α ~> e'' ⇐ t) →
              (e' == e'')
    actdet3 D1 (AASubsume x x₁ x₂) D3 = {!!} -- π1 (actdet2 x x₁ {!D3!})

    actdet3 D1 (AAMove x) (AASubsume x₁ x₂ x₃) = {!x!}
    actdet3 D1 (AAMove x) (AAMove x₁) = movedet x x₁
    actdet3 D1 (AAMove EMLamParent) (AAZipLam x₃ D3) = {!!}

    actdet3 D1 AADel (AASubsume _ SADel _) = refl
    actdet3 D1 AADel AADel = refl

    actdet3 D1 AAConAsc (AASubsume x SAConAsc x₂) = {!x₂!}
    actdet3 D1 AAConAsc AAConAsc = refl

    actdet3 {Γ = G} D1 (AAConVar x₁ p) (AASubsume x₂ (SAConVar p₁) x₄) with ctxunicity {Γ = G} p p₁
    ... | refl = abort (x₁ x₄)
    actdet3 D1 (AAConVar x₁ p) (AAConVar x₂ p₁) = refl

    actdet3 D1 (AAConLam1 x₃) (AASubsume SEHole (SAConLam x₅) x₆) = {!SEHole!}
    actdet3 D1 (AAConLam1 x₁) (AAConLam1 x₂) = refl
    actdet3 D1 (AAConLam1 x₃) (AAConLam2 x₄ x₅) = abort (x₅ (lem1 D1))

    actdet3 D1 (AAConLam2 x₁ x₂) (AASubsume x₃ (SAConLam x₄) x₅) = abort (x₂ x₅)
    actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam1 x₃) = abort (x₂ (lem1 D1))
    actdet3 D1 (AAConLam2 x₁ x₂) (AAConLam2 x₃ x₄) = refl

    actdet3 D1 (AAConNumlit x) (AASubsume x₁ SAConNumlit x₃) = abort (x x₃)
    actdet3 D1 (AAConNumlit x) (AAConNumlit x₁) = refl

    actdet3 D1 (AAFinish x) (AASubsume x₁ (SAFinish x₂) x₃) = refl
    actdet3 D1 (AAFinish x) (AAFinish x₁) = refl

    actdet3 D1 (AAZipLam x₁ D2) D3 = actdet3 D1 {!D2!} D3




  -- these theorems aren't listed in the draft, but have been discussed
  -- since submission.

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

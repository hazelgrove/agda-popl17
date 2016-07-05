open import Nat
open import Prelude

module core where
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

  ---- contexts and some operations on them

  -- variables are named with naturals in ė. therefore we represent
  -- contexts as functions from names for variables (nats) to possible
  -- bindings.
  ·ctx : Set
  ·ctx = Nat → Maybe τ̇

  -- convenient shorthand for the (unique up to fun. ext.) empty context
  ∅ : ·ctx
  ∅ _ = None

  -- add a new binding to the context, clobbering anything that might have
  -- been there before.
  _,,_ : ·ctx → (Nat × τ̇) → ·ctx
  (Γ ,, (x , t)) y with natEQ x y
  (Γ ,, (x , t)) .x | Inl refl = Some t
  (Γ ,, (x , t)) y  | Inr neq  = Γ y

  -- membership, or presence, in a context
  _∈_ : (p : Nat × τ̇) → (Γ : ·ctx) → Set
  (x , t) ∈ Γ = (Γ x) == Some t

  -- apartness for contexts, so that we can follow barendregt's convention
  _#_ : (n : Nat) → (Γ : ·ctx) → Set
  x # Γ = (Γ x) == None

  -- without: remove a variable from a context
  _/_ : ·ctx → Nat → ·ctx
  (Γ / x) y with natEQ x y
  (Γ / x) .x | Inl refl = None
  (Γ / x) y  | Inr neq  = Γ y

  -- the type consistency judgement
  data _~_ : (t1 : τ̇) → (t2 : τ̇) → Set where
    TCRefl : {t : τ̇} → t ~ t
    TCHole1 : {t : τ̇} → t ~ <||>
    TCHole2 : {t : τ̇} → <||> ~ t
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')

  -- type inconsistency. rather than enumerate the types which aren't
  -- consistent, we encode this judgement immediately as the complement of
  -- consistency.
  _~̸_ : τ̇ → τ̇ → Set
  t1 ~̸ t2 = (t1 ~ t2) → ⊥

  --- matching for arrows
  data _▸arr_ : τ̇ → τ̇ → Set where
    MAHole :                  <||>     ▸arr (<||> ==> <||>)
    MAArr  : {t1 t2 : τ̇} → (t1 ==> t2) ▸arr (t1 ==> t2)

  -- matching produces unique answers
  matchunicity : ∀{ t t2 t3 } →
                 t ▸arr t2 →
                 t ▸arr t3 →
                 t2 == t3
  matchunicity MAHole MAHole = refl
  matchunicity MAArr MAArr = refl

  -- bidirectional type checking judgements for ė
  mutual
    -- synthesis
    data _⊢_=>_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
      SAsc    : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 Γ ⊢ e <= t →
                 Γ ⊢ (e ·: t) => t
      SVar    : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                 (n , t) ∈ Γ →
                 Γ ⊢ X n => t
      SAp     : {Γ : ·ctx} {e1 e2 : ė} {t t' t2 : τ̇} →
                 Γ ⊢ e1 => t →
                 t ▸arr (t2 ==> t') →
                 Γ ⊢ e2 <= t2 →
                 Γ ⊢ (e1 ∘ e2) => t'
      SNum    :  {Γ : ·ctx} {n : Nat} →
                 Γ ⊢ N n => num
      SPlus   : {Γ : ·ctx} {e1 e2 : ė}  →
                 Γ ⊢ e1 <= num →
                 Γ ⊢ e2 <= num →
                 Γ ⊢ (e1 ·+ e2) => num
      SEHole  : {Γ : ·ctx} → Γ ⊢ <||> => <||>
      SFHole  : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 Γ ⊢ e => t →
                 Γ ⊢ <| e |> => <||>

    -- analysis
    data _⊢_<=_ : (Γ : ·ctx) → (e : ė) → (t : τ̇) → Set where
      ASubsume : {Γ : ·ctx} {e : ė} {t t' : τ̇} →
                 Γ ⊢ e => t' →
                 t ~ t' →
                 Γ ⊢ e <= t
      ALam : {Γ : ·ctx} {e : ė} {t t1 t2 : τ̇} {x : Nat} →
                 x # Γ →
                 t ▸arr (t1 ==> t2) →
                 (Γ ,, (x , t1)) ⊢ e <= t2 →
                 Γ ⊢ (·λ x e) <= t

  ----- a couple of exmaples to demonstrate how the encoding above works

  -- the function (λx. x + 0) where x is named "0".
  add0 : ė
  add0 = ·λ 0 (X 0 ·+ N 0)

  -- this is the derivation that fn has type num ==> num
  ex1 : ∅ ⊢ ·λ 0 (X 0 ·+ N 0) <= (num ==> num)
  ex1 = ALam refl MAArr (ASubsume
                           (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume SNum TCRefl))
                           TCRefl)

  -- the derivation that when applied to the numeric argument 10 add0
  -- produces a num.
  ex2 : ∅ ⊢ (add0 ·: (num ==> num)) ∘ (N 10) => num
  ex2 = SAp (SAsc ex1) MAArr (ASubsume SNum TCRefl)

  -- the slightly longer derivation that argues that add0 applied to a
  -- variable that's known to be a num produces a num
  ex2b : (∅ ,, (1 , num)) ⊢ (add0 ·: (num ==> num)) ∘ (X 1) => num
  ex2b = SAp (SAsc (ALam refl MAArr (ASubsume
                                       (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume SNum TCRefl))
                                       TCRefl))) MAArr (ASubsume (SVar refl) TCRefl)

  -- eta-expanding addition to curry it gets num → num → num
  ex3 : ∅ ⊢ ·λ 0 ( (·λ 1 (X 0 ·+ X 1)) ·: (num ==> num)  )
               <= (num ==> (num ==> num))
  ex3 = ALam refl MAArr (ASubsume (SAsc (ALam refl MAArr (ASubsume
                                                            (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume (SVar refl) TCRefl))
                                                            TCRefl))) TCRefl)

  -- applying three to four has type hole -- but there is no action that
  -- can fill the hole in the type so this term is forever incomplete.
  ex4 : ∅ ⊢ ((N 3) ·: <||>) ∘ (N 4) => <||>
  ex4 = SAp (SAsc (ASubsume SNum TCHole2)) MAHole (ASubsume SNum TCHole2)


  ----- some theorems about the rules and judgement presented so far.

  -- a variable is apart from any context from which it is removed
  aar : (Γ : ·ctx) (x : Nat) → x # (Γ / x)
  aar Γ x with natEQ x x
  aar Γ x | Inl refl = refl
  aar Γ x | Inr x≠x  = abort (x≠x refl)

  -- contexts give at most one binding for each variable
  ctxunicity : {Γ : ·ctx} {n : Nat} {t t' : τ̇} →
               (n , t) ∈ Γ →
               (n , t') ∈ Γ →
               t == t'
  ctxunicity {n = n} p q with natEQ n n
  ctxunicity p q | Inl refl = someinj (! p · q)
  ctxunicity _ _ | Inr x≠x = abort (x≠x refl)

  -- type consistency is symmetric
  ~sym : {t1 t2 : τ̇} → t1 ~ t2 → t2 ~ t1
  ~sym TCRefl = TCRefl
  ~sym TCHole1 = TCHole2
  ~sym TCHole2 = TCHole1
  ~sym (TCArr p1 p2) = TCArr (~sym p1) (~sym p2)

  -- if the domain or codomain of a pair of arrows isn't consistent, the
  -- whole arrow isn't consistent.
  lemarr1 : {t1 t2 t3 t4 : τ̇} → (t1 ~ t3 → ⊥) → (t1 ==> t2) ~ (t3 ==> t4)  → ⊥
  lemarr1 v TCRefl = v TCRefl
  lemarr1 v (TCArr p _) = v p

  lemarr2 : {t1 t2 t3 t4 : τ̇} → (t2 ~ t4 → ⊥) → (t1 ==> t2) ~ (t3 ==> t4) →  ⊥
  lemarr2 v TCRefl = v TCRefl
  lemarr2 v (TCArr _ p) = v p

  --  every pair of types is either consistent or not consistent
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

  -- theorem: no pair of types is both consistent and not consistent. this
  -- is immediate from our encoding of the ~̸ judgement in the formalism
  -- here; in the exact mathematics presented in the paper, this would
  -- require induction to relate the two judgements.
  ~apart : {t1 t2 : τ̇} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart v p = v p


  -- synthesis only produces equal types. note that there is no need for an
  -- analagous theorem for analytic positions because we think of
  -- the type as an input
  synthunicity : {Γ : ·ctx} {e : ė} {t t' : τ̇} →
                  (Γ ⊢ e => t)
                → (Γ ⊢ e => t')
                → t == t'
  synthunicity (SAsc _) (SAsc _) = refl
  synthunicity {Γ = G} (SVar in1) (SVar in2) = ctxunicity {Γ = G} in1 in2
  synthunicity (SAp D1 MAHole b) (SAp D2 MAHole y) = refl
  synthunicity (SAp D1 MAHole b) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr b) (SAp D2 MAHole y) with synthunicity D1 D2
  ... | ()
  synthunicity (SAp D1 MAArr b) (SAp D2 MAArr y) with synthunicity D1 D2
  ... | refl = refl
  synthunicity SNum SNum = refl
  synthunicity (SPlus _ _ ) (SPlus _ _ ) = refl
  synthunicity SEHole SEHole = refl
  synthunicity (SFHole _) (SFHole _) = refl


  ----- the zippered form of the forms above and the rules for actions on them

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
    envelop : action

  -- type actions
  data _+_+>_ : (t : τ̂) → (α : action) → (t' : τ̂) → Set where
    TMFirstChild : {t1 t2 : τ̇} →
               ▹ t1 ==> t2 ◃ + move firstChild +> (▹ t1 ◃ ==>₁ t2)
    TMParent1 : {t1 t2 : τ̇} →
               (▹ t1 ◃ ==>₁ t2) + move parent +> ▹ t1 ==> t2 ◃
    TMParent2 : {t1 t2 : τ̇} →
               (t1 ==>₂ ▹ t2 ◃) + move parent +> ▹ t1 ==> t2 ◃
    TMNextSib : {t1 t2 : τ̇} →
               (▹ t1 ◃ ==>₁ t2) + move nextSib +> (t1 ==>₂ ▹ t2 ◃)
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

    EMApFirstChild : {e1 e2 : ė} →
               (▹ e1 ∘ e2 ◃) + move firstChild +>e (▹ e1 ◃ ∘₁ e2)
    EMApParent1 : {e1 e2 : ė} →
               (▹ e1 ◃ ∘₁ e2) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMApParent2 : {e1 e2 : ė} →
               (e1 ∘₂ ▹ e2 ◃) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMApNextSib : {e1 e2 : ė} →
               (▹ e1 ◃ ∘₁ e2) + move nextSib +>e (e1 ∘₂ ▹ e2 ◃)

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
                (p : (x , t) ∈ Γ) →
                Γ ⊢ ▹ <||> ◃ => <||> ~ construct (var x) ~> ▹ X x ◃ => t
      SAConLam : {Γ : ·ctx} {x : Nat} →
               (x # Γ) →
                Γ ⊢ ▹ <||> ◃ => <||> ~ construct (lam x) ~>
                   ((·λ x <||>) ·:₂ (▹ <||> ◃ ==>₁ <||>)) => (<||> ==> <||>)
      SAConApArr : {Γ : ·ctx} {t t1 t2 : τ̇} {e : ė} →
                t ▸arr (t1 ==> t2) →
                Γ ⊢ ▹ e ◃ => t ~ construct ap ~>  e ∘₂ ▹ <||> ◃ => t2
      SAConApOtw : {Γ : ·ctx} {t : τ̇} {e : ė} →
                (t ~̸ (<||> ==> <||>)) →
                Γ ⊢ ▹ e ◃ => t ~ construct ap ~> <| e |> ∘₂ ▹ <||> ◃ => <||>
      SAConArg : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ ▹ e ◃ => t ~ construct arg ~> ▹ <||> ◃ ∘₁ e => <||>
      SAConNumlit : {Γ : ·ctx} {n : Nat} →
                Γ ⊢ ▹ <||> ◃ => <||> ~ construct (numlit n) ~> ▹ N n ◃ => num
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
                  (Γ ⊢ e <= (t' ◆t)) →
                  Γ ⊢ (e ·:₂ t) => (t ◆t) ~ α ~> (e ·:₂ t') => (t' ◆t)
      SAZipApArr : {Γ : ·ctx} {t t1 t2 t3 t4 : τ̇} {α : action} {eh eh' : ê} {e : ė} →
                 (t ▸arr (t3 ==> t4)) →
                 (Γ ⊢ (eh ◆e) => t2) →
                 (Γ ⊢ eh => t2 ~ α ~> eh' => t) →
                 (Γ ⊢ e <= t3) →
                 Γ ⊢ (eh ∘₁ e) => t1 ~ α ~> (eh' ∘₁ e) => t4
      SAZipApAna : {Γ : ·ctx} {t' t2 t : τ̇} {e : ė} {eh eh' : ê} {α : action} →
                 (t' ▸arr (t2 ==> t)) →
                 (Γ ⊢ e => t') →
                 (Γ ⊢ eh ~ α ~> eh' ⇐ t2) →
                 Γ ⊢ (e ∘₂ eh) => t ~ α ~> (e ∘₂ eh') => t
      SAZipPlus1 : {Γ : ·ctx} {e : ė} {eh eh' : ê} {α : action} →
                   (Γ ⊢ eh ~ α ~> eh' ⇐ num) →
                   Γ ⊢ (eh ·+₁ e) => num ~ α ~> (eh' ·+₁ e) => num
      SAZipPlus2 : {Γ : ·ctx} {e : ė} {eh eh' : ê} {α : action} →
                   (Γ ⊢ eh ~ α ~> eh' ⇐ num) →
                   Γ ⊢ (e ·+₂ eh) => num ~ α ~> (e ·+₂ eh') => num
      SAZipHole1 : {Γ : ·ctx} {e e' : ê} {t t' : τ̇} {α : action} →
                   (Γ ⊢ (e ◆e) => t) →
                   (Γ ⊢ e => t ~ α ~> e' => t') →
                   ((e' == ▹ <||> ◃) → ⊥) →
                   Γ ⊢ <| e |> => <||> ~ α ~>  <| e' |> => <||>
      SAZipHole2 : {Γ : ·ctx} {e : ê} {t : τ̇} {α : action} →
                   (Γ ⊢ (e ◆e) => t) →
                   (Γ ⊢ e => t ~ α ~> ▹ <||> ◃ => <||>) →
                   Γ ⊢ <| e |> => <||> ~ α ~> ▹ <||> ◃ => <||>
      SAEnvelop : {Γ : ·ctx} {e : ė} {t : τ̇} →
                  Γ ⊢ ▹ e ◃ => t ~ envelop ~> ▹ <| e |> ◃ => <||>

    -- analytic action expressions
    data _⊢_~_~>_⇐_ : (Γ : ·ctx) → (e : ê) → (α : action) →
                      (e' : ê) → (t : τ̇) → Set where
      AASubsume : {Γ : ·ctx} {e e' : ê} {t t' t'' : τ̇} {α : action} →
                  {p : (α == construct asc → ⊥) ×
                       ((x : Nat) → (α == construct (lam x) → ⊥))} →
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
      AAConVar : {Γ : ·ctx} {t t' : τ̇} {x : Nat} →
                 (t ~̸ t') →
                 (p : (x , t') ∈ Γ) →
                 Γ ⊢ ▹ <||> ◃ ~ construct (var x) ~> <| ▹ X x ◃ |> ⇐ t
      AAConLam1 : {Γ : ·ctx} {x : Nat} {t t1 t2 : τ̇} →
                  (x # Γ) →
                  (t ▸arr (t1 ==> t2)) →
                  Γ ⊢ ▹ <||> ◃ ~ construct (lam x) ~>
                      ·λ x (▹ <||> ◃) ⇐ t
      AAConLam2 : {Γ : ·ctx} {x : Nat} {t : τ̇} →
                  (x # Γ) →
                  (t ~̸ (<||> ==> <||>)) →
                  Γ ⊢ ▹ <||> ◃ ~ construct (lam x) ~>
                      <| ·λ x <||> ·:₂ (▹ <||> ◃ ==>₁ <||>) |> ⇐ t
      AAConNumlit : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                    (t ~̸ num) →
                    Γ ⊢ ▹ <||> ◃ ~ construct (numlit n) ~> <| ▹ (N n) ◃ |> ⇐ t
      AAFinish : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 (Γ ⊢ e <= t) →
                 Γ ⊢ ▹ <| e |> ◃ ~ finish ~> ▹ e ◃ ⇐ t
      AAZipLam : {Γ : ·ctx} {x : Nat} {t t1 t2 : τ̇} {e e' : ê} {α : action} →
                 (x # Γ) →
                 (t ▸arr (t1 ==> t2)) →
                 ((Γ ,, (x , t1)) ⊢ e ~ α ~> e' ⇐ t2) →
                 Γ ⊢ (·λ x e) ~ α ~> (·λ x e') ⇐ t

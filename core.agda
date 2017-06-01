open import Nat
open import Prelude

module core where
  -- types
  data τ̇ : Set where
    num  : τ̇
    ⦇⦈ : τ̇
    _==>_ : τ̇ → τ̇ → τ̇
    _⊕_ : τ̇ → τ̇ → τ̇

  -- expressions, prefixed with a · to distinguish name clashes with agda
  -- built-ins
  data ė : Set where
    _·:_  : ė → τ̇ → ė
    X     : Nat → ė
    ·λ    : Nat → ė → ė
    N     : Nat → ė
    _·+_  : ė → ė → ė
    ⦇⦈  : ė
    ⦇_⦈ : ė → ė
    _∘_   : ė → ė → ė
    inl  : ė → ė
    inr  : ė → ė
    case  : ė → Nat → ė → Nat → ė → ė

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
    TCHole1 : {t : τ̇} → t ~ ⦇⦈
    TCHole2 : {t : τ̇} → ⦇⦈ ~ t
    TCArr : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ==> t2) ~ (t1' ==> t2')
    TCPlus : {t1 t2 t1' t2' : τ̇} →
               t1 ~ t1' →
               t2 ~ t2' →
               (t1 ⊕ t2) ~ (t1' ⊕ t2')

  -- type inconsistency. a judgmental version and associated proofs are in
  -- judgemental-inconsistency.agda. each definition implies the other, but
  -- the two are isomorphic only if you treat proofs of inconsistency at
  -- arrow types as being proof-irrelevant---that is, if you don't
  -- distinguish between cases where the inconsistency between a pair of
  -- function types stems from the domain, range, or both. we use the form
  -- below throughout the rest of the development because we do not care to
  -- make that distinction.
  data _~̸_ : τ̇ → τ̇ → Set where
    ICNumArr1 : {t1 t2 : τ̇} → num ~̸ (t1 ==> t2)
    ICNumArr2 : {t1 t2 : τ̇} → (t1 ==> t2) ~̸ num
    ICArr1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               (t1 ==> t2) ~̸ (t3 ==> t4)
    ICArr2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               (t1 ==> t2) ~̸ (t3 ==> t4)
    ICNumPlus1 : {t1 t2 : τ̇} → num ~̸ (t1 ⊕ t2)
    ICNumPlus2 : {t1 t2 : τ̇} → (t1 ⊕ t2) ~̸ num
    ICPlus1 : {t1 t2 t3 t4 : τ̇} →
               t1 ~̸ t3 →
               (t1 ⊕ t2) ~̸ (t3 ⊕ t4)
    ICPlus2 : {t1 t2 t3 t4 : τ̇} →
               t2 ~̸ t4 →
               (t1 ⊕ t2) ~̸ (t3 ⊕ t4)
    ICPlusArr1 : {t1 t2 t3 t4 : τ̇} → (t1 ⊕ t2) ~̸ (t3 ==> t4)
    ICPlusArr2 : {t1 t2 t3 t4 : τ̇} → (t1 ==> t2) ~̸ (t3 ⊕ t4)

  --- matching for arrows
  data _▸arr_ : τ̇ → τ̇ → Set where
    MAHole : ⦇⦈ ▸arr (⦇⦈ ==> ⦇⦈)
    MAArr  : {t1 t2 : τ̇} → (t1 ==> t2) ▸arr (t1 ==> t2)

  data _▸plus_ : τ̇ → τ̇ → Set where
    MPHole  : ⦇⦈ ▸plus (⦇⦈ ⊕ ⦇⦈)
    MPPlus  : {t1 t2 : τ̇} → (t1 ⊕ t2) ▸plus (t1 ⊕ t2)

  -- matching produces unique answers
  matcharrunicity : ∀{ t t2 t3 } →
                 t ▸arr t2 →
                 t ▸arr t3 →
                 t2 == t3
  matcharrunicity MAHole MAHole = refl
  matcharrunicity MAArr MAArr = refl

  -- matching produces unique answers
  matchplusunicity : ∀{ t t2 t3 } →
                 t ▸plus t2 →
                 t ▸plus t3 →
                 t2 == t3
  matchplusunicity MPHole MPHole = refl
  matchplusunicity MPPlus MPPlus = refl

  -- if a type matches, then it's consistent with the least restrictive
  -- function type
  matchconsist : ∀{t t'} →
                 t ▸arr t' →
                 t ~ (⦇⦈ ==> ⦇⦈)
  matchconsist MAHole = TCHole2
  matchconsist MAArr = TCArr TCHole1 TCHole1

  matchnotnum : ∀{t1 t2} → num ▸arr (t1 ==> t2) → ⊥
  matchnotnum ()

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
      SEHole  : {Γ : ·ctx} → Γ ⊢ ⦇⦈ => ⦇⦈
      SNEHole : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 Γ ⊢ e => t →
                 Γ ⊢ ⦇ e ⦈ => ⦇⦈

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
      AInl : {Γ : ·ctx} {e : ė} {t+ t1 t2 : τ̇} →
                 t+ ▸plus (t1 ⊕ t2) →
                 Γ ⊢ e <= t1 →
                 Γ ⊢ inl e <= t+
      AInr : {Γ : ·ctx} {e : ė} {t+ t1 t2 : τ̇} →
                 t+ ▸plus (t1 ⊕ t2) →
                 Γ ⊢ e <= t2 →
                 Γ ⊢ inr e <= t+
      ACase : {Γ : ·ctx} {e e1 e2 : ė} {t t+ t1 t2 : τ̇} {x y : Nat} →
                 x # Γ →
                 y # Γ →
                 t+ ▸plus (t1 ⊕ t2) →
                 Γ ⊢ e => t+ →
                 (Γ ,, (x , t1)) ⊢ e1 <= t →
                 (Γ ,, (y , t2)) ⊢ e2 <= t →
                 Γ ⊢ case e x e1 y e2 <= t

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
  ~sym (TCPlus p1 p2) = TCPlus (~sym p1) (~sym p2)

  -- type consistency isn't transitive
  not-trans : ((t1 t2 t3 : τ̇) → t1 ~ t2 → t2 ~ t3 → t1 ~ t3) → ⊥
  not-trans t with t (num ==> num) ⦇⦈ num TCHole1 TCHole2
  ... | ()

  --  every pair of types is either consistent or not consistent
  ~dec : (t1 t2 : τ̇) → ((t1 ~ t2) + (t1 ~̸ t2))
    -- this takes care of all hole cases, so we don't consider them below
  ~dec _ ⦇⦈ = Inl TCHole1
  ~dec ⦇⦈ _ = Inl TCHole2
    -- num cases
  ~dec num num = Inl TCRefl
  ~dec num (t2 ==> t3) = Inr ICNumArr1
    -- arrow cases
  ~dec (t1 ==> t2) num = Inr ICNumArr2
  ~dec (t1 ==> t2) (t3 ==> t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCArr x y)
  ... | Inl _ | Inr y = Inr (ICArr2 y)
  ... | Inr x | _     = Inr (ICArr1 x)
    -- plus cases
  ~dec (t1 ⊕ t2) num = Inr ICNumPlus2
  ~dec (t1 ⊕ t2) (t3 ==> t4) = Inr ICPlusArr1
  ~dec (t1 ⊕ t2) (t3 ⊕ t4) with ~dec t1 t3 | ~dec t2 t4
  ... | Inl x | Inl y = Inl (TCPlus x y)
  ... | _     | Inr x = Inr (ICPlus2 x)
  ... | Inr x | Inl _ = Inr (ICPlus1 x)
  ~dec num (y ⊕ y₁) = Inr ICNumPlus1
  ~dec (x ==> x₁) (y ⊕ y₁) = Inr ICPlusArr2

  -- theorem: no pair of types is both consistent and not consistent. this
  -- is immediate from our encoding of the ~̸ judgement in the formalism
  -- here; in the exact mathematics presented in the paper, this would
  -- require induction to relate the two judgements.
  ~apart : {t1 t2 : τ̇} → (t1 ~̸ t2) → (t1 ~ t2) → ⊥
  ~apart ICNumArr1 ()
  ~apart ICNumArr2 ()
  ~apart (ICArr1 v) TCRefl = ~apart v TCRefl
  ~apart (ICArr1 v) (TCArr p p₁) = ~apart v p
  ~apart (ICArr2 v) TCRefl = ~apart v TCRefl
  ~apart (ICArr2 v) (TCArr p p₁) = ~apart v p₁
  ~apart ICNumPlus1 ()
  ~apart ICNumPlus2 ()
  ~apart (ICPlus1 x) TCRefl = ~apart x TCRefl
  ~apart (ICPlus1 x) (TCPlus y y₁) = ~apart x y
  ~apart (ICPlus2 x) TCRefl = ~apart x TCRefl
  ~apart (ICPlus2 x) (TCPlus y y₁) = ~apart x y₁
  ~apart ICPlusArr1 ()
  ~apart ICPlusArr2 ()

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
  synthunicity (SNEHole _) (SNEHole _) = refl


  ----- the zippered form of the forms above and the rules for actions on them

  -- those types without holes anywhere
  tcomplete : τ̇ → Set
  tcomplete num         = ⊤
  tcomplete ⦇⦈        = ⊥
  tcomplete (t1 ==> t2) = (tcomplete t1) × (tcomplete t2)
  tcomplete (t1 ⊕ t2) = (tcomplete t1) × (tcomplete t2)

  -- similarly to the complete types, the complete expressions
  ecomplete : ė → Set
  ecomplete (e1 ·: t)  = ecomplete e1 × tcomplete t
  ecomplete (X _)      = ⊤
  ecomplete (·λ _ e1)  = ecomplete e1
  ecomplete (N x)      = ⊤
  ecomplete (e1 ·+ e2) = ecomplete e1 × ecomplete e2
  ecomplete ⦇⦈       = ⊥
  ecomplete ⦇ e1 ⦈   = ⊥
  ecomplete (e1 ∘ e2)  = ecomplete e1 × ecomplete e2
  ecomplete (inl e)    = ecomplete e
  ecomplete (inr e)    = ecomplete e
  ecomplete (case e x e1 y e2)  = ecomplete e × ecomplete e1 × ecomplete e2

  -- zippered form of types
  data τ̂ : Set where
    ▹_◃  : τ̇ → τ̂
    _==>₁_ : τ̂ → τ̇ → τ̂
    _==>₂_ : τ̇ → τ̂ → τ̂
    _⊕₁_ : τ̂ → τ̇ → τ̂
    _⊕₂_ : τ̇ → τ̂ → τ̂

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
    ⦇_⦈ : ê → ê
    inl : ê → ê
    inr : ê → ê
    case₁ : ê → Nat → ė → Nat → ė → ê
    case₂ : ė → Nat → ê → Nat → ė → ê
    case₃ : ė → Nat → ė → Nat → ê → ê

  -- erasure of cursor for types and expressions, judgementally. see
  -- jugemental-erase.agda for an argument that this defines an isomorphic
  -- object to the direct metafunction provided in the text of the paper
  data erase-t : τ̂ → τ̇ → Set where
    ETTop  : ∀{t} → erase-t (▹ t ◃) t
    ETArrL : ∀{t1 t1' t2} → erase-t t1 t1' → erase-t (t1 ==>₁ t2) (t1' ==> t2)
    ETArrR : ∀{t1 t2 t2'} → erase-t t2 t2' → erase-t (t1 ==>₂ t2) (t1 ==> t2')
    ETPlusL : ∀{t1 t1' t2} → erase-t t1 t1' → erase-t (t1 ⊕₁ t2) (t1' ⊕ t2)
    ETPlusR : ∀{t1 t2 t2'} → erase-t t2 t2' → erase-t (t1 ⊕₂ t2) (t1 ⊕ t2')

  data erase-e : ê → ė → Set where
    EETop   : ∀{x}         → erase-e (▹ x ◃) x
    EEAscL  : ∀{e e' t}    → erase-e e e'   → erase-e (e ·:₁ t) (e' ·: t)
    EEAscR  : ∀{e t t'}    → erase-t t t'   → erase-e (e ·:₂ t) (e ·: t')
    EELam   : ∀{x e e'}    → erase-e e e'   → erase-e (·λ x e) (·λ x e')
    EEApL   : ∀{e1 e1' e2} → erase-e e1 e1' → erase-e (e1 ∘₁ e2) (e1' ∘ e2)
    EEApR   : ∀{e1 e2 e2'} → erase-e e2 e2' → erase-e (e1 ∘₂ e2) (e1 ∘ e2')
    EEPlusL : ∀{e1 e1' e2} → erase-e e1 e1' → erase-e (e1 ·+₁ e2) (e1' ·+ e2)
    EEPlusR : ∀{e1 e2 e2'} → erase-e e2 e2' → erase-e (e1 ·+₂ e2) (e1 ·+ e2')
    EENEHole : ∀{e e'}     → erase-e e e'   → erase-e ⦇ e ⦈  ⦇ e' ⦈
    EEInl   : ∀{e e'}      → erase-e e e'   → erase-e (inl e) (inl e')
    EEInr   : ∀{e e'}      → erase-e e e'   → erase-e (inr e) (inr e')
    EECase1 : ∀{e e' x e1 y e2} → erase-e e e' →
                                  erase-e (case₁ e x e1 y e2) (case e' x e1 y e2)
    EECase2 : ∀{e x e1 e1' y e2} → erase-e e1 e1' →
                                  erase-e (case₂ e x e1 y e2) (case e x e1' y e2)
    EECase3 : ∀{e x e1 y e2 e2'} → erase-e e2 e2' →
                                  erase-e (case₃ e x e1 y e2) (case e x e1 y e2')

  -- the three grammars that define actions
  data direction : Set where
    child : Nat → direction
    parent : direction

  data shape : Set where
    arrow : shape
    num   : shape
    asc   : shape
    var   : Nat → shape
    lam   : Nat → shape
    ap    : shape
    numlit : Nat → shape
    plus  : shape
    nehole : shape
    tplus : shape
    inl : shape
    inr : shape
    case : Nat → Nat → shape

  data action : Set where
    move : direction → action
    construct : shape → action
    del : action
    finish : action

  -- type actions
  data _+_+>_ : (t : τ̂) → (α : action) → (t' : τ̂) → Set where
    TMArrChild1 : {t1 t2 : τ̇} →
               ▹ t1 ==> t2 ◃ + move (child 1) +> (▹ t1 ◃ ==>₁ t2)
    TMArrChild2 : {t1 t2 : τ̇} →
               ▹ t1 ==> t2 ◃ + move (child 2) +> (t1 ==>₂ ▹ t2 ◃)
    TMArrParent1 : {t1 t2 : τ̇} →
               (▹ t1 ◃ ==>₁ t2) + move parent +> ▹ t1 ==> t2 ◃
    TMArrParent2 : {t1 t2 : τ̇} →
               (t1 ==>₂ ▹ t2 ◃) + move parent +> ▹ t1 ==> t2 ◃
    TMPlusChild1 : {t1 t2 : τ̇} →
               ▹ t1 ⊕ t2 ◃ + move (child 1) +> (▹ t1 ◃ ⊕₁ t2)
    TMPlusChild2 : {t1 t2 : τ̇} →
               ▹ t1 ⊕ t2 ◃ + move (child 2) +> (t1 ⊕₂ ▹ t2 ◃)
    TMPlusParent1 : {t1 t2 : τ̇} →
               (▹ t1 ◃ ⊕₁ t2) + move parent +> ▹ t1 ⊕ t2 ◃
    TMPlusParent2 : {t1 t2 : τ̇} →
               (t1 ⊕₂ ▹ t2 ◃) + move parent +> ▹ t1 ⊕ t2 ◃
    TMDel     : {t : τ̇} →
                (▹ t ◃) + del +> (▹ ⦇⦈ ◃)
    TMConArrow  : {t : τ̇} →
                (▹ t ◃) + construct arrow +> (t ==>₂ ▹ ⦇⦈ ◃)
    TMConPlus  : {t : τ̇} →
                (▹ t ◃) + construct tplus +> (t ⊕₂ ▹ ⦇⦈ ◃)
    TMConNum  : (▹ ⦇⦈ ◃) + construct num +> (▹ num ◃)
    TMArrZip1 : {t1 t1' : τ̂} {t2 : τ̇} {α : action} →
                (t1 + α +> t1') →
                ((t1 ==>₁ t2) + α +> (t1' ==>₁ t2))
    TMArrZip2 : {t2 t2' : τ̂} {t1 : τ̇} {α : action} →
                (t2 + α +> t2') →
                ((t1 ==>₂ t2) + α +> (t1 ==>₂ t2'))
    TMPlusZip1 : {t1 t1' : τ̂} {t2 : τ̇} {α : action} →
                (t1 + α +> t1') →
                ((t1 ⊕₁ t2) + α +> (t1' ⊕₁ t2))
    TMPlusZip2 : {t2 t2' : τ̂} {t1 : τ̇} {α : action} →
                (t2 + α +> t2') →
                ((t1 ⊕₂ t2) + α +> (t1 ⊕₂ t2'))

  -- expression movement
  data _+_+>e_ : (e : ê) → (α : action) → (e' : ê) → Set where
    -- rules for ascriptions
    EMAscChild1 : {e : ė} {t : τ̇} →
              (▹ e ·: t ◃) + move (child 1) +>e (▹ e ◃ ·:₁ t)
    EMAscChild2 : {e : ė} {t : τ̇} →
              (▹ e ·: t ◃) + move (child 2) +>e (e  ·:₂ ▹ t ◃)
    EMAscParent1 : {e : ė} {t : τ̇} →
              (▹ e ◃ ·:₁ t) + move parent +>e (▹ e ·: t ◃)
    EMAscParent2 : {e : ė} {t : τ̇} →
              (e ·:₂ ▹ t ◃) + move parent +>e (▹ e ·: t ◃)
    -- rules for lambdas
    EMLamChild1 : {e : ė} {x : Nat} →
              ▹ (·λ x e) ◃ + move (child 1) +>e ·λ x (▹ e ◃)
    EMLamParent : {e : ė} {x : Nat} →
               ·λ x (▹ e ◃) + move parent +>e ▹ (·λ x e) ◃
    -- rules for 2-ary constructors
    EMPlusChild1 : {e1 e2 : ė} →
               (▹ e1 ·+ e2 ◃) + move (child 1) +>e (▹ e1 ◃ ·+₁ e2)
    EMPlusChild2 : {e1 e2 : ė} →
               (▹ e1 ·+ e2 ◃) + move (child 2) +>e (e1 ·+₂ ▹ e2 ◃)
    EMPlusParent1 : {e1 e2 : ė} →
               (▹ e1 ◃ ·+₁ e2) + move parent +>e (▹ e1 ·+ e2 ◃)
    EMPlusParent2 : {e1 e2 : ė} →
               (e1 ·+₂ ▹ e2 ◃) + move parent +>e (▹ e1 ·+ e2 ◃)

    EMApChild1 : {e1 e2 : ė} →
               (▹ e1 ∘ e2 ◃) + move (child 1)+>e (▹ e1 ◃ ∘₁ e2)
    EMApChild2 : {e1 e2 : ė} →
               (▹ e1 ∘ e2 ◃) + move (child 2) +>e (e1 ∘₂ ▹ e2 ◃)
    EMApParent1 : {e1 e2 : ė} →
               (▹ e1 ◃ ∘₁ e2) + move parent +>e (▹ e1 ∘ e2 ◃)
    EMApParent2 : {e1 e2 : ė} →
               (e1 ∘₂ ▹ e2 ◃) + move parent +>e (▹ e1 ∘ e2 ◃)

    -- rules for non-empty holes
    EMNEHoleChild1 : {e : ė} →
               (▹ ⦇ e ⦈ ◃) + move (child 1) +>e ⦇ ▹ e ◃ ⦈
    EMNEHoleParent : {e : ė} →
                ⦇ ▹ e ◃ ⦈ + move parent +>e (▹ ⦇ e ⦈ ◃)

    -- rules for injections
    EMInlChild1 : {e : ė} →
               ▹ inl e ◃ + move (child 1) +>e inl ▹ e ◃
    EMInlParent : {e : ė} →
                inl ▹ e ◃ + move parent +>e ▹ inl e  ◃
    EMInrChild1 : {e : ė} →
               ▹ inr e ◃ + move (child 1) +>e inr ▹ e ◃
    EMInrParent : {e : ė} →
                inr ▹ e ◃ + move parent +>e ▹ inr e  ◃

    -- rules for case
    EMCaseParent1 : {e e1 e2 : ė} {x y : Nat} →
                case₁ ▹ e ◃ x e1 y e2 + move parent +>e ▹ case e x e1 y e2 ◃
    EMCaseParent2 : {e e1 e2 : ė} {x y : Nat} →
                case₂ e x ▹ e1 ◃ y e2 + move parent +>e ▹ case e x e1 y e2 ◃
    EMCaseParent3 : {e e1 e2 : ė} {x y : Nat} →
                case₃ e x e1 y ▹ e2 ◃ + move parent +>e ▹ case e x e1 y e2 ◃
    EMCaseChild1 : {e e1 e2 : ė} {x y : Nat} →
                ▹ case e x e1 y e2 ◃ + move (child 1) +>e case₁ ▹ e ◃ x e1 y e2
    EMCaseChild2 : {e e1 e2 : ė} {x y : Nat} →
                ▹ case e x e1 y e2 ◃ + move (child 2) +>e case₂ e x ▹ e1 ◃ y e2
    EMCaseChild3 : {e e1 e2 : ė} {x y : Nat} →
                ▹ case e x e1 y e2 ◃ + move (child 3) +>e case₃ e x e1 y ▹ e2 ◃

  mutual
  -- synthetic action expressions
    data _⊢_=>_~_~>_=>_ : (Γ : ·ctx) → (e1 : ê) → (t1 : τ̇)
                        → (α : action) → (e2 : ê) → (t2 : τ̇) → Set where
      SAMove : {δ : direction} {e e' : ê} {Γ : ·ctx} {t : τ̇} →
                (e + move δ +>e e') →
                Γ ⊢ e => t ~ move δ ~> e' => t
      SADel : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ ▹ e ◃ => t ~ del ~> ▹ ⦇⦈ ◃ => ⦇⦈
      SAConAsc : {Γ : ·ctx} {e : ė} {t : τ̇} →
                Γ ⊢ ▹ e ◃ => t ~ construct asc ~> (e ·:₂ ▹ t ◃ ) => t
      SAConVar : {Γ : ·ctx} {x : Nat} {t : τ̇} →
                (p : (x , t) ∈ Γ) →
                Γ ⊢ ▹ ⦇⦈ ◃ => ⦇⦈ ~ construct (var x) ~> ▹ X x ◃ => t
      SAConLam : {Γ : ·ctx} {x : Nat} →
               (x # Γ) →
                Γ ⊢ ▹ ⦇⦈ ◃ => ⦇⦈ ~ construct (lam x) ~>
                   ((·λ x ⦇⦈) ·:₂ (▹ ⦇⦈ ◃ ==>₁ ⦇⦈)) => (⦇⦈ ==> ⦇⦈)
      SAConApArr : {Γ : ·ctx} {t t1 t2 : τ̇} {e : ė} →
                t ▸arr (t1 ==> t2) →
                Γ ⊢ ▹ e ◃ => t ~ construct ap ~>  e ∘₂ ▹ ⦇⦈ ◃ => t2
      SAConApOtw : {Γ : ·ctx} {t : τ̇} {e : ė} →
                (t ~̸ (⦇⦈ ==> ⦇⦈)) →
                Γ ⊢ ▹ e ◃ => t ~ construct ap ~> ⦇ e ⦈ ∘₂ ▹ ⦇⦈ ◃ => ⦇⦈
      SAConNumlit : {Γ : ·ctx} {n : Nat} →
                Γ ⊢ ▹ ⦇⦈ ◃ => ⦇⦈ ~ construct (numlit n) ~> ▹ N n ◃ => num
      SAConPlus1 : {Γ : ·ctx} {e : ė} {t : τ̇} →
                (t ~ num) →
                Γ ⊢ ▹ e ◃ => t ~ construct plus ~> e ·+₂ ▹ ⦇⦈ ◃  => num
      SAConPlus2 : {Γ : ·ctx} {e : ė} {t : τ̇} →
                (t ~̸ num) →
                Γ ⊢ ▹ e ◃ => t ~ construct plus ~> ⦇ e ⦈ ·+₂ ▹ ⦇⦈ ◃  => num
      SAConNEHole : {Γ : ·ctx} {e : ė} {t : τ̇} →
                  Γ ⊢ ▹ e ◃ => t ~ construct nehole ~> ⦇ ▹ e ◃ ⦈ => ⦇⦈
      SAFinish : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 (Γ ⊢ e => t) →
                 Γ ⊢ ▹ ⦇ e ⦈ ◃ => ⦇⦈ ~ finish ~> ▹ e ◃ => t
      SAZipAsc1 : {Γ : ·ctx} {e e' : ê} {α : action} {t : τ̇} →
                  (Γ ⊢ e ~ α ~> e' ⇐ t) →
                  Γ ⊢ (e ·:₁ t) => t ~ α ~> (e' ·:₁ t) => t
      SAZipAsc2 : {Γ : ·ctx} {e : ė} {α : action} {t t' : τ̂} {t◆ t'◆ : τ̇} →
                  (t + α +> t') →
                  (erase-t t' t'◆) →
                  (erase-t t t◆) →
                  (Γ ⊢ e <= t'◆) →
                  Γ ⊢ (e ·:₂ t) => t◆ ~ α ~> (e ·:₂ t') => t'◆
      SAZipApArr : {Γ : ·ctx} {t t1 t2 t3 t4 : τ̇} {α : action} {eh eh' : ê} {e eh◆ : ė} →
                 (t ▸arr (t3 ==> t4)) →
                 (erase-e eh eh◆) →
                 (Γ ⊢ (eh◆) => t2) →
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
      SAZipHole : {Γ : ·ctx} {e e' : ê} {t t' : τ̇} {α : action} {e◆ : ė} →
                   (erase-e e e◆) →
                   (Γ ⊢ e◆ => t) →
                   (Γ ⊢ e => t ~ α ~> e' => t') →
                   Γ ⊢ ⦇ e ⦈ => ⦇⦈ ~ α ~>  ⦇ e' ⦈ => ⦇⦈
      SAConInl : {Γ : ·ctx} {t : τ̇} →
                  Γ ⊢ ▹ ⦇⦈ ◃ => t ~ construct inl ~> inl ⦇⦈ ·:₂ (▹ ⦇⦈ ◃ ⊕₁ ⦇⦈) => (⦇⦈ ⊕ ⦇⦈)
      SAConInr : {Γ : ·ctx} {t : τ̇} →
                  Γ ⊢ ▹ ⦇⦈ ◃ => t ~ construct inr ~> inr ⦇⦈ ·:₂ (⦇⦈ ⊕₂ ▹ ⦇⦈ ◃) => (⦇⦈ ⊕ ⦇⦈)
      SAConCase1 : {Γ : ·ctx} {x y : Nat} {t t1 t2 : τ̇} {e : ė} →
                   x # Γ →
                   y # Γ →
                   t ▸plus (t1 ⊕ t2) →
                   Γ ⊢ ▹ e ◃ => t ~ construct (case x y) ~> (case₂ e x (▹ ⦇⦈ ◃) y ⦇⦈) ·:₁ ⦇⦈ => ⦇⦈
      SAConCase2 : {Γ : ·ctx} {x y : Nat} {t : τ̇} {e : ė} →
                   x # Γ →
                   y # Γ →
                   t ~̸ (⦇⦈ ⊕ ⦇⦈) →
                   Γ ⊢ ▹ e ◃ => t ~ construct (case x y) ~> (case₁ (⦇ ▹ e ◃ ⦈ ) x ⦇⦈ y ⦇⦈) ·:₁ ⦇⦈ => ⦇⦈

    -- analytic action expressions
    data _⊢_~_~>_⇐_ : (Γ : ·ctx) → (e : ê) → (α : action) →
                      (e' : ê) → (t : τ̇) → Set where
      AASubsume : {Γ : ·ctx} {e e' : ê} {t t' t'' : τ̇} {α : action} {e◆ : ė} →
                  (erase-e e e◆) →
                  (Γ ⊢ e◆ => t') →
                  (Γ ⊢ e => t' ~ α ~> e' => t'') →
                  (t ~ t'') →
                  Γ ⊢ e ~ α ~> e' ⇐ t
      AAMove : {e e' : ê} {δ : direction} {Γ : ·ctx} {t : τ̇} →
                  (e + move δ +>e e') →
                  Γ ⊢ e ~ move δ ~> e' ⇐ t
      AADel : {e : ė} {Γ : ·ctx} {t : τ̇} →
                 Γ ⊢ ▹ e ◃ ~ del ~> ▹ ⦇⦈ ◃ ⇐ t
      AAConAsc : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 Γ ⊢ ▹ e ◃ ~ construct asc ~> (e ·:₂ ▹ t ◃) ⇐ t
      AAConVar : {Γ : ·ctx} {t t' : τ̇} {x : Nat} →
                 (t ~̸ t') →
                 (p : (x , t') ∈ Γ) →
                 Γ ⊢ ▹ ⦇⦈ ◃ ~ construct (var x) ~> ⦇ ▹ X x ◃ ⦈ ⇐ t
      AAConLam1 : {Γ : ·ctx} {x : Nat} {t t1 t2 : τ̇} →
                  (x # Γ) →
                  (t ▸arr (t1 ==> t2)) →
                  Γ ⊢ ▹ ⦇⦈ ◃ ~ construct (lam x) ~>
                      ·λ x (▹ ⦇⦈ ◃) ⇐ t
      AAConLam2 : {Γ : ·ctx} {x : Nat} {t : τ̇} →
                  (x # Γ) →
                  (t ~̸ (⦇⦈ ==> ⦇⦈)) →
                  Γ ⊢ ▹ ⦇⦈ ◃ ~ construct (lam x) ~>
                      ⦇ ·λ x ⦇⦈ ·:₂ (▹ ⦇⦈ ◃ ==>₁ ⦇⦈) ⦈ ⇐ t
      AAConNumlit : {Γ : ·ctx} {t : τ̇} {n : Nat} →
                    (t ~̸ num) →
                    Γ ⊢ ▹ ⦇⦈ ◃ ~ construct (numlit n) ~> ⦇ ▹ (N n) ◃ ⦈ ⇐ t
      AAFinish : {Γ : ·ctx} {e : ė} {t : τ̇} →
                 (Γ ⊢ e <= t) →
                 Γ ⊢ ▹ ⦇ e ⦈ ◃ ~ finish ~> ▹ e ◃ ⇐ t
      AAZipLam : {Γ : ·ctx} {x : Nat} {t t1 t2 : τ̇} {e e' : ê} {α : action} →
                 x # Γ →
                 (t ▸arr (t1 ==> t2)) →
                 ((Γ ,, (x , t1)) ⊢ e ~ α ~> e' ⇐ t2) →
                 Γ ⊢ (·λ x e) ~ α ~> (·λ x e') ⇐ t
      AAConInl1 : {Γ : ·ctx} {t+ t1 t2 : τ̇} →
                t+ ▸plus (t1 ⊕ t2) →
                Γ ⊢ ▹ ⦇⦈ ◃ ~ construct inl ~> inl ▹ ⦇⦈ ◃ ⇐ t+
      AAConInl2 : {Γ : ·ctx} {t : τ̇} →
                t ~̸ (⦇⦈ ⊕ ⦇⦈) →
                Γ ⊢ ▹ ⦇⦈ ◃ ~ construct inl ~> ⦇ inl ⦇⦈ ·:₂ (▹ ⦇⦈ ◃ ⊕₁ ⦇⦈) ⦈ ⇐ t
      AAConInr1 : {Γ : ·ctx} {t+ t1 t2 : τ̇} →
                t+ ▸plus (t1 ⊕ t2) →
                Γ ⊢ ▹ ⦇⦈ ◃ ~ construct inr ~> inr ▹ ⦇⦈ ◃ ⇐ t+
      AAConInr2 : {Γ : ·ctx} {t : τ̇} →
                t ~̸  (⦇⦈ ⊕ ⦇⦈) →
                Γ ⊢ ▹ ⦇⦈ ◃ ~ construct inr ~> ⦇ inr ⦇⦈ ·:₂ (▹ ⦇⦈ ◃ ⊕₁ ⦇⦈) ⦈ ⇐ t
      AAConCase : {Γ : ·ctx} {x y : Nat} {t : τ̇} →
                x # Γ →
                y # Γ →
                Γ ⊢ ▹ ⦇⦈ ◃ ~ construct (case x y) ~> case₁ ▹ ⦇⦈ ◃ x ⦇⦈ y ⦇⦈ ⇐ t
      AAZipInl : {Γ : ·ctx} {t+ t1 t2 : τ̇} {e e' : ê} {α : action} →
                 t+ ▸plus (t1 ⊕ t2) →
                 Γ ⊢ e ~ α ~> e' ⇐ t1 →
                 Γ ⊢ inl e ~ α ~> inl e' ⇐ t+
      AAZipInr : {Γ : ·ctx} {t+ t1 t2 : τ̇} {e e' : ê} {α : action} →
                 t+ ▸plus (t1 ⊕ t2) →
                 Γ ⊢ e ~ α ~> e' ⇐ t2 →
                 Γ ⊢ inr e ~ α ~> inr e' ⇐ t+
      AAZipCase1 : {Γ : ·ctx} {e e' : ê} {e◆ e1 e2 : ė} {x y : Nat} {t t0 t+ t1 t2 : τ̇} {α : action} →
                 x # Γ →
                 y # Γ →
                 erase-e e e◆ →
                 Γ ⊢ e◆ => t0 →
                 Γ ⊢ e => t0 ~ α ~> e' => t+ →
                 t+ ▸plus (t1 ⊕ t2) →
                 (Γ ,, (x , t1)) ⊢ e1 <= t →
                 (Γ ,, (y , t2)) ⊢ e2 <= t →
                 Γ ⊢ case₁ e x e1 y e2 ~ α ~> case₁ e' x e1 y e2 ⇐ t
      AAZipCase2 : {Γ : ·ctx} {e1 e1' : ê} {e e2 : ė} {x y : Nat} {t t+ t1 t2 : τ̇} {α : action} →
                 x # Γ →
                 y # Γ →
                 Γ ⊢ e => t+ →
                 t+ ▸plus (t1 ⊕ t2) →
                 (Γ ,, (x , t1)) ⊢ e1 ~ α ~> e1' ⇐ t →
                 Γ ⊢ case₂ e x e1 y e2 ~ α ~> case₂ e x e1' y e2 ⇐ t
      AAZipCase3 : {Γ : ·ctx} {e2 e2' : ê} {e e1 : ė} {x y : Nat} {t t+ t1 t2 : τ̇} {α : action} →
                 x # Γ →
                 y # Γ →
                 Γ ⊢ e => t+ →
                 t+ ▸plus (t1 ⊕ t2) →
                 (Γ ,, (y , t2)) ⊢ e2 ~ α ~> e2' ⇐ t →
                 Γ ⊢ case₃ e x e1 y e2 ~ α ~> case₃ e x e1 y e2' ⇐ t

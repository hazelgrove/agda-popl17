open import Prelude
open import Nat

module List where
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  [_] : {A : Set} → A → List A
  [ x ] = x :: []

  -- lets us omit a bunch of parens
  infixr 9 _++_

  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  x :: l1 ++ l2 = x :: (l1 ++ l2)

  ++assoc : {A : Set} (l1 l2 l3 : List A) → (l1 ++ (l2 ++ l3)) == ((l1 ++ l2) ++ l3)
  ++assoc [] l2 l3 = refl
  ++assoc (x :: l1) l2 l3 = ap1 (_::_ x) (++assoc l1 l2 l3)

  map : {A B : Set} → (A → B) → (List A) → List B
  map f [] = []
  map f (x :: L) = (f x) :: map f L

  foldr : {A B : Set} → (A → B → B) → B → List A → B
  foldr f b [] = b
  foldr f b (x :: l) = f x (foldr f b l)

  -- list  membership
  data _∈_ {A : Set} : A → List A → Set where
    ∈h : {x : A} {l : List A} → x ∈ (x :: l)
    ∈t : {x y : A} {l : List A} → x ∈ l → x ∈ y :: l

  infixr 99 _::_

  data Unique {A B : Set} (f : A → B) : List A → Set where
    U[] : Unique f []
    U:: : {x : A} {xs : List A}
           → Unique f xs
           → (f x ∈ map f xs → ⊥)
           → Unique f (x :: xs)

  L : List (Nat × Nat)
  L = ((1 , 9) :: (2 , 9) :: [])

  ex1 : Unique π1 L
  ex1 = U:: (U:: U[] notemp) notin
    where
      notemp : {x : Nat} → x ∈ [] → ⊥
      notemp ()

      notin : 1 ∈ (2 :: []) → ⊥
      notin (∈t p) = notemp p

  ex2 : Unique π2 L → ⊥
  ex2 (U:: p x) = x ∈h

  maxl : List Nat → Nat
  maxl = foldr max 0

  -- addmax : {L : List Nat} (p : Unique (\x → x) L) → Unique (\x → x) ((1+ (maxl L)) :: L)
  -- addmax U[] = U:: U[] (λ ())
  -- addmax (U:: p x₁) with addmax p
  -- ... | ih = U:: (U:: p x₁) (λ x → x₁ {!!})

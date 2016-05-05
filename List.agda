open import Prelude
open import Nat

module List where
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  map : {A B : Set} → (A → B) → (List A) → List B
  map f [] = []
  map f (x :: L) = (f x) :: map f L

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

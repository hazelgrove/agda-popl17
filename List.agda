module List where
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  -- list  membership
  data _∈_ {A : Set} : A → List A → Set where
    ∈h : {x : A} {l : List A} → x ∈ (x :: l)
    ∈t : {x y : A} {l : List A} → x ∈ l → x ∈ y :: l

  infixr 99 _::_

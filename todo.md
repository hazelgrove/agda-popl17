- reflection: generate mapreduces, so that makes tcomplete and ecomplete
  effectively just
    ```agda
    (mapreduce τ̇) (\ <||> = ⊥ | _ = ⊤) (_×_)
    (mapreduce ė) (\ <||> = ⊥ | <| _ |> = ⊥ | _ = ⊤) tcomplete (_×_)
    ```
  generate e^ and t^ from e and t, both erasure erasure functions, matched
  for both. what else? probably the movement rules.

   (need newer version of agda to do reflection.)


- [make a new branch to work this out]

  abstract over constructor pairs in the expression movement stuff and
  write it up. i don't think this works. the idea is that for constructors
  (of either types or exps) that have the same arity, a lot of rules get
  repeated because of the zipper structure. so you want to be able to write
  stuff like
    ```agda
    Test : {tl tr : τ̇}
           (_Cl_ : τ̂ → τ̇ → τ̂)
           (_Cr_ : τ̇ → τ̂ → τ̂) →
           (▹ tl ◃ Cl tr ) + move nextSib +> (tl Cr ▹ tr ◃ )
    ```
  so that "any thing that forms a type out of two types moves the same
  way". the problem is that there's a coherence condition between Cl and Cr
  that i don't know how to express. specifically we intend this to be for
  ==>1 and ==>2, but (if we had x1 and x2 for product types) we could apply
  Test ==>1 x2 and get a bullshit movement. i don't know how to encode this
  in the type at the moment.

  * solution: judgmental coherence conditions.
    ```agda
       EMoveNextSib : {el er : ė}
            (_Cl_ : ê → ė → ê)
  	    (_Cr_ : ė → ê → ê)
   	    (cohere : (el Cl er)  ◆e) == ((el Cr er)  ◆e) →
            (▹ el ◃ Cl er ) + move nextSib +> (el Cr ▹ er ◃ )
     ```
     this lets us deal with anything.

  * second approach:

    ```agda
    data match : (ê → ė → ê) → (ė → ê → ê) → Set where
      Match∘ :  (l : ê → ė → ê)
                (r : ė → ê → ê)
                (pl : l == _∘₁_)
                (pr : r == _∘₂_) → match l r
      Match+ :  (l : ê → ė → ê)
                (r : ė → ê → ê)
                (pl : l == _·+₁_)
                (pr : r == _·+₂_) → match l r
    ```

  * third approach:
    ```
     cohere : (Cl == zap1 and Cr == zap2) or (Cl == zplus1 and Cr == zplus2)
     	  (just list out the pairs)
    ```
  the problem with these, so far, is that they're not a form that allows
  agda to generate the cases for determinism, or show that the cases that
  would be right if you wrote them out by hand are exhaustive. so it's a
  good idea but needs more work. maybe there's a better way to state them
  that doesn't cause this problem with this specific tool? maybe reflection
  is the right way to think about it; where the repetition in the rules is
  fine because there's really a fragment that's machine-writable, and you
  get the lemmas you need about them for free anyway.

  ---> the problem with all of these is that they're higher order
       constructors and that breaks things.

- fix todos in agda (am i using the barendregt variable convention correctly?)

- try to knock down some cases / use more lemmas

- constructable

- reachable (amounts to lowest common ancestor)

- declarative system + iso -> progress and preservation

- dynamics

- add ourselves to the agda wiki page, after arXive i guess

- extend with other types (sums, products) (branch)

- merge concrete branch back into master

- readme file

- i think the specific definition of focus erasure is breaking pattern
  matching in a bunch of places. you can't pattern match on the result of a
  function call. this happens also in defining the obvious ||_|| for
  erasure of ascriptions to relate the bidirectional system to a
  declarative one. i guess i need a new grammar, so i have constructors to
  break down?

- add let

- think of a better way to encode expression and type erasure. you can't
  pattern match on function calls, only things given by data
  declarations. that might make these proofs a lot easier. (as shown by
  working on the iso stuff.)

- abstract over movments somehow. moving between arguments is a little hard
  coded; what if everything had a list of arguments instead of specific
  forms? or is that the slippery slope to writing a full ABT library?

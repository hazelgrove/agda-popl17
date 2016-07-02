technical complaints about the proof text
-----------------------------------------

- fix todos in agda

- am i using the barendregt variable convention correctly?

- try to knock down some cases / use more lemmas

more metatheory
---------------

- constructable & reachable (amounts to lowest common ancestor)

dynamics
--------

- finish a dynamics on the complete system so we can sanity check holey
  ones

- write out the declarative type rules and injection from one to the other,
  per Frank's notes

- prove progress and preservation through the declarative system


langauge extensions
-------------------

- extend with other types (sums, products)

- let

- ifz


longer term ideas
-----------------

- abstract over movments somehow. moving between arguments is a little hard
  coded; what if everything had a list of arguments instead of specific
  forms? is that the slippery slope to writing a full ABT library, or the
  one to lvars?

- a richer notion of actions that allows for derived action forms. so if
  you can prove that a new action you have is admissible with respect to
  existing ones, you should be able to use it freely without needing to
  change the core proofs. like prevsib can be expressed with nextsib,
  parent, and first child.

- reflection: generate mapreduces, so that makes tcomplete and ecomplete
  effectively just
    ```agda
    (mapreduce τ̇) (\ <||> = ⊥ | _ = ⊤) (_×_)
    (mapreduce ė) (\ <||> = ⊥ | <| _ |> = ⊥ | _ = ⊤) tcomplete (_×_)
    ```
  generate e^ and t^ from e and t, both erasure erasure functions, matched
  for both. what else? probably the movement rules.

  need newer version of agda to do reflection, which will probably break
  other proofs we've done so far because of backwards compatiblity issues.

- abstract over constructor pairs in the expression movement stuff and
  write it up. the problem with all of the ideas below is that, while they
  work, it's all through higher order constructors and that breaks pattern
  generation and matching.

  i can prove sensibility with the higher order constructors formulation,
  but not determinism.

  the idea is that for constructors (of either types or exps) that have the
  same arity, a lot of rules get repeated because of the zipper
  structure. so you want to be able to write stuff like

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
  good idea but needs more work.

  maybe there's a better way to state them that doesn't cause this problem
  with this specific tool? maybe reflection is the right way to think about
  it; where the repetition in the rules is fine because there's really a
  fragment that's machine-writable, and you get the lemmas you need about
  them for free anyway.

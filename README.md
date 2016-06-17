# agda-tfp16

This repository contains the formalization of Hazelnut and the associated
metatheory.

Agda File Descriptions
======================

- [List.agda](List.agda), [Nat.agda](Nat.agda), and
   [Prelude.agda](Prelude.agda) describe some standard data structures,
   helpful types, a notion of equality, and related lemmas.

- [Hazelnut-core.agda](Hazelnut-core.agda) defines the basic syntax of
   Hazelnut, the static semantics, and the action semantics judgements.

- [Hazelnut-deterministic.agda and
   Hazelnut-sensible.agda](Hazelnut-deterministic.agda and
   Hazelnut-sensible.agda) prove the theorems from the TFP draft paper
   arguing that actions preserve well-typedness and are deterministic.

- [Hazelnut-declarative.agda](Hazelnut-declarative.agda) defines a
   declarative typing judgement for Hazelnut terms, rather than the main
   bidirectional one, and relates the two. This allows us to state type
   safety with respect to possible dynamic semantics.

- [Hazelnut-complete-dynamics.agda](Hazelnut-complete-dynamics.agda)
   defines the standard dynamic semantics on complete terms -- i.e. ones
   with no holes in them.

- [Hazelnut-checks.agda](Hazelnut-checks.agda) is a collection of theorems
   that amount to sanity checking the rules from the judgements -- the fact
   that they are true is not surprising, but does demonstrate that rules
   haven't been omitted. This is part of the effort to make the core
   calculus easy to extend with confidence.

- [todo.md](todo.md) is the short-hand todo list for this formalization
  effort.

- [keys.md](keys.md) is a list of agda-mode emacs key chords that enter the
   odder bits of unicode that we use in the Agda files

Assumptions and Represenatation Decisions
=========================================

- To keep the formalization tidy, we make a pretty strong assumption about
  variables in terms called Barendregt's convention.

  That is, we represent variables with just natural numbers, and assume
  that all terms are in something like a de Bruijn normal form with respect
  to these. That is to say: if a variable with name n ever appears
  anywhere, it's always the same varaible.

  The problem with this is that it's not true about arbitrary well-typed
  terms of a language. There is an injection from arbitrary terms to
  Barendregt-friendly ones, so it's sufficient. That injection is a
  whole-program transformation that amounts to careful use of alpha
  equivalence, so for the purpose of the current formalization our approach
  is sufficient.

  A more robust way to do this would be to implement an ABT library in
  Agda, likely with de Bruijn indices under the hood. That's a meaningful
  project all by itself, and not within the scope of this effort.

- Contexts are implemented as a function from variable names to possible
  types. This encodes the idea of contexts as a finite mapping neatly
  without getting the somewhat unwieldy Agda standard library involved and
  obfuscating the proof text.

  One concern with this representation is whether or not it's really
  constructive: there are some theorems about contexts that are only about
  this representation if you have function extensionality, which amounts to
  the Axiom of Choice.

  In this case, however, the functions that we build as contexts always
  have a finite domain and codomain, so that concern is not as bad as it
  might be. That fact is not reflected in the type of contexts. It could be
  made explicit by using mappings from `Fin n → τ̇` or paired with a
  maximum-name-used-so-far. We have not needed to do that yet, but it is an
  easy refactoring if we do in the future.

- Type compatability is a judgement all its own, rather than trying to use
  an agda internal notion of equality. This is because the notion of
  compatibility that we inherit from the work on gradual typing is
  deliberately not transitive, so it can't be easily encoded as equality.

  It's possible that there is a more elegant way to encode compatability
  with the homotopy type theoretic notion of a higher inductive type (HIT)
  but we haven't explored that at all.

- Type incompatability is not its own judgement, but rather represented as
  `{t1 t2 : ·τ} → t1 ~ t2 → ⊥`, which is the standard way to represent
  negation.

  This means the same thing as the judgement in the text, but saves us
  proving some lemmas describing the coherence between two types that would
  result from the direct translation into Agda. The only downside is that
  if the incompatibility judgement is extended in an incorrect way, we have
  no metatheory in the formalization that will break to show that.

- Each of the clauses of the theorems in the text are broken off into
  separate functions in the formalization. This is because the clauses are
  mutually recursive, following the mutual recursion of the bidirectional
  typing judgements.

- The sequence of conjunctions in the antecedents of the theorems have been
  curried into a sequence of implications instead, which is a benign
  transformation that simplifies the syntax of the formalization
  substantially.

- In the proofs of determinism, there's a fair amount of repeated
  argumentation. Agda's case exhaustiveness checking isn't sharp enough to
  know that two arguments of the same type in adjacent positions might be
  treated up to symmetry. In another language, we'd just write `f x y => f
  y x` as a default case, but this doesn't pass the termination checker for
  obvious reasons. The cases that are particularly verbose are diked out
  into a lemma; the rest are just repeated in place.

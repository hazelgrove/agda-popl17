# agda-popl17

This repository contains the formalization of Hazelnut and the associated
metatheory as submitted to POPL 2017.

The branch `sums` is formalization of the core calculus extended with sum
types. Currently, all theorems that are true for one are true for the
other. The best way to look at this and see what's required to extend the
Hazelnut core and metatheory for new language features is to run the
command `git diff master sums`.

File Descriptions
=================

[core.agda](core.agda) is the best file to start with. It gives
the basic definitions and syntax. Each file is documented
internally, but we give a brief description here in alphabetical order.

- [LICENSE](LICENSE) is the license for this work

- [List.agda](List.agda), [Nat.agda](Nat.agda), and,
  [Prelude.agda](Prelude.agda) define common data structures, types, and
  lemmas not specific to Hazelnut.

- [README.md](README.md) is this file you're reading right now.

- [aasubsume-min.agda](aasubsume-min.agda) describes a mapping from action
  derivations to a subset of the same type that is deterministic. This is
  part of the restricted form of determinism that we've proven.

- [all.agda](all.agda) acts as an ad-hoc make file for the project. If you
  run `agda all.agda` at the commandline in a clone with no `.agdai` files,
  it will check all the complete proofs from scratch. The files that
  contain proofs that are not yet done are also listed here, but commented
  out because Agda (very rightly) won't let you include modules with
  unsolved goals.

- [checks.agda](checks.agda) defines the iterated action semantics and the
  lemmas that lift the zipper rules to them.

- [complete-dynamics.agda](complete-dynamics.agda) is incomplete, but
  defines a notion of a dynamics on complete terms.

- [constructability.agda](constructability.agda) gives the proof of
  constructability.

- [core.agda](core.agda) defines the main judgements and grammars of the
  language, and gives a few lemmas.

- [declarative.agda](declarative.agda) is incomplete, but defines a
  declarative rather than bidirectional typing system and relates it to the
  main system.

- [deterministic.agda](deterministic.agda) proves that the action
  semantics, modulo the predicate defined in
  [aasubsume-min.agda](aasubsume-min.agda) are deterministic.

- [examples.agda](examples.agda) is a handful of small examples of the
  judgements and definitions from the other files in actions, showing small
  typing and action semantics derivations to help intuition.

- [future-work.agda](future-work.agda) is full of half-baked crack pot
  ideas about possible things we might want to prove soon.

- [judgemental-erase.agda](judgemental-erase.agda) defines the function
  form of cursor erasure and proves it isomorpic to the judgemental form
  given in [core.agda](core.agda).

- [judgemental-inconsistency.agda](judgemental-inconsistency.agda) defines
  a jugemental form of type inconsistency and proves it isomorphic to the
  functional form given in [core.agda](core.agda).

- [keys.md](keys.md) is a list of emacs agda-mode key chords to enter the
  unicode characters we use throughout the development.

- [moveerase.agda](moveerase.agda) contains theorems about the interaction
  between movement and cursor erasure.

- [reachability.agda](reachability.agda) gives the proof of reachability.

- [sensible.agda](sensible.agda) gives the proof of action sensibility.

- [structural.agda](structural.agda) is incomplete, but has proofs of
  standard structural properties like weakening, exchange, and contraction
  for the various context-sensitive judgements.


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

- Type consistency is a judgement all its own, rather than trying to use an
  agda internal notion of equality. This is because the notion of
  compatibility that we inherit from the work on gradual typing is
  deliberately not transitive, so it can't be easily encoded as equality.

  It's possible that there is a more elegant way to encode compatability
  with the homotopy type theoretic notion of a higher inductive type (HIT)
  but we haven't explored that at all.

- Type inconsistency is not its own judgement, but rather represented as
  `{t1 t2 : ·τ} → t1 ~ t2 → ⊥`, which is the standard way to represent
  negation.

  This means the same thing as the judgement in the text, but saves us
  proving some lemmas describing the coherence between two types that would
  result from the direct translation into Agda.

  The two views are shown isomorphic in
  [judgemental-inconsistency.agda](judgemental-inconsistency.agda), so if
  bad rules are added that isomorphism will break. This also jusitifes our
  use of the much-easier-to-program-with negation form.

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

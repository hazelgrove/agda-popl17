# agda-popl17

This repository contains the mechanization of Hazelnut and the associated
metatheory as submitted to POPL 2017.

The branch `sums` is the mechanization of the core calculus extended with
sum types as described in section 4 of the paper. It's a conservative
extension in the sense that the difference between the branches only adds
code for the new constructs: nothing is removed. All theorems are proven
for both branches.

The exact additions can be seen easily with `git diff master sums`, `git
diff master sums FILE` for a particualr file name, or in a slightly
prettier way at [https://github.com/hazelgrove/agda-popl17/compare/sums]
under the "Files Changed" tab.

Installation
============

In order to run the proofs in this repository through a type checker, you
need two tools: the Haskell Platform and Agda. We

Where To Find Each Theorem and Claim
====================================

Every theorem in the paper is proven in the mechanization.

In most cases this entails proving a few lemmas about the particular
representations defined in [core.agda](core.agda) or how they interact. We
have tried to name these lemmas in sugguestive ways and tried to locate
them near where they're used, but it's the nature of such things to end up
a little bit spread out. Each lemma has a quick slogan of what it roughly
shows over its definition.

There are also several places where we refer the reader to the
mechanization for more details. Here is where to look for each of these:

- Theorem 1, _Action Sensibility_, is in
  [sensibility.agda](sensibility.agda). The clauses are implemented by
  `actsense-synth` and `actsense-ana`.

- Theorem 2, _Movement Erasure Invariance_, is in
  [moveerase.agda](moveerase.agda). The clauses are implemented by
  `moveeraset`, `moveerase-synth`, and `moveerase-ana`.

- Theorem 3, _Reachability_, is in
  [reachability.agda](reachability.agda). The clauses are implemented by
  `reachability-types`, `reachability-synth`, and `reachability-ana`.

- Theorem 4, _Reach Up_, is also in
  [reachability.agda](reachability.agda). The clauses are implemented by
  `reachup-types`, `reachup-synth`, and `reachup-ana`.

- Theorem 5, _Reach Down_, is also in
  [reachability.agda](reachability.agda). The clauses are implemented by
  `reachdown-types`, `reachdown-synth`, and `reachdown-ana`.

- Theorem 6, _Constructability_, is in
  [constructability.agda](constructability.agda). The clauses are
  implemented by `construct-type`, `construct-synth` and `construct-ana`.

- Theorem 7, _Type Action Determinism_, is in
  [determinism.agda](determinism.agda). It is implemented by `actdet-type`.

- Theorem 8, Expression Action Determinism, is also in
  [determinism.agda](determinism.agda). The clauses are implemented by
  `actdet-synth` and `actdet-ana`. The predicate on derivations is given in
  [aasubsume-min.agda](aasubsume-min.agda) by `aasubmin-synth` and
  `aasubmin-ana`.


File Descriptions
=================

Here is a break down of what is in each file, listed in `ls` order.
[core.agda](core.agda) is the best file to start with.

- [LICENSE](LICENSE) is the license for this work.

- [List.agda](List.agda), [Nat.agda](Nat.agda), and,
  [Prelude.agda](Prelude.agda) define common data structures, types,
  notational conveniences, and lemmas not specific to Hazelnut.

- [README.md](README.md) is this file you're reading right now.

- [aasubsume-min.agda](aasubsume-min.agda) describes a mapping from action
  derivations to a subset of the same type that is deterministic. This is
  part of the restricted form of determinism that we've proven.

- [all.agda](all.agda) acts as an ad-hoc make file for the project. If you
  run `agda all.agda` at the command line in a clone with no `.agdai` files
  in the directory, it will check all the proofs from scratch. On a modern
  machine, this takes about 10 seconds for the master branch and about 14
  for the extension with sums.

- [checks.agda](checks.agda) defines the iterated action semantics and the
  lemmas that lift the zipper rules to it.

- [constructability.agda](constructability.agda) gives the proof of
  constructability.

- [core.agda](core.agda) is the best file to start with. It gives the basic
  definitions and syntax for the whole language in the order listed in the
  paper. The syntax of Agda forces us to name each rule in the paper when
  they have just numbers in the text, but we have tried to give them
  reasonably mnemonic names.

- [determinism.agda](determinism.agda) proves that the action semantics,
  modulo the predicate defined in [aasubsume-min.agda](aasubsume-min.agda),
  are deterministic.

- [examples.agda](examples.agda) is a handful of small examples of the
  judgements and definitions from the other files in actions, showing small
  typing and action semantics derivations to help intuition. This includes
  a full version of both Figure 1 and Figure 2 from the paper text.

- [judgemental-erase.agda](judgemental-erase.agda) defines the function
  form of cursor erasure given in the paper and proves it isomorpic to the
  judgemental form given in [core.agda](core.agda). It also defines lemmas
  to move between them. Since we prove them to be isomorphic, we use both
  forms throughout, choosing whichever one is more convenient in a given
  situation.

- [judgemental-inconsistency.agda](judgemental-inconsistency.agda) defines
  a jugemental form of type inconsistency and proves it isomorphic to the
  functional form given in [core.agda](core.agda).

- [keys.md](keys.md) is a list of emacs agda-mode key chords to enter the
  unicode characters we use throughout the development.

- [moveerase.agda](moveerase.agda) gives the proof of movement erasure
  invariance.

- [reachability.agda](reachability.agda) gives the proof of reachability.

- [sensibility.agda](sensibility.agda) gives the proof of action sensibility.

- [structural.agda](structural.agda) has proofs for the standard structural
  properties of weakening, exchange, and contraction for each of the the four
  context-sensitive judgements.


Assumptions and Represenatation Decisions
=========================================

- To keep the mechanization tidy, we make a pretty strong assumption about
  variables in terms called Barendregt's convention.

  That is, we represent variables with just natural numbers, and assume
  that all terms are in something like a de Bruijn normal form with respect
  to these. That is to say: if a variable with name n ever appears
  anywhere, it's always the same varaible.

  The problem with this is that it's not true about arbitrary well-typed
  terms of a language. There is an injection from arbitrary terms to
  Barendregt-friendly ones, so it's sufficient. That injection is a
  whole-program transformation that amounts to careful use of alpha
  equivalence, so for the purpose of the current mechanization our approach
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
  separate functions in the mechanization. This is because the clauses are
  mutually recursive, following the mutual recursion of the bidirectional
  typing judgements.

- The sequence of conjunctions in the antecedents of the theorems have been
  curried into a sequence of implications instead, which is a benign
  transformation that simplifies the syntax of the mechanization
  substantially.

- In the proofs of determinism, there's a fair amount of repeated
  argumentation. Agda's case exhaustiveness checking isn't sharp enough to
  know that two arguments of the same type in adjacent positions might be
  treated up to symmetry. In another language, we'd just write `f x y => f
  y x` as a default case, but this doesn't pass the termination checker for
  obvious reasons. The cases that are particularly verbose are diked out
  into a lemma; the rest are just repeated in place.

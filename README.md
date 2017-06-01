# agda-popl17

This repository contains the mechanization of Hazelnut and the associated
metatheory as submitted to POPL 2017 for artifact evaluation.

The branch `sums` is the mechanization of the core calculus extended with
sum types as described in Section 4 of the paper. It's a conservative
extension in the sense that the difference between the branches only adds
code for the new constructs: nothing is removed.

The branches `master-no-jincon` and `sums-no-jincon` are the same as their
namesakes, but with only one definition of type inconsistency. These were
not reviewed by the POPL AEC, but are included because they may be of
interest. The benefit to this development is that we don't need to reason
about proof irrelevance to establish the isomorphism between the two forms
of inconsistency; the downside is that the relationship between consistency
and inconsistency is less immediately obvious.

All theorems are proven for all branches.

The exact additions can be seen easily with `git diff master sums`, `git
diff master sums FILE` for a particular file name, or in a slightly
prettier way at http://github.com/hazelgrove/agda-popl17/compare/sums under
the "Files Changed" tab.

Inspecting The Artifact
=======================

In order to inspect the artifact, the first thing you need to do is
download the code in this repository. You can either clone the repository
and switch between branches, or download zip files of both branches through
the github web interface.

In order to actually check the proofs, you need two tools: the Haskell
Platform and Agda. Both are available for most modern operating systems and
have extensive documentation for installation at their home sites:

- https://www.haskell.org/platform/

- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download

We know the Agda in this artifact to load cleanly under `Agda version
2.5.1.1`, which is the most recent stable version at the time of
submission. As research software, Agda frequently breaks backwards and
forwards compatibility, so it may or may not load under other versions.

Once Agda has been installed, the command `agda all.agda` run in the
appropriate directory will cause Agda to typecheck our artifact. On a
modern machine, this takes about 10 seconds for the master branch and about
14 for the extension with sums.

For syntax hilighting and other support, Agda files can be viewed in
`emacs`, `vim`, or here on github.

Where To Find Each Theorem and Claim
====================================

Every theorem in the paper is proven in the mechanization.

In most cases this entails proving a few lemmas about the particular
representations defined in [core.agda](core.agda) or how they interact. We
have tried to name these lemmas in suggestive ways and tried to locate
them near where they're used, but it's the nature of such things to end up
a little bit spread out. Each lemma has a quick slogan of what it roughly
shows over its definition.

Here is where to find each theorem:

- Theorem 1, _Action Sensibility_, is in
  [sensibility.agda](sensibility.agda), given by `actsense-synth` and
  `actsense-ana`.

- Theorem 2, _Movement Erasure Invariance_, is in
  [moveerase.agda](moveerase.agda), given by `moveeraset`,
  `moveerase-synth`, and `moveerase-ana`.

- Theorem 3, _Reachability_, is in [reachability.agda](reachability.agda),
  given by `reachability-types`, `reachability-synth`, and
  `reachability-ana`.

- Theorem 4, _Reach Up_, is also in [reachability.agda](reachability.agda),
  given by `reachup-types`, `reachup-synth`, and `reachup-ana`.

- Theorem 5, _Reach Down_, is also in
  [reachability.agda](reachability.agda), given by `reachdown-types`,
  `reachdown-synth`, and `reachdown-ana`.

- Theorem 6, _Constructability_, is in
  [constructability.agda](constructability.agda). The clauses are
  implemented by `construct-type`, `construct-synth` and `construct-ana`.

- Theorem 7, _Type Action Determinism_, is in
  [determinism.agda](determinism.agda), given by `actdet-type`.

- Theorem 8, _Expression Action Determinism_, is also in
  [determinism.agda](determinism.agda), given by `actdet-synth` and
  `actdet-ana`. The predicate on derivations is given in
  [aasubsume-min.agda](aasubsume-min.agda) by `aasubmin-synth` and
  `aasubmin-ana`.

There are also several places where we refer the reader to the
mechanization for more details. Here is where to look for each of these:

- The missing rules for z-expression cursor movement mentioned on page 2
  are present in the version of Figure 1 and Figure 2 in
  [examples.agda](examples.agda).

- The proof that the judgements that mention contexts obey weakening,
  exchange, and contraction mentioned on page 3 is in
  [structural.agda](structural.agda).

- The predicate on derivations mentioned on page 8 is in
  [aasubsume-min.agda](aasubsume-min.agda).

- The extension to the language mentioned on page 8 is in the `sums` branch
  of this repository.

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
  in the directory, it will check all the proofs from scratch.

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
  form of cursor erasure given in the paper and proves it isomorphic to the
  judgemental form given in [core.agda](core.agda). It also defines lemmas
  to move between them. Since we prove them to be isomorphic, we use both
  forms throughout, choosing whichever one is more convenient in a given
  situation.

- [keys.md](keys.md) is a list of emacs agda-mode key chords to enter the
  unicode characters we use throughout the development.

- [moveerase.agda](moveerase.agda) gives the proof of movement erasure
  invariance.

- [reachability.agda](reachability.agda) gives the proof of reachability.

- [sensibility.agda](sensibility.agda) gives the proof of action sensibility.

- [structural.agda](structural.agda) has proofs for the standard structural
  properties of weakening, exchange, and contraction for each of the the four
  context-sensitive judgements.


Assumptions and Representation Decisions
=========================================

- To keep the mechanization tidy, we make a pretty strong assumption about
  variables in terms called Barendregt's convention.

  That is, we represent variables with just natural numbers, and assume
  that all terms are in something like a de Bruijn normal form with respect
  to these: if a variable with name `n` ever appears anywhere, it's always
  the same variable.

  This is reflected in the mechanization mostly by a few apartness premises
  in the rules that are omitted in the on-paper notation.

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
  constructive: there are some theorems about contexts that are only
  provably about this representation if you have function extensionality,
  which is independent from the logic of Agda.

  In this case, however, the functions that we build as contexts always
  have a finite domain and codomain. Function extensionality is provable
  under that restriction, but the restriction is not reflected in the type
  of contexts. It could be made explicit by using mappings from `Fin n → τ̇`
  or paired with a maximum-name-used-so-far. We have not needed to do that
  yet, but it is an easy refactoring if we do in the future.

- The notion of consistency that we inherit from the work on gradual typing
  is deliberately not transitive, so it can't be gracefully encoded with
  equality using any of the common techniques involving the module system
  or dependent types. Therefore it is given by a type, like all the other
  judgements.

  It's possible that there is a more elegant way to encode compatibility
  with the homotopy type theoretic notion of a higher inductive type (HIT)
  but we haven't explored that at all.

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

- The paper text does not specify exactly what the base type `num` is. In
  the mechanization we use unary natural numbers, specifically the type
  `Nat`. The only property that we require of `num` is that equality be
  decidable, so another choice would have been to abstract the rules over
  anything that happens to have decidable equality--and maybe anything that
  has enough algebraic structure to support addition.

  While Agda does provide tools to take this other approach, we chose to
  use natural numbers as a surrogate instead to keep the proofs smaller and
  more focused on the properties we're interested in proving.

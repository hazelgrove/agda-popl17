# agda-tfp16

Formalization of joint work submitted to TFP2016

Assumptions and Represenatation Decisions
=========================================

- To keep the formalization tidy, we make a pretty strong assumption about
  variables in terms. That is, we represent variables with just natural
  numbers, and assume that all terms are in something like a de Bruijn
  normal form with respect to these. That is to say: if a variable with
  name n ever appears anywhere, it's always the same varaible.

  a more robust way to do this would be to implement an ABT library in
  Agda, likely with de Bruijn indices under the hood. that's a meaningful
  project all by itself, and not within the scope of this effort.

- contexts are implemented with simple lists of pairs of variables and
  types. we make no effort to check if something's already present in a
  context or try to keep them in sorted order.  premises that involve
  something being present in a context are expressed using the inductive
  type that encodes membership.

- type compatability is a judgement all its own, rather than trying to use
  an agda internal notion of equality. this is irritating, but given (1ja)
  i'm not sure how to avoid it without HITs or something similarly elephant
  gun like.

- type incompatability is not its own judgement, but rather represented as
  {t1 t2 : ·τ} → t1 ~ t2 → ⊥, which is the standard way to represent
  negation. this means the same thing as the judgement in the text, but
  saves us proving some unimportant lemmas describing the coherence between
  two types that would result from the direct translation into Agda

- each of the clauses of the theorems in the text are broken off into
  separate functions in the formalization.

- the sequence of conjunctions inte the antecedents of the theorems have
  been curried into a sequence of implications instead

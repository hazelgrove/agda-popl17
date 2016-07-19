open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import sensible

module checks where
  -- these three judmgements lift the action semantics judgements to relate
  -- an expression and a list of pair-wise composable actions to the
  -- expression that's produced by tracing through the action semantics for
  -- each element in that list.
  --
  -- we do this just by appealing to the original judgement with
  -- constraints on the terms to enforce composability.
  --
  -- in all three cases, we assert that the empty list of actions
  -- constitutes a reflexivity step, so when you run out of actions to
  -- preform you have to be where you wanted to be.
  --
  -- note that the only difference between the types for each judgement and
  -- the original action semantics is that the action is now a list of
  -- actions.
  data runtype : (t : τ̂) (Lα : List action) (t' : τ̂) → Set where
     DoRefl : {t : τ̂} → runtype t [] t
     DoType : {t : τ̂} {α : action} {t' t'' : τ̂}
              {L : List action} →
               t + α +> t' →
               runtype t' L t'' →
               runtype t (α :: L) t''

  data runsynth :
    (Γ : ·ctx) (e : ê) (t1 : τ̇) (Lα : List action) (e' : ê) (t2 : τ̇) → Set where
     DoRefl  : {Γ : ·ctx} {e : ê} {t : τ̇} → runsynth Γ e t [] e t
     DoSynth : {Γ : ·ctx} {e : ê} {t : τ̇} {α : action} {e' e'' : ê} {t' t'' : τ̇}
               {L : List action} →
               Γ ⊢ e => t ~ α ~> e' => t' →
               runsynth Γ e' t' L e'' t'' →
               runsynth Γ e t (α :: L) e'' t''

  data runana : (Γ : ·ctx) (e : ê) (Lα : List action) (e' : ê) (t : τ̇) → Set where
     DoRefl : {Γ : ·ctx} {e : ê} {t : τ̇} → runana Γ e [] e t
     DoAna : {Γ : ·ctx} {e : ê} {α : action} {e' e'' : ê} {t : τ̇}
              {L : List action} →
              Γ ⊢ e ~ α ~> e' ⇐ t →
              runana Γ e' L e'' t →
              runana Γ e (α :: L) e'' t

  -- all three run judgements lift to the list monoid as expected. these
  -- theorems are simple because the structure of lists is simple, but they
  -- amount a reasoning principle about the composition of action sequences
  -- by letting you split lists in (nearly) arbitrary places and argue
  -- about the consequences of the splits before composing them together.
  runtype++ : ∀{t t' t'' L1 L2 }
                → runtype t  L1 t'
                → runtype t' L2 t''
                → runtype t (L1 ++ L2) t''
  runtype++ DoRefl d2 = d2
  runtype++ (DoType x d1) d2 = DoType x (runtype++ d1 d2)

  runsynth++ : ∀{Γ e t L1 e' t' L2 e'' t''}
                → runsynth Γ e t L1 e' t'
                → runsynth Γ e' t' L2 e'' t''
                → runsynth Γ e t (L1 ++ L2) e'' t''
  runsynth++ DoRefl d2 = d2
  runsynth++ (DoSynth x d1) d2 = DoSynth x (runsynth++ d1 d2)

  runana++ : ∀{Γ e t L1 e' L2 e''}
                → runana Γ e  L1 e' t
                → runana Γ e' L2 e'' t
                → runana Γ e (L1 ++ L2) e'' t
  runana++ DoRefl d2 = d2
  runana++ (DoAna x d1) d2 = DoAna x (runana++ d1 d2)

  -- the following collection of lemmas asserts that the various runs
  -- interoperate nicely. in many cases, these amount to observing
  -- something like congruence: if a subterm is related to something by one
  -- of the judgements, it can be replaced by the thing to which it is
  -- related in a larger context without disrupting that larger
  -- context.
  --
  -- taken together, this is a little messier than a proper congruence,
  -- because the action semantics demand well-typedness at each step, and
  -- therefore there are enough premises to each lemma to supply to the
  -- action semantics rules.
  --
  -- therefore, these amount to a checksum on the zipper actions under the
  -- lifing of the action semantics to the list monoid.
  --
  -- they only check the zipper actions they happen to be include, however,
  -- which is driven by the particular lists we use in the proofs of
  -- contructability and reachability, which may or may not be all of
  -- them. additionally, the lemmas given here are what is needed for these
  -- proofs, not anything that's more general.

    -- type zippers
  ziplem-tm1 : ∀ {t1 t1' t2 L } →
            runtype t1' L t1 →
            runtype (t1' ==>₁ t2) L (t1 ==>₁ t2)
  ziplem-tm1 DoRefl = DoRefl
  ziplem-tm1 (DoType x L') = DoType (TMZip1 x) (ziplem-tm1 L')

  ziplem-tm2 : ∀ {t1 t2 t2' L } →
            runtype t2' L t2 →
            runtype (t1 ==>₂ t2') L (t1 ==>₂ t2)
  ziplem-tm2 DoRefl = DoRefl
  ziplem-tm2 (DoType x L') = DoType (TMZip2 x) (ziplem-tm2 L')


    -- expression zippers
  ziplem-asc1 : ∀{Γ t L e e'} →
        runana Γ e L e' t →
        runsynth Γ (e ·:₁ t) t L (e' ·:₁ t) t
  ziplem-asc1 DoRefl = DoRefl
  ziplem-asc1 (DoAna a r) = DoSynth (SAZipAsc1 a) (ziplem-asc1 r)

  -- todo: why is this easier with a weird mix of erasures?
  ziplem-asc2 : ∀{Γ t L t' t◆ t'◆} →
               erase-t t t◆ →
               erase-t t' t'◆ →
               runtype t L t' →
               runsynth Γ (<||> ·:₂ t) t◆ L (<||> ·:₂ t') t'◆
  ziplem-asc2 {Γ} er er' rt with erase-t◆ er | erase-t◆ er'
  ... | refl | refl = ziplem-asc2' {Γ = Γ} rt
   where
     ziplem-asc2' : ∀{t L t' Γ } →
               runtype t L t' →
               runsynth Γ (<||> ·:₂ t) (t ◆t) L (<||> ·:₂ t') (t' ◆t)
     ziplem-asc2' DoRefl = DoRefl
     ziplem-asc2' (DoType x rt) = DoSynth
                      (SAZipAsc2 x (◆erase-t _ _ refl) (◆erase-t _ _ refl)
                                (ASubsume SEHole TCHole1)) (ziplem-asc2' rt)

  ziplem-lam : ∀ {Γ x e t t1 t2 L e'} →
                   x # Γ →
                   t ▸arr (t1 ==> t2) →
                   runana (Γ ,, (x , t1)) e L e' t2 →
                   runana Γ (·λ x e) L (·λ x e') t
  ziplem-lam a m DoRefl = DoRefl
  ziplem-lam a m (DoAna x₁ d) =  DoAna (AAZipLam a m x₁) (ziplem-lam a m d)

  ziplem-plus1 : ∀{ Γ e L e' f} →
                       runana Γ e L e' num →
                       runsynth Γ (e ·+₁ f) num L (e' ·+₁ f) num
  ziplem-plus1 DoRefl = DoRefl
  ziplem-plus1 (DoAna x d) = DoSynth (SAZipPlus1 x) (ziplem-plus1 d)

  ziplem-plus2 : ∀{ Γ e L e' f} →
                       runana Γ e L e' num →
                       runsynth Γ (f ·+₂ e) num L (f ·+₂ e') num
  ziplem-plus2 DoRefl = DoRefl
  ziplem-plus2 (DoAna x d) = DoSynth (SAZipPlus2 x) (ziplem-plus2 d)

  ziplem-ap2 : ∀{ Γ e L e' t t' f tf} →
                       Γ ⊢ f => t' →
                       t' ▸arr (t ==> tf) →
                       runana Γ e L e' t →
                       runsynth Γ (f ∘₂ e) tf L (f ∘₂ e') tf
  ziplem-ap2 wt m DoRefl = DoRefl
  ziplem-ap2 wt m (DoAna x d) = DoSynth (SAZipApAna m wt x) (ziplem-ap2 wt m d)

  -- todo: why is this easier with functional erasure?
  ziplem-nehole-a : ∀{Γ e e' L t t'} →
                (Γ ⊢ e ◆e => t) →
                runsynth Γ e t L e' t' →
                runsynth Γ <| e |> <||> L <| e' |> <||>
  ziplem-nehole-a wt DoRefl = DoRefl
  ziplem-nehole-a wt (DoSynth {e = e} x d) =
    DoSynth (SAZipHole (rel◆ e) wt x) (ziplem-nehole-a (actsense1 (rel◆ e) (rel◆ _) x wt) d)


  erase-in-hole : ∀ {e e'} → erase-e e e' → erase-e <| e |> <| e' |>
  erase-in-hole (EENEHole er) = EENEHole (erase-in-hole er)
  erase-in-hole x = EENEHole x

  -- todo: why is this easier with functional erasure? which one of these
  -- do i really need? currently only use d.
  ziplem-nehole-b : ∀{Γ e e' L t t'} →
                (Γ ⊢ e ◆e => t) →
                runsynth Γ e t L e' t' →
                runana Γ <| e |> L <| e' |> t'
  ziplem-nehole-b wt DoRefl = DoRefl
  ziplem-nehole-b wt (DoSynth {e = e} x d) =
                     DoAna (AASubsume {e◆ = <| e ◆e |>}
                          (erase-in-hole (rel◆ _)) (SNEHole wt) (SAZipHole (rel◆ _) wt x) TCHole1)
                               (ziplem-nehole-b (actsense1 (rel◆ _) (rel◆ _) x wt) d)

  ziplem-nehole-c : ∀{Γ e e' L t t'} →
                (Γ ⊢ e ◆e => t) →
                runsynth Γ e t L e' t' →
                runana Γ <| e |> L <| e' |> <||>
  ziplem-nehole-c wt DoRefl = DoRefl
  ziplem-nehole-c wt (DoSynth x rs) =
                     DoAna (AASubsume
                           (erase-in-hole (rel◆ _)) (SNEHole wt) (SAZipHole (rel◆ _) wt x) TCHole2)
                              (ziplem-nehole-c (actsense1 (rel◆ _) (rel◆ _) x wt) rs)

  ziplem-nehole-d : ∀{Γ e e' L t t' t''} →
                (Γ ⊢ e ◆e => t) →
                (t'' ~ t') →
                runsynth Γ e t L e' t' →
                runana Γ <| e |> L <| e' |> t''
  ziplem-nehole-d wt c DoRefl = DoRefl
  ziplem-nehole-d wt c (DoSynth x rs) =
                     DoAna (AASubsume (erase-in-hole (rel◆ _)) (SNEHole wt) (SAZipHole (rel◆ _) wt x) TCHole1)
                           (ziplem-nehole-d (actsense1 (rel◆ _) (rel◆ _) x wt) c rs)


  -- because the point of the reachability theorems is to show that we
  -- didn't forget to define any of the action semantic cases, it's
  -- important that theorems include the fact that the witness only uses
  -- move -- otherwise, you could cheat by just prepending [ del ] to the
  -- list produced by constructability. constructability does also use
  -- some, but not all, of the possible movements, so this would no longer
  -- demonstrate the property we really want. to that end, we define a
  -- predicate on lists that they contain only (move _) and that the
  -- various things above that produce the lists we use have this property.

  -- predicate
  data movements : List action → Set where
    AM:: : {L : List action} {δ : direction}
              → movements L
              → movements ((move δ) :: L)
    AM[] : movements []

  -- movements breaks over the list monoid, as expected
  movements++ : {l1 l2 : List action} → movements l1 → movements l2 →
                                        movements (l1 ++ l2)
  movements++ (AM:: m1) m2 = AM:: (movements++ m1 m2)
  movements++ AM[] m2 = m2

open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase

module checks where
  -- theorem: movement doesn't change the term other than moving the focus around.
  moveerase : {e e' : ê} {δ : direction} {t : τ̇} →
            (e + move δ +>e e') →
            (e ◆e) == (e' ◆e)
  moveerase EMAscFirstChild = refl
  moveerase EMAscParent1 = refl
  moveerase EMAscParent2 = refl
  moveerase EMAscNextSib = refl
  moveerase EMLamFirstChild = refl
  moveerase EMLamParent = refl
  moveerase EMPlusFirstChild = refl
  moveerase EMPlusParent1 = refl
  moveerase EMPlusParent2 = refl
  moveerase EMPlusNextSib = refl
  moveerase EMApFirstChild = refl
  moveerase EMApParent1 = refl
  moveerase EMApParent2 = refl
  moveerase EMApNextSib = refl
  moveerase EMNEHoleFirstChild = refl
  moveerase EMNEHoleParent = refl


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
  -- related in a larger context without disrupting that larger context.
  --
  -- algorithmically, these amount to a checksum on the zipper actions; by
  -- iterating the action semantics, we need to show that they interplay in
  -- the right way, which is congruence.

  runtype-cong1 : ∀ {t1 t1' t2 L } →
            runtype t1' L t1 →
            runtype (t1' ==>₁ t2) L (t1 ==>₁ t2)
  runtype-cong1 DoRefl = DoRefl
  runtype-cong1 (DoType x L') = DoType (TMZip1 x) (runtype-cong1 L')

  runtype-cong2 : ∀ {t1 t2 t2' L } →
            runtype t2' L t2 →
            runtype (t1 ==>₂ t2') L (t1 ==>₂ t2)
  runtype-cong2 DoRefl = DoRefl
  runtype-cong2 (DoType x L') = DoType (TMZip2 x) (runtype-cong2 L')

  lem-tscong : ∀ {L t t' Γ} →
               runtype t L t' →
               runsynth Γ (<||> ·:₂ t) (t ◆t) L (<||> ·:₂ t') (t' ◆t)
  lem-tscong DoRefl = DoRefl
  lem-tscong (DoType x rt) with lem-tscong rt
  ... | ih = DoSynth (SAZipAsc2 x (ASubsume SEHole TCHole1)) ih


  lem-anasynthasc : ∀{Γ t L e e'} →
        runana Γ e L e' t →
        runsynth Γ (e ·:₁ t) t L (e' ·:₁ t) t
  lem-anasynthasc DoRefl = DoRefl
  lem-anasynthasc (DoAna a r) = DoSynth (SAZipAsc1 a) (lem-anasynthasc r)

  ana-lam-cong : ∀ {Γ x e t t1 t2 L e'} →
                   x # Γ →
                   t ▸arr (t1 ==> t2) →
                   runana (Γ ,, (x , t1)) e L e' t2 →
                   runana Γ (·λ x e) L (·λ x e') t
  ana-lam-cong a m DoRefl = DoRefl
  ana-lam-cong a m (DoAna x₁ d) =  DoAna (AAZipLam a m x₁) (ana-lam-cong a m d)

  synth-ana-plus1-cong : ∀{ Γ e L e' f} →
                       runana Γ e L e' num →
                       runsynth Γ (e ·+₁ f) num L (e' ·+₁ f) num
  synth-ana-plus1-cong DoRefl = DoRefl
  synth-ana-plus1-cong (DoAna x d) = DoSynth (SAZipPlus1 x) (synth-ana-plus1-cong d)

  synth-ana-plus2-cong : ∀{ Γ e L e' f} →
                       runana Γ e L e' num →
                       runsynth Γ (f ·+₂ e) num L (f ·+₂ e') num
  synth-ana-plus2-cong DoRefl = DoRefl
  synth-ana-plus2-cong (DoAna x d) = DoSynth (SAZipPlus2 x) (synth-ana-plus2-cong d)

  synth-ana-ap2-cong : ∀{ Γ e L e' t t' f tf} →
                       Γ ⊢ f => t' →
                       t' ▸arr (t ==> tf) →
                       runana Γ e L e' t →
                       runsynth Γ (f ∘₂ e) tf L (f ∘₂ e') tf
  synth-ana-ap2-cong wt m DoRefl = DoRefl
  synth-ana-ap2-cong wt m (DoAna x d) = DoSynth (SAZipApAna m wt x) (synth-ana-ap2-cong wt m d)





  -- if there is a list of actions that builds a type, running that list
  -- from the empty hole in focus really does produce the target type.
  -- run-subsume :  ∀ { Γ L e e' t t' } →
  --                runsynth Γ e t L e' t' →
  --                runana Γ e L e' t'
  -- run-subsume DoRefl = DoRefl
  -- run-subsume (DoSynth x act) = {!!}

  -- runsynth-congap1 : ∀{Γ e1 t L e1' e2 t'} →
  --                   runsynth Γ e1 t' L e1' t' →
  --                   runsynth Γ (e1 ∘₁ e2) t L (e1' ∘₁ e2) t
  -- runsynth-congap1 DoRefl = DoRefl
  -- runsynth-congap1 (DoSynth x d) = DoSynth {!!} {!!}

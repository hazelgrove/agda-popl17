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
  -- algorithmically, these amount to a checksum on the zipper actions; by
  -- iterating the action semantics, we need to show that they interplay in
  -- the right way, which is congruence. the only check the zipper actions
  -- they happen to be include, however, which is driven by the particular
  -- lists we use in the proof of contructability.

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

  ziplem-asc1 : ∀{Γ t L e e'} →
        runana Γ e L e' t →
        runsynth Γ (e ·:₁ t) t L (e' ·:₁ t) t
  ziplem-asc1 DoRefl = DoRefl
  ziplem-asc1 (DoAna a r) = DoSynth (SAZipAsc1 a) (ziplem-asc1 r)

  -- this one is very specific to the particular proof of constructability.
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

  ziplem-nehole-a : ∀{Γ e e' L t t'} →
                (Γ ⊢ e ◆e => t) →
                runsynth Γ e t L e' t' →
                runsynth Γ <| e |> <||> L <| e' |> <||>
  ziplem-nehole-a wt DoRefl = DoRefl
  ziplem-nehole-a wt (DoSynth {e = e} x d) =
    DoSynth (SAZipHole (rel◆ e) wt x) (ziplem-nehole-a (actsense1 (rel◆ e) (rel◆ _) x wt) d)

  ziplem-nehole-b : ∀{Γ e e' L t t'} →
                (Γ ⊢ e ◆e => t) →
                runsynth Γ e t L e' t' →
                runana Γ <| e |> L <| e' |> t'
  ziplem-nehole-b wt DoRefl = DoRefl
  ziplem-nehole-b wt (DoSynth {e = e} x d) = DoAna (AASubsume {e◆ = <| e ◆e |>} (lemX (rel◆ _)) (SNEHole wt) (SAZipHole (rel◆ _) wt x) TCHole1)
                                  (ziplem-nehole-b (actsense1 (rel◆ _) (rel◆ _) x wt) d)
   where
     lemX : ∀ {e e'} → erase-e e e' → erase-e <| e |> <| e' |>
     lemX (EENEHole er) = EENEHole (lemX er)
     lemX x = EENEHole x


  -- runsynth-unicity : ∀{Γ t0 t' e L e' e'' t''} →
  --     runsynth Γ e t0 L e' t' →
  --     runsynth Γ e t0 L e'' t'' →
  --     t' == t''
  -- runsynth-unicity DoRefl DoRefl = refl
  -- runsynth-unicity (DoSynth x rs) (DoSynth x' rs')
  --   with actsense1 {!!} {!!} x {!!} | actsense1 {!!} {!!} x' {!!}
  -- ... | wt1 | wt2 with synthunicity wt1 wt2
  -- ... | refl = {!runsynth-unicity rs !}

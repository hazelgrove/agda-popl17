open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module reachability where
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
  movements++ : {l1 l2 : List action} → movements l1 → movements l2 → movements (l1 ++ l2)
  movements++ (AM:: am1) (AM:: am2) = AM:: (movements++ am1 (AM:: am2))
  movements++ (AM:: am1) AM[] = AM:: (movements++ am1 AM[])
  movements++ AM[] (AM:: am2) = AM:: am2
  movements++ AM[] AM[] = AM[]

  -- algorithmically, we break reachability into two halves: first you
  -- produce a list of actions that are all "move parent" to pull the focus
  -- to the very top of the expression in question. then, you go back down
  -- into the expression with a sequence of move firstChild and move
  -- nextSibs as appropriate. the append of these two lists will reach from
  -- one expression to the other.
  --
  -- there may well be a shorter list of actions that does the same thing;
  -- the expression with top-level focus may not be the Least Common
  -- Ancestor in the expression tree of the given pair. however, the work
  -- of this less minimal thing and corresponding size of the proof term is
  -- still bounded linearly by the size of the expression, and is far
  -- easier to maniupulate judgementally.

  reachup-type : {t : τ̂} {t' : τ̇} →
              erase-t t t' →
              Σ[ L ∈ List action ] (runtype t L (▹ t' ◃) × movements L)
  reachup-type ETTop = [] , DoRefl , AM[]
  reachup-type (ETArrL er) with reachup-type er
  ... | (l , ih , m ) = l ++ [ move parent ] ,
                        runtype++ (ziplem-tm1 ih) (DoType TMParent1 DoRefl) ,
                        movements++ m (AM:: AM[])
  reachup-type (ETArrR er) with reachup-type er
  ... | (l , ih , m ) = l ++ [ move parent ] ,
                        runtype++ (ziplem-tm2 ih) (DoType TMParent2 DoRefl) ,
                        movements++ m (AM:: AM[])

  -- runsynth-type : ∀{t L t' Γ e ter} →
  --                 Γ ⊢ e <= ter →
  --                 erase-t t ter →
  --                 runtype t L t' →
  --                 runsynth Γ (e ·:₂ t) ter L (e ·:₂ t') ter
  -- runsynth-type wt er rt = {!!}

  -- synth-ap1-cong : ∀{Γ e t t1 t2 L e' f er} →
  --                      erase-e e er →
  --                      Γ ⊢ er => t →
  --                      Γ ⊢ f <= t2 →
  --                      t ▸arr (t2 ==> t1) →
  --                      runsynth Γ e t L e' t →
  --                      runsynth Γ (e ∘₁ f) t1 L (e' ∘₁ f) t1
  -- synth-ap1-cong er wt1 wt2 m rs = {!!}

  mutual
    reachup-synth : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      erase-e e e' →
                      Γ ⊢ e' => t →
                     Σ[ L ∈ List action ] runsynth Γ e t L ▹ e' ◃ t × movements L
    reachup-synth er wt = {!!}

    reachup-ana : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      erase-e e e' →
                      Γ ⊢ e' <= t →
                      Σ[ L ∈ List action ] runana Γ e L ▹ e' ◃ t × movements L
    reachup-ana er wt = {!!}

  reachdown-type : {t : τ̇} {t' : τ̂} → (p : erase-t t' t) →
                     Σ[ L ∈ List action ] runtype (▹ t ◃) L t' × movements L
  reachdown-type ETTop = {!!}
  reachdown-type (ETArrL er) = {!!}
  reachdown-type (ETArrR er) = {!!}

  mutual
    reachdown-synth : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      (p : erase-e e e') →
                      (wt : Γ ⊢ e' => t) →
                      Σ[ L ∈ List action ] runsynth Γ ▹ e' ◃ t L e t × movements L
    reachdown-synth = {!!}

    reachdown-ana : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      (p : erase-e e e') →
                      (wt : Γ ⊢ e' <= t) →
                      Σ[ L ∈ List action ] runana Γ ▹ e' ◃ L e  t × movements L
    reachdown-ana = {!!}

  -- this is the final statement of the reachability triplet. the movement
  -- between judgemental and metafunctional erasure happens internally to
  -- theses statements to present a consistent interface with the text of
  -- the paper, while also allowing easy pattern matching in the proofs.
  --
  -- the justification for these statements, intuitively, is that focus
  -- cannot change the type of things because the typing judgement is
  -- defined on the focus-erased terms and types. so if two terms agree up
  -- to erasure, they must have the exact same type in the same context,
  -- not merely a compatible one in an extension or any other weakening of
  -- the statement. these are lemmas which are currently not proven. TODO?

  reachability-types : (t1 t2 : τ̂) → (t1 ◆t) == (t2 ◆t) →
                           Σ[ L ∈ List action ] runtype t1 L t2 × movements L
  reachability-types t1 t2 eq with ◆erase-t t1 (t2 ◆t) eq | ◆erase-t t2 (t1 ◆t) (! eq)
  ... | er1 | er2 with reachup-type er1 | reachdown-type er2
  ... | (lup , rup , mvup)  | (ldwn , rdwn , mvdwn) =
        lup ++ ldwn ,
        runtype++ rup (tr (λ x → runtype ▹ x ◃ ldwn t2) eq rdwn) ,
        movements++ mvup mvdwn

  reachability-synth : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e => t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runsynth Γ e1 t L e2 t × movements L
  reachability-synth Γ t e1 e2 wt1 eq with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-synth er1 (tr (λ x → Γ ⊢ x => t) eq wt1) | reachdown-synth er2 wt1
  ... | (lup , rup , mvup)  | (ldwn , rdwn , mvdwn) =
      (lup ++ ldwn) ,
      runsynth++ rup (tr (λ x → runsynth Γ ▹ x ◃ t ldwn e2 t) eq rdwn) ,
      movements++ mvup mvdwn

  reachability-ana : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e <= t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runana Γ e1 L e2 t × movements L
  reachability-ana Γ t e1 e2 wt1 eq with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-ana er1 (tr (λ x → Γ ⊢ x <= t) eq wt1) | reachdown-ana er2 wt1
  ... | (lup , rup , mvup)  | (ldwn , rdwn , mvdwn) =
      lup ++ ldwn ,
      (runana++ rup (tr (λ x → runana Γ ▹ x ◃ ldwn e2 t) eq rdwn)) ,
      (movements++ mvup mvdwn)

open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks
open import moveerase

module reachability where
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

  ziplem-moves-ap1 : ∀{Γ l e1 e1' e2 t t'} →
                   movements l →
                   runsynth Γ e1 t l e1' t →
                   runsynth Γ (e1 ∘₁ e2) t' l (e1' ∘₁ e2) t'
  ziplem-moves-ap1 _ DoRefl = DoRefl
  ziplem-moves-ap1 (AM:: m) (DoSynth x rs) =
                   DoSynth (SAZipApArr {!!} {!!} {!!} x {!!})
                           (ziplem-moves-ap1 m {!rs!})


  mutual
    reachup-synth : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      erase-e e e' →
                      Γ ⊢ e' => t →
                     Σ[ L ∈ List action ] runsynth Γ e t L ▹ e' ◃ t × movements L
    reachup-synth (EELam _) ()
    reachup-synth EETop _ = [] , DoRefl , AM[]
    reachup-synth (EEAscL er) (SAsc x) with reachup-ana er x
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ (ziplem-asc1 ih) (DoSynth (SAMove EMAscParent1) DoRefl) ,
                       movements++ m (AM:: AM[])
    reachup-synth (EEAscR er) (SAsc x₁) with reachup-type er
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ {L1 = l} (ziplem-moves-asc2 m er x₁ ih) (DoSynth (SAMove EMAscParent2) DoRefl) ,
                       movements++ m (AM:: AM[])
    reachup-synth (EEApL er) (SAp wt x x₁) with reachup-synth er wt
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ {L1 = l} {!!} (DoSynth (SAMove EMApParent1) DoRefl) ,
                       movements++ m (AM:: AM[])
    reachup-synth (EEApR er) (SAp wt x x₁) with reachup-ana er x₁
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ (ziplem-ap2 wt x ih) (DoSynth (SAMove EMApParent2) DoRefl) ,
                       movements++ m (AM:: AM[])
    reachup-synth (EEPlusL er) (SPlus x x₁) with reachup-ana er x
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ (ziplem-plus1 ih) (DoSynth (SAMove EMPlusParent1) DoRefl) ,
                       movements++ m (AM:: AM[])
    reachup-synth (EEPlusR er) (SPlus x x₁) with reachup-ana er x₁
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ (ziplem-plus2 ih) (DoSynth (SAMove EMPlusParent2) DoRefl) ,
                       movements++ m (AM:: AM[])
    reachup-synth (EENEHole er) (SNEHole wt) with reachup-synth er wt
    ... | l , ih , m = l ++ [ move parent ] ,
                       runsynth++ (ziplem-nehole-a (lem-erase-synth er wt) ih) (DoSynth (SAMove EMNEHoleParent) DoRefl) ,
                       movements++ m (AM:: AM[])

    reachup-ana : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      erase-e e e' →
                      Γ ⊢ e' <= t →
                      Σ[ L ∈ List action ] runana Γ e L ▹ e' ◃ t × movements L
    reachup-ana EETop _ = [] , DoRefl , AM[]
    reachup-ana er (ASubsume x x₁) with reachup-synth er x
    ... | l , ih , m = l ,
                       {!!} ,
                       m
    reachup-ana (EELam er) (ALam x₁ x₂ wt) with reachup-ana er wt
    ... | l , ih , m = l ++ [ move parent ] ,
                       runana++ (ziplem-lam x₁ x₂ ih) (DoAna (AAMove EMLamParent) DoRefl) ,
                       movements++ m (AM:: AM[])


  --------------------------


  reachdown-type : {t : τ̇} {t' : τ̂} → (p : erase-t t' t) →
                     Σ[ L ∈ List action ] runtype (▹ t ◃) L t' × movements L
  reachdown-type ETTop = [] , DoRefl , AM[]
  reachdown-type (ETArrL er) with reachdown-type er
  ... | (l , ih , m ) = move firstChild :: l ,
                        DoType TMFirstChild (ziplem-tm1 ih) ,
                        AM:: m
  reachdown-type (ETArrR er) with reachdown-type er
  ... | (l , ih , m ) = move firstChild :: move nextSib :: l ,
                        DoType TMFirstChild (DoType TMNextSib (ziplem-tm2 ih)) ,
                        AM:: (AM:: m)

  mutual
    reachdown-synth : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      (p : erase-e e e') →
                      (wt : Γ ⊢ e' => t) →
                      Σ[ L ∈ List action ] runsynth Γ ▹ e' ◃ t L e t × movements L
    reachdown-synth (EELam _) ()
    reachdown-synth EETop _ = [] , DoRefl , AM[]
    reachdown-synth (EEAscL er) (SAsc x) with reachdown-ana er x
    ... | l , ih , m = move firstChild :: l ,
                       DoSynth (SAMove EMAscFirstChild) (ziplem-asc1 ih) ,
                       AM:: m
    reachdown-synth (EEAscR er) (SAsc x₁) with reachdown-type er
    ... | l , ih , m = move firstChild :: move nextSib :: l ,
                       DoSynth (SAMove EMAscFirstChild) (DoSynth (SAMove EMAscNextSib) (ziplem-moves-asc2 m ETTop x₁ ih)) ,
                       AM:: (AM:: m)
    reachdown-synth (EEApL er) (SAp wt x x₁) with reachdown-synth er wt
    ... | l , ih , m = move firstChild :: l ,
                       DoSynth (SAMove EMApFirstChild) {!!} ,
                       AM:: m
    reachdown-synth (EEApR er) (SAp wt x x₁) with reachdown-ana er x₁
    ... | l , ih , m = move firstChild :: move nextSib :: l ,
                       DoSynth (SAMove EMApFirstChild) (DoSynth (SAMove EMApNextSib) (ziplem-ap2 wt x ih)) ,
                       AM:: (AM:: m)
    reachdown-synth (EEPlusL er) (SPlus x x₁) with reachdown-ana er x
    ... | l , ih , m = move firstChild :: l ,
                       DoSynth (SAMove EMPlusFirstChild) (ziplem-plus1 ih) ,
                       AM:: m
    reachdown-synth (EEPlusR er) (SPlus x x₁) with reachdown-ana er x₁
    ... | l , ih , m = move firstChild :: move nextSib :: l ,
                       DoSynth (SAMove EMPlusFirstChild) (DoSynth (SAMove EMPlusNextSib) (ziplem-plus2 ih)) ,
                       AM:: (AM:: m)
    reachdown-synth (EENEHole er) (SNEHole wt) with reachdown-synth er wt
    ... | l , ih , m = move firstChild :: l ,
                       DoSynth (SAMove EMNEHoleFirstChild) (ziplem-nehole-a wt ih) ,
                       AM:: m

    reachdown-ana : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      (p : erase-e e e') →
                      (wt : Γ ⊢ e' <= t) →
                      Σ[ L ∈ List action ] runana Γ ▹ e' ◃ L e  t × movements L
    reachdown-ana EETop _ = [] , DoRefl , AM[]
    reachdown-ana er (ASubsume x x₁) with reachdown-synth er x
    ... | l , ih , m = l ,
                       {!!} ,
                       m
    reachdown-ana (EELam er) (ALam x₁ x₂ wt) with reachdown-ana er wt
    ... | l , ih , m = move firstChild :: l ,
                       DoAna (AAMove EMLamFirstChild) (ziplem-lam x₁ x₂ ih) ,
                       AM:: m


  --------------------------


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
  reachability-types t1 t2 eq
    with ◆erase-t t1 (t2 ◆t) eq | ◆erase-t t2 (t1 ◆t) (! eq)
  ... | er1 | er2 with reachup-type er1 | reachdown-type er2
  ... | (lup , rup , mvup)  | (ldwn , rdwn , mvdwn) =
        lup ++ ldwn ,
        runtype++ rup (tr (λ x → runtype ▹ x ◃ ldwn t2) eq rdwn) ,
        movements++ mvup mvdwn

  reachability-synth : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e => t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runsynth Γ e1 t L e2 t × movements L
  reachability-synth Γ t e1 e2 wt1 eq
    with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-synth er1 (tr (λ x → Γ ⊢ x => t) eq wt1)
                     | reachdown-synth er2 wt1
  ... | (lup , rup , mvup)  | (ldwn , rdwn , mvdwn) =
      (lup ++ ldwn) ,
      runsynth++ rup (tr (λ x → runsynth Γ ▹ x ◃ t ldwn e2 t) eq rdwn) ,
      movements++ mvup mvdwn

  reachability-ana : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e <= t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runana Γ e1 L e2 t × movements L
  reachability-ana Γ t e1 e2 wt1 eq
    with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-ana er1 (tr (λ x → Γ ⊢ x <= t) eq wt1)
                     | reachdown-ana er2 wt1
  ... | (lup , rup , mvup)  | (ldwn , rdwn , mvdwn) =
      lup ++ ldwn ,
      (runana++ rup (tr (λ x → runana Γ ▹ x ◃ ldwn e2 t) eq rdwn)) ,
      (movements++ mvup mvdwn)

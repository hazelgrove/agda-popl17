open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks

module reachability where

------- reachability

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

  moveup-t : τ̂ → List action
  moveup-t ▹ _ ◃      = []
  moveup-t (t ==>₁ _) = moveup-t t ++ [ move parent ]
  moveup-t (_ ==>₂ t) = moveup-t t ++ [ move parent ]

  moveup-e : ê → List action
  moveup-e ▹ _ ◃      = []
  moveup-e (e ·:₁ _)  = moveup-e e ++ [ move parent ]
  moveup-e (_ ·:₂ t)  = moveup-t t ++ [ move parent ]
  moveup-e (·λ _ e)   = moveup-e e ++ [ move parent ]
  moveup-e (e ∘₁ _)   = moveup-e e ++ [ move parent ]
  moveup-e (_ ∘₂ e)   = moveup-e e ++ [ move parent ]
  moveup-e (e ·+₁ _)  = moveup-e e ++ [ move parent ]
  moveup-e (_ ·+₂ e)  = moveup-e e ++ [ move parent ]
  moveup-e <| e |>    = moveup-e e ++ [ move parent ]


  reachup-type : {t : τ̂} {t' : τ̇} →
              erase-t t t' →
              runtype t (moveup-t t) (▹ t' ◃)
  reachup-type ETTop = DoRefl
  reachup-type (ETArrL tr) with reachup-type tr
  ... | ih = runtype++ (runtype-cong1 ih) (DoType TMParent1 DoRefl)
  reachup-type (ETArrR tr) with reachup-type tr
  ... | ih = runtype++ (runtype-cong2 ih) (DoType TMParent2 DoRefl)

  runsynth-type : ∀{t L t' Γ e ter} →
                  Γ ⊢ e <= ter →
                  erase-t t ter →
                  runtype t L t' →
                  runsynth Γ (e ·:₂ t) ter L (e ·:₂ t') ter
  runsynth-type _ _ DoRefl = DoRefl
  runsynth-type wt er (DoType x d) with erase-t◆ er
  ... | refl = DoSynth {!SAZipAsc2  !} (runsynth-type {!!}  {!!} d)

  mutual
    reachup-synth : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      erase-e e e' →
                      Γ ⊢ e' => t →
                      runsynth Γ e t (moveup-e e) ▹ e' ◃ t
    reachup-synth (EELam er) ()
    reachup-synth EETop _ = DoRefl
    reachup-synth (EEAscL er) (SAsc x) = {!!}
    reachup-synth (EEAscR x) (SAsc x₁) with reachup-type x
    ... | ih = runsynth++ (runsynth-type x₁ x ih) (DoSynth (SAMove EMAscParent2) DoRefl)
    reachup-synth (EEApL er) (SAp wt m x) with reachup-synth er wt
    ... | ih = runsynth++ {!ih!} (DoSynth (SAMove EMApParent1) DoRefl)
    reachup-synth (EEApR er) (SAp wt m x) = {!!}
    reachup-synth (EEPlusL er) (SPlus x x₁) = {!!}
    reachup-synth (EEPlusR er) (SPlus x x₁) = {!!}
    reachup-synth (EENEHole er) (SNEHole wt) = {!!}

    reachup-ana : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      erase-e e e' →
                      Γ ⊢ e' <= t →
                      runana Γ e (moveup-e e) ▹ e' ◃ t
    reachup-ana = {!!}

  movedown-t : (t : τ̇) (t' : τ̂) (p : erase-t t' t) → List action
  movedown-t _ ▹ ._ ◃ ETTop = []
  movedown-t (t ==> t₁) (t' ==>₁ .t₁) (ETArrL p) = move firstChild :: (movedown-t _ _ p)
  movedown-t (t ==> t₁) (.t ==>₂ t') (ETArrR p) = move firstChild :: move nextSib :: movedown-t _ _ p

  movedown-e : (e : ė) (e' : ê) (p : erase-e e' e) → List action
  movedown-e _ ▹ ._ ◃  EETop = []
  movedown-e (e ·: x)  (e' ·:₁ .x)  (EEAscL er)  = move firstChild :: movedown-e _ _ er
  movedown-e (e ·: x)  (.e ·:₂ x₁)  (EEAscR tr)  = move firstChild :: move nextSib :: movedown-t _ _ tr
  movedown-e (·λ x e)  (·λ .x e')   (EELam er)   = move firstChild :: movedown-e _ _ er
  movedown-e (e ·+ e₁) (e' ·+₁ .e₁) (EEPlusL er) = move firstChild :: movedown-e _ _ er
  movedown-e (e ·+ e₁) (.e ·+₂ e')  (EEPlusR er) = move firstChild :: move nextSib ::  movedown-e _ _ er
  movedown-e <| e |>   <| e' |>     (EENEHole er) = move firstChild :: movedown-e _ _ er
  movedown-e (e ∘ e₁)  (e' ∘₁ .e₁)  (EEApL er)   = move firstChild :: movedown-e _ _ er
  movedown-e (e ∘ e₁)  (.e ∘₂ e')   (EEApR er)   = move firstChild :: move nextSib :: movedown-e _ _ er

  reachdown-type : {t : τ̇} {t' : τ̂} → (p : erase-t t' t) →
                     runtype (▹ t ◃) (movedown-t t t' p) t'
  reachdown-type ETTop = DoRefl
  reachdown-type (ETArrL p) with reachdown-type p
  ... | ih = DoType TMFirstChild (runtype-cong1 ih)
  reachdown-type (ETArrR p) with reachdown-type p
  ... | ih = DoType TMFirstChild (DoType TMNextSib (runtype-cong2 ih))

  mutual
    reachdown-synth : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      (p : erase-e e e') →
                      (wt : Γ ⊢ e' => t)
                     → runsynth Γ ▹ e' ◃ t (movedown-e e' e p) e t
    reachdown-synth (EELam p) ()
    reachdown-synth EETop _ = DoRefl
    reachdown-synth (EEAscL p) (SAsc x) = {!!}
    reachdown-synth (EEAscR x) (SAsc x₁) = {!!}
    reachdown-synth (EEApL p) (SAp wt m  x) = {!!}
    reachdown-synth (EEApR p) (SAp wt m x) = {!!}
    reachdown-synth (EEPlusL p) (SPlus x x₁) = {!!}
    reachdown-synth (EEPlusR p) (SPlus x x₁) = {!!}
    reachdown-synth (EENEHole p) (SNEHole wt) = {!!}

    reachdown-ana : {Γ : ·ctx} {e : ê} {t : τ̇} {e' : ė} →
                      (p : erase-e e e') →
                      (wt : Γ ⊢ e' <= t)
                     → runana Γ ▹ e' ◃ (movedown-e e' e p) e  t
    reachdown-ana EETop _ = DoRefl
    reachdown-ana (EEAscL p) (ASubsume x x₁) = {!reachdown-synth ? x!}
    reachdown-ana (EEAscR x) (ASubsume x₁ x₂) = {!!}
    reachdown-ana (EELam p) (ASubsume x₁ x₂) = {!!}
    reachdown-ana (EEApL p) (ASubsume x x₁) = {!!}
    reachdown-ana (EEApR p) (ASubsume x x₁) = {!!}
    reachdown-ana (EEPlusL p) (ASubsume x x₁) = {!!}
    reachdown-ana (EEPlusR p) (ASubsume x x₁) = {!!}
    reachdown-ana (EENEHole p) (ASubsume x x₁) = {!!}
    reachdown-ana (EELam p) (ALam m x₁ wt) = {!!}

  -- because the point of the reachability theorems is to show that we
  -- didn't forget to define any of the action semantic cases, it's
  -- important that theorems include the fact that the witness only uses
  -- move -- otherwise, you could prepend [ del ] to the list produced by
  -- constructability. constructability does also use some, but not all, of
  -- the possible movements, so this would no longer demonstrate the
  -- property we really want. to that end, we define a predicate on lists
  -- that they contain only (move _) and that the various things above that
  -- produce the lists we use have this property.

  -- predicate
  data allmoves : List action → Set where
    AM:: : {L : List action} {δ : direction}
              → allmoves L
              → allmoves ((move δ) :: L)
    AM[] : allmoves []

  allmoves++ : {l1 l2 : List action} → allmoves l1 → allmoves l2 → allmoves (l1 ++ l2)
  allmoves++ (AM:: am1) (AM:: am2) = AM:: (allmoves++ am1 (AM:: am2))
  allmoves++ (AM:: am1) AM[] = AM:: (allmoves++ am1 AM[])
  allmoves++ AM[] (AM:: am2) = AM:: am2
  allmoves++ AM[] AM[] = AM[]

  allmoves-moveup-t : (t : τ̂) → allmoves (moveup-t t)
  allmoves-moveup-t ▹ x ◃ = AM[]
  allmoves-moveup-t (t ==>₁ x) = allmoves++ (allmoves-moveup-t t) (AM:: AM[])
  allmoves-moveup-t (x ==>₂ t) = allmoves++ (allmoves-moveup-t t) (AM:: AM[])

  allmoves-moveup-e : (e : ê) → allmoves (moveup-e e)
  allmoves-moveup-e ▹ x ◃ = AM[]
  allmoves-moveup-e (e ·:₁ x) = allmoves++ (allmoves-moveup-e e) (AM:: AM[])
  allmoves-moveup-e (x ·:₂ x₁) = allmoves++ (allmoves-moveup-t x₁) (AM:: AM[])
  allmoves-moveup-e (·λ x e) = allmoves++ (allmoves-moveup-e e) (AM:: AM[])
  allmoves-moveup-e (e ∘₁ x) = allmoves++ (allmoves-moveup-e e) (AM:: AM[])
  allmoves-moveup-e (x ∘₂ e) = allmoves++ (allmoves-moveup-e e) (AM:: AM[])
  allmoves-moveup-e (e ·+₁ x) = allmoves++ (allmoves-moveup-e e) (AM:: AM[])
  allmoves-moveup-e (x ·+₂ e) = allmoves++ (allmoves-moveup-e e) (AM:: AM[])
  allmoves-moveup-e <| e |> = allmoves++ (allmoves-moveup-e e) (AM:: AM[])

  allmoves-movedown-t : (t : τ̇) (t' : τ̂) (p : erase-t t' t) → allmoves(movedown-t t t' p)
  allmoves-movedown-t _ ▹ ._ ◃ ETTop = AM[]
  allmoves-movedown-t (t ==> t₁) (t' ==>₁ .t₁) (ETArrL p) = AM:: (allmoves-movedown-t t t' p)
  allmoves-movedown-t (t ==> t₁) (.t ==>₂ t') (ETArrR p) = AM:: (AM:: (allmoves-movedown-t t₁ t' p))

  allmoves-movedown-e :(e : ė) (e' : ê) (p : erase-e e' e) → allmoves(movedown-e e e' p)
  allmoves-movedown-e _ ▹ ._ ◃ EETop = AM[]
  allmoves-movedown-e (e ·: x) (e' ·:₁ .x) (EEAscL p) = AM:: (allmoves-movedown-e e e' p)
  allmoves-movedown-e (e ·: x) (.e ·:₂ x₁) (EEAscR x₂) = AM:: (AM:: (allmoves-movedown-t x x₁ x₂))
  allmoves-movedown-e (·λ x e) (·λ .x e') (EELam p) = AM:: (allmoves-movedown-e e e' p)
  allmoves-movedown-e (e ·+ e₁) (e' ·+₁ .e₁) (EEPlusL p) = AM:: (allmoves-movedown-e e e' p)
  allmoves-movedown-e (e ·+ e₁) (.e ·+₂ e') (EEPlusR p) = AM:: (AM:: (allmoves-movedown-e e₁ e' p))
  allmoves-movedown-e <| e |> <| e' |> (EENEHole p) = AM:: (allmoves-movedown-e e e' p)
  allmoves-movedown-e (e ∘ e₁) (e' ∘₁ .e₁) (EEApL p) = AM:: (allmoves-movedown-e e e' p)
  allmoves-movedown-e (e ∘ e₁) (.e ∘₂ e') (EEApR p) = AM:: (AM:: (allmoves-movedown-e e₁ e' p))

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
                           Σ[ L ∈ List action ] runtype t1 L t2 × allmoves L
  reachability-types t1 t2 eq with ◆erase-t t1 (t2 ◆t) eq | ◆erase-t t2 (t1 ◆t) (! eq)
  ... | er1 | er2 with reachup-type er1 | reachdown-type er2
  ... | up  | down = moveup-t t1 ++ movedown-t (t1 ◆t) t2 er2 ,
                     (runtype++ up (tr (λ x → runtype ▹ x ◃ (movedown-t (t1 ◆t) t2 er2) t2) eq down)) ,
                     allmoves++ (allmoves-moveup-t t1) (allmoves-movedown-t (t1 ◆t) t2 er2)

  reachability-synth : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e => t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runsynth Γ e1 t L e2 t × allmoves L
  reachability-synth Γ t e1 e2 wt1 eq with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-synth er1 (tr (λ x → Γ ⊢ x => t) eq wt1) | reachdown-synth er2 wt1
  ... | up  | down = moveup-e e1 ++ movedown-e (e1 ◆e) e2 er2 ,
                     runsynth++ up (tr (λ x → runsynth Γ ▹ x ◃ t (movedown-e (e1 ◆e) e2 er2) e2 t) eq down),
                     allmoves++ (allmoves-moveup-e e1) (allmoves-movedown-e (e1 ◆e) e2 er2)

  reachability-ana : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e <= t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runana Γ e1 L e2 t × allmoves L
  reachability-ana Γ t e1 e2 wt1 eq with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-ana er1 (tr (λ x → Γ ⊢ x <= t) eq wt1) | reachdown-ana er2 wt1
  ... | up  | down = moveup-e e1 ++ movedown-e (e1 ◆e) e2 er2 ,
                     runana++ up (tr (λ x → runana Γ ▹ x ◃ (movedown-e (e1 ◆e) e2 er2) e2 t) eq down) ,
                     allmoves++ (allmoves-moveup-e e1) (allmoves-movedown-e (e1 ◆e) e2 er2)

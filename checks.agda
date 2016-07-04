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
  moveerase EMFHoleFirstChild = refl
  moveerase EMFHoleParent = refl

  ------- constructability

  -- todo: should there be construct hole forms? currently hole isn't a
  -- shape so you can't create it with an action, only by using the action
  -- semantics. but that means you can't build something like num ==> <||>,
  -- which is troubling. maybe the right thing to do in the build hole
  -- cases is just nothing at all.

  data buildtype : (t : τ̂) → List action → Set where
    BuildNum   : buildtype ▹ num ◃  [ construct num ]
    BuildTHole : buildtype ▹ <||> ◃ [ del ]
    BuildArr   : {t1 t2 : τ̇} {l1 l2 : List action}
                 → buildtype ▹ t1 ◃ l1
                 → buildtype ▹ t2 ◃ l2
                 → buildtype ▹ t1 ==> t2 ◃
                      (l1 ++ (construct arrow :: l2 ++ [ move parent ]))

  -- small example of a derivation for building a particular type.
  bt-ex : Σ[ l ∈ List action ] buildtype (▹ num ==> <||> ◃) l
  bt-ex = construct num :: construct arrow :: del :: move parent :: [] ,
         BuildArr  BuildNum
         BuildTHole

  -- todo: it's not clear if i can get away with not knowing the typing
  -- information here. the same action makes different expressions
  -- depending on if it's in a synthetic or analytic position given the
  -- paired action semantics judgements.
  --
  --  (Γ : ·ctx) (t : τ̇) (wt : (Γ ⊢ e => t) + (Γ ⊢ e <= t))
  --
  -- or, more realistically, will need two jugements, buildeana and
  -- buildesynth

  -- there's a hidden invariant here, which is that we always leave the
  -- focus at the top of the expression. this lets us prove later that we
  -- can build a specifc thing starting at the expression that's just a
  -- hole in focus.

  -- CURRENTLY DO NOT TRUST THAT THESE LISTS ARE CORRECT
  data buildexp : (e : ê) → List action → Set where
    BuildAsc : {e : ė} {t : τ̇} {l1 l2 : List action}
               → buildexp ▹ e ◃ l1
               → buildtype ▹ t ◃ l2
               → buildexp ▹ e ·: t ◃ (l1 ++ (construct asc :: l2 ++ [ move parent ]))
    BuildX : {x : Nat} → buildexp ▹ X x ◃  [ construct (var x) ]
    BuildLam : {x : Nat} {e : ė} {l : List action}
               → buildexp ▹ e ◃ l
               → buildexp ▹ ·λ x e ◃ [] -- stub
    BuildN : {n : Nat} → buildexp ▹ N n ◃ [ construct (numlit n) ]
    BuildPlus : {e1 e2 : ė} {l1 l2 : List action}
                 → buildexp ▹ e1 ◃ l1
                 → buildexp ▹ e2 ◃ l2
                 → buildexp ▹ e1 ·+ e2 ◃
                            (l1 ++ l2 ++ [ move parent ])
    BuildAp :  {e1 e2 : ė} {l1 l2 : List action}
                 → buildexp ▹ e1 ◃ l1
                 → buildexp ▹ e2 ◃ l2
                 → buildexp ▹ e1 ∘ e2 ◃
                            (l1 ++ l2 ++ [ move parent ])
    BuildEHole : buildexp ▹ <||> ◃ [ del ]
    BuildFHole : {e : ė} {l : List action} →
                 buildexp ▹ e ◃ l →
                 buildexp ▹ <| e |> ◃ [] -- stub

  -- taken together, these three theorems say that the build judgements
  -- have mode (∀, ∃), which is to say that they effectively define total
  -- functions and we didn't miss any cases.
  --
  -- note that they do *not* say anything whatsoever about whether the
  -- lists produced are remotely correct. the proofs have been written in a
  -- style that pins them least to the particular choice of lists of
  -- actions in the jugement -- agda unification will pick whatever lists
  -- are written allow and automatically adjust these to arbitrary changes
  -- in the judgement
  buildtype-mode : (t : τ̇) → Σ[ l ∈ List action ] buildtype ▹ t ◃ l
  buildtype-mode num  = _ , BuildNum
  buildtype-mode <||> = _ , BuildTHole
  buildtype-mode (t1 ==> t2) with buildtype-mode t1 | buildtype-mode t2
  ... | (_ , p1) | (_ , p2) = _ , BuildArr p1 p2

  mutual
    buildexp-mode-synth : {Γ : ·ctx} {e : ė} {t : τ̇} (wt : Γ ⊢ e => t) →
               Σ[ l ∈ List action ] buildexp ▹ e ◃ l
    buildexp-mode-synth (SAsc {t = t} d) with buildexp-mode-ana d | buildtype-mode t
    ... | (_ , p1) | (_ , p2) = _ ,  BuildAsc p1 p2
    buildexp-mode-synth (SVar _) = _ , BuildX
    buildexp-mode-synth (SAp d1 d2) with buildexp-mode-synth d1 | buildexp-mode-ana d2
    ... | (_ , p1) | (_ , p2) = _ , BuildAp p1 p2
    buildexp-mode-synth SNum = _ , BuildN
    buildexp-mode-synth (SPlus d1 d2) with buildexp-mode-ana d1 | buildexp-mode-ana d2
    ... | (_ , p1) | (_ , p2) = _ , BuildPlus p1 p2
    buildexp-mode-synth SEHole = _ , BuildEHole
    buildexp-mode-synth (SFHole d) with buildexp-mode-synth d
    ... | (_ , p)= _ , BuildFHole p
    buildexp-mode-synth (SApHole d1 d2) with buildexp-mode-synth d1 | buildexp-mode-ana d2
    ... | (_ , p1) | (_ , p2) = _ , BuildAp p1 p2

    buildexp-mode-ana : {Γ : ·ctx} {e : ė} {t : τ̇} (wt : Γ ⊢ e <= t) →
              Σ[ l ∈ List action ] buildexp ▹ e ◃ l
    buildexp-mode-ana (ASubsume x _) = buildexp-mode-synth x
    buildexp-mode-ana (ALam _ d) with buildexp-mode-ana d
    ... | (_ , p)= _ , BuildLam p

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

  -- runtype lifts to the list monoid as expected
  runtype++ : ∀{t t' t'' L1 L2 }
                → runtype t  L1 t'
                → runtype t' L2 t''
                → runtype t (L1 ++ L2) t''
  runtype++ DoRefl d2 = d2
  runtype++ (DoType x d1) d2 = DoType x (runtype++ d1 d2)

  -- runtype is a congruence; that is, you can replace related subterms and
  -- preseve relatedness
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


  data runsynth :
    (Γ : ·ctx) (e : ê) (t1 : τ̇) (Lα : List action) (e' : ê) (t2 : τ̇) → Set where
     DoRefl  : {Γ : ·ctx} {e : ê} {t : τ̇} → runsynth Γ e t [] e t
     DoSynth : {Γ : ·ctx} {e : ê} {t : τ̇} {α : action} {e' e'' : ê} {t' t'' : τ̇}
               {L : List action} →
                Γ ⊢ e => t ~ α ~> e' => t →
               runsynth Γ e' t' L e'' t'' →
               runsynth Γ e t (α :: L) e'' t''

  -- runsynth lifts to the list monoid as expected
  runsynth++ : ∀{Γ e t L1 e' t' L2 e'' t''}
                → runsynth Γ e t L1 e' t'
                → runsynth Γ e' t' L2 e'' t''
                → runsynth Γ e t (L1 ++ L2) e'' t''
  runsynth++ DoRefl d2 = d2
  runsynth++ (DoSynth x d1) d2 = DoSynth x (runsynth++ d1 d2)

  -- congruence rules for runsynth
  runsynth-congap1 : ∀{Γ e1 t L e1' e2 t'} →
                    runsynth Γ e1 t' L e1' t' →
                    runsynth Γ (e1 ∘₁ e2) t L (e1' ∘₁ e2) t
  runsynth-congap1 DoRefl = DoRefl
  runsynth-congap1 (DoSynth x d) = DoSynth (SAZipAp1 {!!} {!x!} {!!})
                                           (runsynth-congap1 {!d!})

  data runana : (Γ : ·ctx) (e : ê) (Lα : List action) (e' : ê) (t : τ̇) → Set where
     DoRefl : {Γ : ·ctx} {e : ê} {t : τ̇} → runana Γ e [] e t
     DoAna : {Γ : ·ctx} {e : ê} {α : action} {e' e'' : ê} {t : τ̇}
              {L : List action} →
              Γ ⊢ e ~ α ~> e' ⇐ t →
              runana Γ e' L e'' t →
              runana Γ e (α :: L) e'' t

  -- runana lifts to the list monoid as expected
  runana++ : ∀{Γ e t L1 e' L2 e''}
                → runana Γ e  L1 e' t
                → runana Γ e' L2 e'' t
                → runana Γ e (L1 ++ L2) e'' t
  runana++ DoRefl d2 = d2
  runana++ (DoAna x d1) d2 = DoAna x (runana++ d1 d2)

  -- if there is a list of actions that builds a type, running that list
  -- from the empty hole in focus really does produce the target type.
  constructτ : {t : τ̇} {L : List action} →
                        buildtype ▹ t ◃ L →
                        runtype (▹ <||> ◃) L (▹ t ◃)
  constructτ  BuildNum = DoType TMConNum DoRefl
  constructτ  BuildTHole = DoType TMDel DoRefl
  constructτ (BuildArr bt1 bt2) with constructτ bt1 | constructτ bt2
  ... | ih1 | ih2 = runtype++ ih1 (DoType TMConArrow (runtype++ (runtype-cong2 ih2) (DoType TMParent2 DoRefl)))

  mutual
    constructsynth : {Γ : ·ctx} {e : ė} {t : τ̇} {L : List action} →
                       Γ ⊢ e => t
                     → buildexp ▹ e ◃ L
                     → runsynth Γ ▹ <||> ◃ <||> L ▹ e ◃ t
    constructsynth wt b = {!!}

    constructana : {Γ : ·ctx} {e : ė} {t : τ̇} {L : List action} →
                       Γ ⊢ e <= t
                     → buildexp ▹ e ◃ L
                     → runana Γ ▹ <||> ◃ L ▹ e ◃ t
    constructana wt b = {!!}


  -- tie together the mode theorem and the above to demonstrate that for
  -- any type there is a spcific list of actions that builds it.
  constructability-types : (t : τ̇) → Σ[ L ∈ List action ] runtype (▹ <||> ◃) L (▹ t ◃)
  constructability-types t with buildtype-mode t
  ... | (L , pf) = L , constructτ pf

  constructability-synth : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e => t) →
                              Σ[ L ∈ List action ]
                                 runsynth Γ ▹ <||> ◃ <||> L ▹ e ◃ t
  constructability-synth wt with buildexp-mode-synth wt
  ... | (L , pf) = L , constructsynth wt pf

  constructability-ana : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e <= t) →
                              Σ[ L ∈ List action ]
                                 runana Γ ▹ <||> ◃ L ▹ e ◃ t
  constructability-ana wt with buildexp-mode-ana wt
  ... | (L , pf) = L , constructana wt pf





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
    reachup-synth (EEApL er) (SAp wt x) with reachup-synth er wt
    ... | ih = runsynth++ (runsynth-congap1 ih) (DoSynth (SAMove EMApParent1) DoRefl)
    reachup-synth (EEApR er) (SAp wt x) = {!!}
    reachup-synth (EEPlusL er) (SPlus x x₁) = {!!}
    reachup-synth (EEPlusR er) (SPlus x x₁) = {!!}
    reachup-synth (EEApL er) (SApHole wt x) = {!!}
    reachup-synth (EEApR er) (SApHole wt x) = {!!}
    reachup-synth (EEFHole er) (SFHole wt) = {!!}

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
  movedown-e <| e |>   <| e' |>     (EEFHole er) = move firstChild :: movedown-e _ _ er
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
    reachdown-synth (EEApL p) (SAp wt x) = {!!}
    reachdown-synth (EEApL p) (SApHole wt x) = {!!}
    reachdown-synth (EEApR p) (SAp wt x) = {!!}
    reachdown-synth (EEApR p) (SApHole wt x) = {!!}
    reachdown-synth (EEPlusL p) (SPlus x x₁) = {!!}
    reachdown-synth (EEPlusR p) (SPlus x x₁) = {!!}
    reachdown-synth (EEFHole p) (SFHole wt) = {!!}

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
    reachdown-ana (EEFHole p) (ASubsume x x₁) = {!!}
    reachdown-ana (EELam p) (ALam x₁ wt) = {!!}

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
                           Σ[ L ∈ List action ] runtype t1 L t2
  reachability-types t1 t2 eq with ◆erase-t t1 (t2 ◆t) eq | ◆erase-t t2 (t1 ◆t) (! eq)
  ... | er1 | er2 with reachup-type er1 | reachdown-type er2
  ... | up  | down = moveup-t t1 ++ movedown-t (t1 ◆t) t2 er2 ,
                     runtype++ up (tr (λ x → runtype ▹ x ◃ (movedown-t (t1 ◆t) t2 er2 ) t2 ) eq down)

  reachability-synth : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e => t →
                            Γ ⊢ e2 ◆e => t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runsynth Γ e1 t L e2 t
  reachability-synth Γ t e1 e2 wt1 wt2 eq with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-synth er1 wt2 | reachdown-synth er2 wt1
  ... | up  | down = moveup-e e1 ++ movedown-e (e1 ◆e) e2 er2 , runsynth++ up (tr (λ x → runsynth Γ ▹ x ◃ t (movedown-e (e1 ◆e) e2 er2) e2 t) eq
                                                                                 down)

  reachability-ana : (Γ : ·ctx) (t : τ̇) (e1 e2 : ê) →
                            Γ ⊢ e1 ◆e <= t →
                            Γ ⊢ e2 ◆e <= t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runana Γ e1 L e2 t
  reachability-ana Γ t e1 e2 wt1 wt2 eq with ◆erase-e e1 (e2 ◆e) eq | ◆erase-e e2 (e1 ◆e) (! eq)
  ... | er1 | er2 with reachup-ana er1 wt2 | reachdown-ana er2 wt1
  ... | up  | down = moveup-e e1 ++ movedown-e (e1 ◆e) e2 er2 , runana++ up (tr (λ x → runana Γ ▹ x ◃ (movedown-e (e1 ◆e) e2 er2) e2 t) eq
                                                                                 down)

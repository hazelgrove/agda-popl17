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
  data runsynth :
    (Γ : ·ctx) (e : ê) (t1 : τ̇) (Lα : List action) (e' : ê) (t2 : τ̇) → Set where
     DoRefl  : {Γ : ·ctx} {e : ê} {t : τ̇} → runsynth Γ e t [] e t
     DoSynth : {Γ : ·ctx} {e : ê} {t : τ̇} {α : action} {e' e'' : ê} {t' t'' : τ̇}
               {L : List action} →
                Γ ⊢ e => t ~ α ~> e' => t →
               runsynth Γ e' t' L e'' t'' →
               runsynth Γ e t (α :: L) e'' t''

  data runana : (Γ : ·ctx) (e : ê) (Lα : List action) (e' : ê) (t : τ̇) → Set where
     DoRefl : {Γ : ·ctx} {e : ê} {t : τ̇} → runana Γ e [] e t
     DoAna : {Γ : ·ctx} {e : ê} {α : action} {e' e'' : ê} {t : τ̇}
              {L : List action} →
              Γ ⊢ e ~ α ~> e' ⇐ t →
              runana Γ e' L e'' t →
              runana Γ e (α :: L) e'' t

  data runtype : (t : τ̂) (Lα : List action) (t' : τ̂) → Set where
     DoRefl : {t : τ̂} → runtype t [] t
     DoType : {t : τ̂} {α : action} {t' t'' : τ̂}
              {L : List action} →
               t + α +> t' →
               runtype t' L t'' →
               runtype t (α :: L) t''

  -- if there is a list of actions that builds a type, running that list
  -- from the empty hole in focus really does produce the target type.
  constructτ : {t : τ̇} {L : List action} →
                        buildtype ▹ t ◃ L →
                        runtype (▹ <||> ◃) L (▹ t ◃)
  constructτ  BuildNum = DoType TMConNum DoRefl
  constructτ  BuildTHole = DoType TMDel DoRefl
  constructτ (BuildArr bt1 bt2) with constructτ bt1 | constructτ bt2
  ... | DoRefl     | DoRefl       = DoType TMConArrow (DoType TMParent2 DoRefl)
  ... | DoRefl     | DoType x q   = DoType TMConArrow {!!}
  ... | DoType x p | DoRefl       = {!!}
  ... | DoType x p | DoType  x₁ q = {!!}

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
  -- still bounded by the size of the expression, and is easier to
  -- maniupulate judgementally.

  movepar-t : τ̂ → List action
  movepar-t ▹ _ ◃      = []
  movepar-t (t ==>₁ _) = move parent :: movepar-t t
  movepar-t (_ ==>₂ t) = move parent :: movepar-t t

  movepar-e : ê → List action
  movepar-e ▹ _ ◃     = []
  movepar-e (e ·:₁ _) = move parent :: movepar-e e
  movepar-e (_ ·:₂ t) = move parent :: movepar-t t
  movepar-e (·λ _ e)  = move parent :: movepar-e e
  movepar-e (e ∘₁ _)  = move parent :: movepar-e e
  movepar-e (_ ∘₂ e)  = move parent :: movepar-e e
  movepar-e (e ·+₁ _) = move parent :: movepar-e e
  movepar-e (_ ·+₂ e) = move parent :: movepar-e e
  movepar-e <| e |>   = move parent :: movepar-e e

  reachτ : {t : τ̂} {t' : τ̇} →
              erase-t t t' →
              runtype t (movepar-t t) (▹ t' ◃)
  reachτ ETTop = DoRefl
  reachτ (ETArrL tr) = {!!}
  reachτ (ETArrR tr) with reachτ tr
  ... | ih = {!!}

  mutual
    reachsynth : {Γ : ·ctx} {e : ê} {t : τ̇} {L : List action} {e' : ė} →
                      (erase-e e e') →
                      (wt : Γ ⊢ e' => t)
                     → runsynth Γ e t (movepar-e e) ▹ e' ◃ t
    reachsynth = {!!}

    reachana : {Γ : ·ctx} {e : ê} {t : τ̇} {L : List action} {e' : ė} →
                      (erase-e e e') →
                      (wt : Γ ⊢ e' <= t)
                     → runana Γ e (movepar-e e) ▹ e' ◃ t
    reachana = {!!}


  -- top level statement of the reachability triplet. the movement between
  -- judgemental and metafunctional erasure happens internally to theses
  -- statements to present a consistent interface with the paper, while
  -- allowing easy pattern matching in the proofs.
  --
  -- the justification for these statements, intuitively, is that focus
  -- cannot change the type of things because the typing judgement is
  -- defined on the focus-erased terms and types. so if two terms agree up
  -- to erasure, they must have the exact same type in the same context,
  -- not merely a compatible one in an extension or any other weakening of
  -- the statement. these are lemmas which are currently not proven. TODO?

  reachability-types : (t1 t2 : τ̂) → (t1 ◆t) == (t2 ◆t) → Σ[ L ∈ List action ] runtype t1 L t2
  reachability-types = {!!}

  reachability-synth : {Γ : ·ctx} {t : τ̇} {e1 e2 : ê} →
                            Γ ⊢ e1 ◆e => t →
                            Γ ⊢ e2 ◆e => t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runsynth Γ e1 t L e2 t
  reachability-synth = {!!}

  reachability-ana : {Γ : ·ctx} {t : τ̇} {e1 e2 : ê} →
                            Γ ⊢ e1 ◆e <= t →
                            Γ ⊢ e2 ◆e <= t →
                            e1 ◆e == e2 ◆e →
                            Σ[ L ∈ List action ] runana Γ e1 L e2 t
  reachability-ana = {!!}

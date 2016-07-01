open import Nat
open import Prelude
open import List
open import core

module checks where
  -- movement doesn't change the term other than moving the focus around.
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
    BuildArr   : (t1 t2 : τ̇) (l1 l2 : List action)
                 → buildtype ▹ t1 ◃ l1
                 → buildtype ▹ t2 ◃ l2
                 → buildtype ▹ t1 ==> t2 ◃
                      (l1 ++ (construct arrow :: l2 ++ [ move parent ]))

  -- small example of a derivation for building a particular type.
  bt-ex : Σ[ l ∈ List action ] buildtype (▹ num ==> <||> ◃) l
  bt-ex = construct num :: construct arrow :: del :: move parent :: [] ,
         BuildArr num <||> (construct num :: []) (del :: []) BuildNum
         BuildTHole



  -- todo: it's not clear if i can get away with not knowing the typing
  -- information here. the same action makes different expressions
  -- depending on if it's in a synthetic or analytic position given the
  -- paired action semantics judgements.
  --
  --  (Γ : ·ctx) (t : τ̇) (wt : (Γ ⊢ e => t) + (Γ ⊢ e <= t))

  -- there's a hidden invariant here, which is that we always leave the
  -- cursor at the top of the expression. this lets us prove later that we
  -- can build a specifc thing starting at the expression that's just a
  -- hole in focus.

  -- currently: DO NOT TRUST THAT THESE LISTS ARE CORRECT
  data buildexp : (e : ê) → List action → Set where
    BuildAsc : (e : ė) (t : τ̇) (l1 l2 : List action)
               → buildexp ▹ e ◃ l1
               → buildtype ▹ t ◃ l2
               → buildexp ▹ e ·: t ◃
                          (l1 ++ (construct asc :: l2 ++ [ move parent ]))
    BuildX : (x : Nat) → buildexp ▹ X x ◃  [ construct (var x) ]
    BuildLam : (x : Nat) (e : ė) (l : List action)
               → buildexp ▹ e ◃ l
               → buildexp ▹ ·λ x e ◃ [] -- stub
    BuildN : (n : Nat) → buildexp ▹ N n ◃ [ construct (numlit n) ]
    BuildPlus : (e1 e2 : ė) (l1 l2 : List action)
                 → buildexp ▹ e1 ◃ l1
                 → buildexp ▹ e2 ◃ l2
                 → buildexp ▹ e1 ·+ e2 ◃
                            (l1 ++ l2 ++ [ move parent ])
    BuildAp :  (e1 e2 : ė) (l1 l2 : List action)
                 → buildexp ▹ e1 ◃ l1
                 → buildexp ▹ e2 ◃ l2
                 → buildexp ▹ e1 ∘ e2 ◃
                            (l1 ++ l2 ++ [ move parent ])
    BuildEHole : buildexp ▹ <||> ◃ [ del ]

    -- this littl guy might just happen sort of automatically in the
    -- inducive structure of the proof and by appealing to zipper rules.
    --
    -- BuildFHole : (e : ė) (l : List action) →
    --              buildexp ▹ e ◃ l →
    --              buildexp ▹ <| e |> ◃ [] -- stub

  -- taken together, these three theorems say that the build judgements
  -- have mode (∀, ∃), which is to say that they effectively define total
  -- functions and we didn't miss any cases.
  buildτ : (t : τ̇) → Σ[ l ∈ List action ] buildtype ▹ t ◃ l
  buildτ num  = _ , BuildNum
  buildτ <||> = _ , BuildTHole
  buildτ (t1 ==> t2) with buildτ t1 | buildτ t2
  ... | (l1 , p1) | (l2 , p2) = _ , BuildArr t1 t2 l1 l2 p1 p2

  mutual
    buildsynth : {Γ : ·ctx} {e : ė} {t : τ̇} (wt : Γ ⊢ e => t) →
               Σ[ l ∈ List action ] buildexp ▹ e ◃ l
    buildsynth (SAsc {e = e} {t = t} x) with buildana x | buildτ t
    ... | (l1 , p1) | (l2 , p2) = _ ,  BuildAsc e t l1 l2 p1 p2
    buildsynth (SVar _) = _ , BuildX _
    buildsynth (SAp {e1 = e1} {e2 = e2} wt x) = {!!}
    buildsynth SNum = _ , BuildN _
    buildsynth (SPlus {e1 = e1} {e2 = e2} x x₁) = {!!}
    buildsynth SEHole = {!!}
    buildsynth (SFHole wt) = {!!}
    buildsynth (SApHole wt x) = {!!}

    buildana : {Γ : ·ctx} {e : ė} {t : τ̇} (wt : Γ ⊢ e <= t) →
              Σ[ l ∈ List action ] buildexp ▹ e ◃ l
    buildana (ASubsume x x₁) = buildsynth x
    buildana (ALam  x wt) = {!!}

  -- these three judmgements lift the action semantics judgements to relate
  -- an expression and a list of pair-wise composable actions to the
  -- expression that's produced by tracing through the action semantics for
  -- each element in that list. we do this just by appealing to the
  -- original judgement with some constraints about using the same term to
  -- enforce composability. in all three cases, we assert that the empty
  -- list of actions constitutes a reflexivity step, so when you run out of
  -- actions to preform you have to be where you wanted to be.
  --
  -- note that the only difference between the types for each judgement and
  -- the original action semantics is that the action is now a list of
  -- actions.
  data runsynth :
    (Γ : ·ctx) (e : ê) (t1 : τ̇) (Lα : List action) (e' : ê) (t2 : τ̇) → Set where
     DoRefl  : {Γ : ·ctx} {e : ê} {t : τ̇} → runsynth Γ e t [] e t
     DoSynth : (Γ : ·ctx) (e : ê) (t : τ̇) (α : action) (e' e'' : ê) (t' t'' : τ̇)
               (L : List action) →
                Γ ⊢ e => t ~ α ~> e' => t →
               runsynth Γ e' t' L e'' t'' →
               runsynth Γ e t (α :: L) e'' t''

  data runana : (Γ : ·ctx) (e : ê) (Lα : List action) (e' : ê) (t : τ̇) → Set where
     DoRefl : {Γ : ·ctx} {e : ê} {t : τ̇} → runana Γ e [] e t
     DoAna : (Γ : ·ctx) (e : ê) (α : action) (e' e'' : ê) (t : τ̇) (L : List action) →
              Γ ⊢ e ~ α ~> e' ⇐ t →
              runana Γ e' L e'' t →
              runana Γ e (α :: L) e'' t

  data runtype : (t : τ̂) (Lα : List action) (t' : τ̂) → Set where
     DoRefl : {t : τ̂} → runtype t [] t
     DoType : (t : τ̂) (α : action) (t' t'' : τ̂) (L : List action) →
               t + α +> t' →
               runtype t' L t'' →
               runtype t (α :: L) t''


  -- if there is a list of actions that builds a type, running that list
  -- from the empty hole in focus really does produce the target type.
  constructτ : (t : τ̇) (L : List action) →
                        buildtype ▹ t ◃ L →
                        runtype (▹ <||> ◃) L (▹ t ◃)
  constructτ .num .(construct num :: []) BuildNum = DoType ▹ <||> ◃ (construct num) ▹ num ◃ ▹ num ◃ [] TMConNum DoRefl
  constructτ .<||> .(del :: []) BuildTHole = DoType ▹ <||> ◃ del ▹ <||> ◃ ▹ <||> ◃ [] TMDel DoRefl
  constructτ .(t1 ==> t2) .(l1 ++ construct arrow :: (l2 ++ move parent :: [])) (BuildArr t1 t2 l1 l2 bt bt₁) = {!!}


  -- tie together the mode theorem and the above to demonstrate that for
  -- any type there is a list of actions that builds it.
  type-constructability : (t : τ̇) → Σ[ L ∈ List action ] runtype (▹ <||> ◃) L (▹ t ◃)
  type-constructability t with buildτ t
  ... | (L , pf) = L , constructτ t L pf

  mutual
    constructsynth : {Γ : ·ctx} {e : ė} {t : τ̇} {L : List action} (wt : Γ ⊢ e => t)
                     → buildexp ▹ e ◃ L
                     → runsynth Γ ▹ <||> ◃ t L ▹ e ◃ t
    constructsynth wt b = {!wt b!}

    constructana : {Γ : ·ctx} {e : ė} {t : τ̇} {L : List action} (wt : Γ ⊢ e <= t)
                     → buildexp ▹ e ◃ L
                     → runana Γ ▹ <||> ◃ L ▹ e ◃ t
    constructana wt b = {!!}


  ------- reachability

  -- we break reachability into two halves: first you produce a list of
  -- actions that are all "move parent" to pull the cursor to the very top
  -- of the expression in question. then, you go back down into the
  -- expression with a sequence of move firstChild and move nextSibs as
  -- appropriate. the append of these two lists will reach from one
  -- expression to the other. there may well be a shorter list of actions
  -- that does the same thing; the expression with top-level focus may not
  -- be the Least Common Ancestor in the expression tree of the given
  -- pair. however, the work of this less minimal thing and corresponding
  -- size of the proof term is still bounded by the size of the expression,
  -- and is easier to maniupulate judgementally.

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

  data erase-t : τ̂ → τ̇ → Set where
    ETTop  : ∀{t} → erase-t (▹ t ◃) t
    ETArrL : ∀{t1 t1' t2} → erase-t t1 t1' → erase-t (t1 ==>₁ t2) (t1' ==> t2)
    ETArrR : ∀{t1 t2 t2'} → erase-t t2 t2' → erase-t (t1 ==>₂ t2) (t1 ==> t2')

  data erase-e : ê → ė → Set where
    EETop   : ∀{x} → erase-e (▹ x ◃) x
    EEAscL  : ∀{e e' t} → erase-e e e' → erase-e (e ·:₁ t) (e' ·: t)
    EEAscR  : ∀{e t t'} → erase-t t t' → erase-e (e ·:₂ t) (e ·: t')
    EELam   : ∀{x e e'} → erase-e e e' → erase-e (·λ x e) (·λ x e')
    EEApL   : ∀{e1 e1' e2} → erase-e e1 e1' → erase-e (e1 ∘₁ e2) (e1' ∘ e2)
    EEApR   : ∀{e1 e2 e2'} → erase-e e2 e2' → erase-e (e1 ∘₂ e2) (e1 ∘ e2')
    EEPlusL : ∀{e1 e1' e2} → erase-e e1 e1' → erase-e (e1 ·+₁ e2) (e1' ·+ e2)
    EEPlusR : ∀{e1 e2 e2'} → erase-e e2 e2' → erase-e (e1 ·+₂ e2) (e1 ·+ e2')
    EEFHole : ∀{e e'} → erase-e e e' → erase-e <| e |>  <| e' |>

  -- this judgemental form really does agree with the function
  erase-t◆ : {t : τ̂} {tr : τ̇} → (erase-t t tr) → (t ◆t == tr)
  erase-t◆ ETTop       = refl
  erase-t◆ (ETArrL p)  = ap1 (λ x → x ==> _) (erase-t◆ p)
  erase-t◆ (ETArrR p)  = ap1 (λ x → _ ==> x) (erase-t◆ p)

  erase-e◆ : {e : ê} {er : ė} → (erase-e e er) → (e ◆e == er)
  erase-e◆ EETop       = refl
  erase-e◆ (EEAscL p)  = ap1 (λ x → x ·: _)  (erase-e◆ p)
  erase-e◆ (EEAscR p)  = ap1 (λ x → _ ·: x)  (erase-t◆ p)
  erase-e◆ (EELam p)   = ap1 (λ e → ·λ _ e)  (erase-e◆ p)
  erase-e◆ (EEApL p)   = ap1 (λ x → x ∘ _)   (erase-e◆ p)
  erase-e◆ (EEApR p)   = ap1 (λ x → _ ∘ x)   (erase-e◆ p)
  erase-e◆ (EEPlusL p) = ap1 (λ x → x ·+ _)  (erase-e◆ p)
  erase-e◆ (EEPlusR p) = ap1 (λ x → _ ·+ x)  (erase-e◆ p)
  erase-e◆ (EEFHole p) = ap1 (λ x → <| x |>) (erase-e◆ p)

  reachτ : {t : τ̂} {t' : τ̇} →
              erase-t t t' →
              runtype t (movepar-t t) (▹ t' ◃)
  reachτ ETTop = DoRefl
  reachτ (ETArrL tr) with reachτ tr
  ... | ih = {!!}
  reachτ (ETArrR tr) with reachτ tr
  ... | ih = {!!}

  mutual
    reachsynth : {Γ : ·ctx} {e : ê} {t : τ̇} {L : List action} {e' : ė} →
                      (erase-e e e') →
                      (wt : Γ ⊢ e' => t)
                     → runsynth Γ e  t (movepar-e e) ▹ e' ◃ t
    reachsynth EETop _ = DoRefl
    reachsynth (EEAscL er) (SAsc x) = {!!}
    reachsynth (EEAscR x) (SAsc x₁) = {!reachτ !}
    reachsynth (EELam er) ()
    reachsynth (EEApL er) (SAp wt x) = {!!}
    reachsynth (EEApL er) (SApHole wt x) = {!!}
    reachsynth (EEApR er) (SAp wt x) = {!!}
    reachsynth (EEApR er) (SApHole wt x) = {!!}
    reachsynth (EEPlusL er) (SPlus x x₁) = {!!}
    reachsynth (EEPlusR er) (SPlus x x₁) = {!!}
    reachsynth (EEFHole er) (SFHole wt) = {!!}

    reachana : {Γ : ·ctx} {e : ê} {t : τ̇} {L : List action} {e' : ė} →
                      (erase-e e e') →
                      (wt : Γ ⊢ e' <= t)
                     → runana Γ e (movepar-e e) ▹ e' ◃ t
    reachana EETop _ = DoRefl
    reachana y (ASubsume x x₁) with reachsynth {L = {!!} :: {!!}} y x
    ... | ih  = {!DoAna _ _ _ _ _ _ _ (AASubsume ? ? ?) !}
    reachana (EELam wt) (ALam x₁ b) = {!!}

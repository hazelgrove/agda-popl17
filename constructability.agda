open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks

module constructability where
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
               → buildexp ▹ e ·: t ◃ (construct asc :: (l2 ++ (move parent :: move firstChild :: (l1 ++ [ move parent ]))))
    BuildX : {x : Nat} → buildexp ▹ X x ◃  [ construct (var x) ]
    BuildLam : {x : Nat} {e : ė} {l : List action}
               → buildexp ▹ e ◃ l
               → buildexp ▹ ·λ x e ◃ ((construct (lam x)) :: (l ++ [ move parent ]))
    BuildN : {n : Nat} → buildexp ▹ N n ◃ [ construct (numlit n) ]
    BuildPlus : {e1 e2 : ė} {l1 l2 : List action}
                 → buildexp ▹ e1 ◃ l1
                 → buildexp ▹ e2 ◃ l2
                 → buildexp ▹ e1 ·+ e2 ◃ ((construct plus :: (l2 ++ (move parent :: move firstChild :: (l1 ++ [ move parent ])))))
    BuildAp :  {e1 e2 : ė} {l1 l2 : List action}
                 → buildexp ▹ e1 ◃ l1
                 → buildexp ▹ e2 ◃ l2
                 → buildexp ▹ e1 ∘ e2 ◃ (l1 ++ (construct ap :: (l2 ++ [ move parent ])))
    BuildEHole : buildexp ▹ <||> ◃ [ del ]
    BuildNEHole : {e : ė} {l : List action} →
                 buildexp ▹ e ◃ l →
                 buildexp ▹ <| e |> ◃ (l ++ (construct nehole :: move parent :: []))

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
    buildexp-mode-synth (SAp d1 m d2)
      with buildexp-mode-synth d1 | buildexp-mode-ana d2
    ... | (_ , p1) | (_ , p2) = _ , BuildAp p1 p2
    buildexp-mode-synth SNum = _ , BuildN
    buildexp-mode-synth (SPlus d1 d2) with buildexp-mode-ana d1 | buildexp-mode-ana d2
    ... | (_ , p1) | (_ , p2) = _ , BuildPlus p1 p2
    buildexp-mode-synth SEHole = _ , BuildEHole
    buildexp-mode-synth (SNEHole d) with buildexp-mode-synth d
    ... | (_ , p)= _ , BuildNEHole p

    buildexp-mode-ana : {Γ : ·ctx} {e : ė} {t : τ̇} (wt : Γ ⊢ e <= t) →
              Σ[ l ∈ List action ] buildexp ▹ e ◃ l
    buildexp-mode-ana (ASubsume x _) = buildexp-mode-synth x
    buildexp-mode-ana (ALam m _ d) with buildexp-mode-ana d
    ... | (_ , p)= _ , BuildLam p

  constructtype : {t : τ̇} {L : List action} →
                        buildtype ▹ t ◃ L →
                        runtype (▹ <||> ◃) L (▹ t ◃)
  constructtype  BuildNum = DoType TMConNum DoRefl
  constructtype  BuildTHole = DoType TMDel DoRefl
  constructtype (BuildArr bt1 bt2) with constructtype bt1 | constructtype bt2
  ... | ih1 | ih2 = runtype++ ih1 (DoType TMConArrow (runtype++ (runtype-cong2 ih2) (DoType TMParent2 DoRefl)))

  mutual
    constructsynth : {Γ : ·ctx} {e : ė} {t : τ̇} {L : List action} →
                       Γ ⊢ e => t
                     → buildexp ▹ e ◃ L
                     → runsynth Γ ▹ <||> ◃ <||> L ▹ e ◃ t
    constructsynth (SAsc x) (BuildAsc b x₁) with constructtype x₁ | constructana x b
    ... | ih1 | ih2 = DoSynth SAConAsc
                       (runsynth++ (lem-tscong ih1)
                         (DoSynth (SAMove EMAscParent2)
                           (DoSynth (SAMove EMAscFirstChild)
                             (runsynth++ (lem-anasynthasc ih2)
                               (DoSynth (SAMove EMAscParent1) DoRefl)))))
    constructsynth (SVar x) BuildX = DoSynth (SAConVar x) DoRefl
    constructsynth (SAp wt m x) (BuildAp b b₁) with constructsynth wt b | constructana x b₁
    ... | ih1 | ih2 = runsynth++ ih1
                       (DoSynth (SAConApArr m)
                        (runsynth++ (synth-ana-ap2-cong wt m ih2)
                          (DoSynth (SAMove EMApParent2) DoRefl)))
    constructsynth SNum BuildN = DoSynth SAConNumlit DoRefl
    constructsynth (SPlus x x₁) (BuildPlus b b₁) with constructana x b | constructana x₁ b₁
    ... | ih1 | ih2 = DoSynth (SAConPlus1 TCHole2)
                       (runsynth++ (synth-ana-plus2-cong ih2)
                         (DoSynth (SAMove EMPlusParent2)
                            (DoSynth (SAMove EMPlusFirstChild)
                               (runsynth++ (synth-ana-plus1-cong ih1)
                                 (DoSynth (SAMove EMPlusParent1) DoRefl)))))
    constructsynth SEHole BuildEHole = DoSynth SADel DoRefl
    constructsynth (SNEHole wt) (BuildNEHole b) = runsynth++ (constructsynth wt b)
                                                    (DoSynth SAConNEHole
                                                      (DoSynth (SAMove EMNEHoleParent) DoRefl))

    constructana : {Γ : ·ctx} {e : ė} {t : τ̇} {L : List action} →
                       Γ ⊢ e <= t
                     → buildexp ▹ e ◃ L
                     → runana Γ ▹ <||> ◃ L ▹ e ◃ t
    constructana (ASubsume x₁ x) build with constructsynth x₁ build
    ... | ih = {!!}
    constructana (ALam m x₁ wt) (BuildLam b) with constructana wt b
    ... | ih = DoAna (AAConLam1 m x₁) (runana++ (ana-lam-cong m x₁ ih) (DoAna (AAMove EMLamParent) DoRefl))


  -- tie together the mode theorem and the above to demonstrate that for
  -- any type there is a spcific list of actions that builds it.
  -- constructability-types : (t : τ̇) → Σ[ L ∈ List action ] runtype (▹ <||> ◃) L (▹ t ◃)
  -- constructability-types t with buildtype-mode t
  -- ... | (L , pf) = L , constructtype pf
  constructability-types : (t : τ̇) → Σ[ L ∈ List action ] runtype (▹ <||> ◃) L (▹ t ◃)
  constructability-types num = [ construct num ] , (DoType TMConNum DoRefl)
  constructability-types <||> = [ del ] , DoType TMDel DoRefl
  constructability-types (t1 ==> t2) with constructability-types t1 | constructability-types t2
  ... | (l1 , ih1) | (l2 , ih2) =
      l1 ++ construct arrow :: l2 ++ [ move parent ] ,
      runtype++ ih1
        (DoType TMConArrow
         (runtype++ (runtype-cong2 ih2) (DoType TMParent2 DoRefl)))

  mutual
    constructability-synth : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e => t) →
                                Σ[ L ∈ List action ]
                                   runsynth Γ ▹ <||> ◃ <||> L ▹ e ◃ t
    constructability-synth wt with buildexp-mode-synth wt
    ... | (L , pf) = L , constructsynth wt pf

  -- constructability-ana : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e <= t) →
  --                             Σ[ L ∈ List action ]
  --                                runana Γ ▹ <||> ◃ L ▹ e ◃ t
  -- constructability-ana wt with buildexp-mode-ana wt
  -- ... | (L , pf) = L , constructana wt pf

    lem-nehole-cong : ∀{Γ e L e' t'} →
                    runsynth Γ e <||> L e' t' →
                    runana Γ <| e |> L <| e' |> t'
    lem-nehole-cong DoRefl = DoRefl
    lem-nehole-cong (DoSynth x d) = {!!}


    constructability-ana : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e <= t) →
                                Σ[ L ∈ List action ]
                                   runana Γ ▹ <||> ◃ L ▹ e ◃ t
    constructability-ana (ASubsume x x₁) with constructability-synth x
    ... | (l1 , ih1) =
        construct nehole :: l1 ++ (finish :: move parent :: []) ,
              DoAna (AASubsume {p = {!!}} SEHole SAConNEHole TCHole1)
                (runana++ {L1 = l1} {L2 = finish :: move parent :: []}
                  {!lem-nehole-cong ih1 !} (DoAna {!!} (DoAna {!!} DoRefl)))
    constructability-ana (ALam x₁ x₂ wt) = {!!}

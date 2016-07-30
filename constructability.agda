open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks

module constructability where
  -- we construct expressions and types by induction on their
  -- structure. for each sub term, we call the relevant theorem, then
  -- assemble the results with carefully chosen lists of actions that allow
  -- us to call the appropriate zipper lemmas and maintain well-typedness
  -- at every stage of the contruction.
  --
  -- the proof term at each stage except subsumption is, morally, just the
  -- mapping of the fragment of the action semantics used by the constructs
  -- in the list in the current formation context into the list monoid.

  -- construction of types
  construct-type : (t : τ̇) → Σ[ L ∈ List action ] runtype (▹ <||> ◃) L (▹ t ◃)
  construct-type num  = [ construct num ] , DoType TMConNum DoRefl
  construct-type <||> = [ del ]           , DoType TMDel DoRefl
  construct-type (t1 ==> t2) with construct-type t1 | construct-type t2
  ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct arrow :: l2 ++ [ move parent ] ,
                                 runtype++ ih1
                                   (DoType TMConArrow
                                     (runtype++ (ziplem-tmarr2 ih2)
                                       (DoType TMArrParent2 DoRefl)))

  mutual
    -- construction of expressions in synthetic positions
    construct-synth : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e => t) →
                                  Σ[ L ∈ List action ]
                                     runsynth Γ ▹ <||> ◃ <||> L ▹ e ◃ t
      -- the three base cases
    construct-synth (SVar x) = [ construct (var _) ]    , DoSynth (SAConVar x) DoRefl
    construct-synth SNum =     [ construct (numlit _) ] , DoSynth SAConNumlit DoRefl
    construct-synth SEHole =   [ del ]                  , DoSynth SADel DoRefl

      -- the inductive cases
    construct-synth {t = t} (SAsc x) with construct-type t | construct-ana x
    ... | (l1 , ih1) | (l2 , ih2) = construct asc :: (l1 ++ move parent :: move firstChild :: (l2 ++ [ move parent ])) ,
                                    DoSynth SAConAsc
                                        (runsynth++ (ziplem-asc2 ETTop ETTop ih1)
                                         (DoSynth (SAMove EMAscParent2)
                                          (DoSynth (SAMove EMAscFirstChild)
                                           (runsynth++ (ziplem-asc1 ih2)
                                            (DoSynth (SAMove EMAscParent1) DoRefl)))))

    construct-synth (SAp e1 m e2) with construct-synth e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct ap :: (l2 ++ [ move parent ]) ,
                                    runsynth++ ih1
                                        (DoSynth (SAConApArr m)
                                         (runsynth++ (ziplem-ap2 e1 m ih2)
                                          (DoSynth (SAMove EMApParent2) DoRefl)))

    construct-synth (SPlus e1 e2 ) with construct-ana e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) = construct plus :: (l2 ++ move parent :: move firstChild :: (l1 ++ [ move parent ])) ,
                                    DoSynth (SAConPlus1 TCHole2)
                                        (runsynth++ (ziplem-plus2 ih2)
                                         (DoSynth (SAMove EMPlusParent2)
                                          (DoSynth (SAMove EMPlusFirstChild)
                                           (runsynth++ (ziplem-plus1 ih1)
                                            (DoSynth (SAMove EMPlusParent1) DoRefl)))))

    construct-synth (SNEHole wt) with construct-synth wt
    ... | (l , ih) = l ++ construct nehole :: move parent :: [] ,
                     runsynth++ ih
                         (DoSynth SAConNEHole (DoSynth (SAMove EMNEHoleParent) DoRefl))

    -- construction of expressions in analytic positions
    construct-ana : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e <= t) →
                                Σ[ L ∈ List action ]
                                   runana Γ ▹ <||> ◃ L ▹ e ◃ t
    construct-ana (ASubsume x c) with construct-synth x
    ... | (l , ih) = construct nehole :: l ++ (move parent :: finish :: []) ,
                     DoAna (AASubsume EETop SEHole SAConNEHole TCHole1)
                      (runana++  (ziplem-nehole-b SEHole c ih)
                        (DoAna (AAMove EMNEHoleParent)
                          (DoAna (AAFinish (ASubsume x c)) DoRefl)))

    construct-ana (ALam a m e) with construct-ana e
    ... | (l , ih) = construct (lam _) :: (l ++ [ move parent ]) ,
                     DoAna (AAConLam1 a m)
                         (runana++ (ziplem-lam a m ih)
                          (DoAna (AAMove EMLamParent) DoRefl))

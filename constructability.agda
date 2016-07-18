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
  ... | (l1 , ih1) | (l2 , ih2)= l1 ++ construct arrow :: l2 ++ [ move parent ] ,
                                 runtype++ ih1
                                   (DoType TMConArrow
                                     (runtype++ (runtype-cong2 ih2)
                                       (DoType TMParent2 DoRefl)))

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
                                        (runsynth++ (lem-tscong ETTop ETTop ih1)
                                         (DoSynth (SAMove EMAscParent2)
                                          (DoSynth (SAMove EMAscFirstChild)
                                           (runsynth++ (lem-anasynthasc ih2)
                                            (DoSynth (SAMove EMAscParent1) DoRefl)))))

    construct-synth (SAp e1 m e2) with construct-synth e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct ap :: (l2 ++ [ move parent ]) ,
                                    runsynth++ ih1
                                        (DoSynth (SAConApArr m)
                                         (runsynth++ (synth-ana-ap2-cong e1 m ih2)
                                          (DoSynth (SAMove EMApParent2) DoRefl)))

    construct-synth (SPlus e1 e2 ) with construct-ana e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) = construct plus :: (l2 ++ move parent :: move firstChild :: (l1 ++ [ move parent ])) ,
                                    DoSynth (SAConPlus1 TCHole2)
                                        (runsynth++ (synth-ana-plus2-cong ih2)
                                         (DoSynth (SAMove EMPlusParent2)
                                          (DoSynth (SAMove EMPlusFirstChild)
                                           (runsynth++ (synth-ana-plus1-cong ih1)
                                            (DoSynth (SAMove EMPlusParent1) DoRefl)))))

    construct-synth (SNEHole wt) with construct-synth wt
    ... | (l , ih) = l ++ construct nehole :: move parent :: [] ,
                     runsynth++ ih
                         (DoSynth SAConNEHole (DoSynth (SAMove EMNEHoleParent) DoRefl))

    -- construction of expressions in analytic positions
    construct-ana : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e <= t) →
                                Σ[ L ∈ List action ]
                                   runana Γ ▹ <||> ◃ L ▹ e ◃ t
    construct-ana (ASubsume {e = e} x x₁) with construct-synth x
    ... | (l , ih) = construct nehole :: l ++ (move parent :: finish :: []) ,
                     DoAna (AASubsume EETop SEHole SAConNEHole TCHole1)
                      (runana++ {L1 = l} {e' = <| ▹ e ◃ |>} (ziplem-nehole {!!} x x₁ ih)
                        (DoAna (AAMove EMNEHoleParent)
                          (DoAna (AAFinish (ASubsume x x₁)) DoRefl)))

    construct-ana (ALam a m e) with construct-ana e
    ... | (l , ih) = construct (lam _) :: (l ++ [ move parent ])
                     , DoAna (AAConLam1 a m)
                         (runana++ (ana-lam-cong a m ih)
                          (DoAna (AAMove EMLamParent) DoRefl))

    -- ziplem-nehole : ∀{Γ t t' l e} →
    --                 t ~ t' →
    --                 runsynth Γ ▹ <||> ◃ <||> l ▹ e ◃ t' →
    --                 runana Γ <| ▹ <||> ◃ |> l <| ▹ e ◃ |> t


    ziplem-nehole : ∀{Γ t t' l e e' e◆ tx} →
                    erase-e e e◆ →
                    Γ ⊢ e◆ => t' →
                    t ~ t' →
                    runsynth Γ e tx l e' t' →
                    runana Γ <| e |> l <| e' |> t
    ziplem-nehole er wt c DoRefl = DoRefl
    ziplem-nehole er wt c (DoSynth x s) =
                  DoAna (AASubsume {!!} {!!} (SAZipHole er {!!} x) TCHole1)
                        {!!}

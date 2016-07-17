open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import checks

module constructability where
  construct-type : (t : τ̇) → Σ[ L ∈ List action ] runtype (▹ <||> ◃) L (▹ t ◃)
  construct-type num = [ construct num ] , (DoType TMConNum DoRefl)
  construct-type <||> = [ del ] , DoType TMDel DoRefl
  construct-type (t1 ==> t2) with construct-type t1 | construct-type t2
  ... | (l1 , ih1) | (l2 , ih2)= l1 ++ construct arrow :: l2 ++ [ move parent ] ,
                   runtype++ ih1
                     (DoType TMConArrow
                       (runtype++ (runtype-cong2 ih2) (DoType TMParent2 DoRefl)))

  mutual
    construct-synth : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e => t) →
                                  Σ[ L ∈ List action ]
                                     runsynth Γ ▹ <||> ◃ <||> L ▹ e ◃ t
    construct-synth {t = t} (SAsc x) with construct-type t | construct-ana x
    ... | (l1 , ih1) | (l2 , ih2) = construct asc :: (l1 ++ move parent :: move firstChild :: (l2 ++ [ move parent ]))
                                    , DoSynth SAConAsc
                                        (runsynth++ (lem-tscong ETTop ETTop ih1)
                                         (DoSynth (SAMove EMAscParent2)
                                          (DoSynth (SAMove EMAscFirstChild)
                                           (runsynth++ (lem-anasynthasc ih2)
                                            (DoSynth (SAMove EMAscParent1) DoRefl)))))
    construct-synth (SVar {n = n} x) = [ construct (var n) ]
                                    , DoSynth (SAConVar x) DoRefl
    construct-synth (SAp e1 m e2) with construct-synth e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) = l1 ++ construct ap :: (l2 ++ [ move parent ])
                                    , runsynth++ ih1
                                        (DoSynth (SAConApArr m)
                                         (runsynth++ (synth-ana-ap2-cong e1 m ih2)
                                          (DoSynth (SAMove EMApParent2) DoRefl)))
    construct-synth (SNum {n = n}) = [ construct (numlit n) ]
                                    , DoSynth SAConNumlit DoRefl
    construct-synth (SPlus e1 e2 ) with construct-ana e1 | construct-ana e2
    ... | (l1 , ih1) | (l2 , ih2) = construct plus :: (l2 ++ move parent :: move firstChild :: (l1 ++ [ move parent ]))
                                    , DoSynth (SAConPlus1 TCHole2)
                                        (runsynth++ (synth-ana-plus2-cong ih2)
                                         (DoSynth (SAMove EMPlusParent2)
                                          (DoSynth (SAMove EMPlusFirstChild)
                                           (runsynth++ (synth-ana-plus1-cong ih1)
                                            (DoSynth (SAMove EMPlusParent1) DoRefl)))))
    construct-synth SEHole = [ del ]
                             , DoSynth SADel DoRefl
    construct-synth (SNEHole wt) with construct-synth wt
    ... | (l , ih) = l ++ construct nehole :: move parent :: []
                     , runsynth++ ih
                         (DoSynth SAConNEHole (DoSynth (SAMove EMNEHoleParent) DoRefl))

    construct-ana : {Γ : ·ctx} {t : τ̇} {e : ė} → (Γ ⊢ e <= t) →
                                Σ[ L ∈ List action ]
                                   runana Γ ▹ <||> ◃ L ▹ e ◃ t
    construct-ana (ASubsume x x₁) = {!!}
    construct-ana (ALam {x = x} a m e) with construct-ana e
    ... | (l , ih) = construct (lam x) :: (l ++ [ move parent ])
                     , DoAna (AAConLam1 a m)
                         (runana++ (ana-lam-cong a m ih)
                          (DoAna (AAMove EMLamParent) DoRefl))

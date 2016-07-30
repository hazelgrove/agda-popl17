open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import sensible
open import moveerase
open import checks

module examples where

  -- this module contains small examples that demonstrate the judgements
  -- and definitions in action. a few of them are directly from the paper,
  -- to aid in comparision between the on-paper notation and the
  -- corresponding agda syntax.

  -- this is figure one from the paper in full detail
  l : List action
  l = construct (lam 0)
    :: construct num
    :: move nextSib
    :: construct num
    :: move parent
    :: move parent
    :: move firstChild
    :: move firstChild
    :: construct (var 0)
    :: construct plus
    :: construct (numlit 1)
    :: []


  figure1 : runsynth ∅ ▹ <||> ◃ <||> l (·λ 0 (X 0 ·+₂ ▹ N 1 ◃) ·:₁ (num ==> num)) (num ==> num)
  figure1 =
        DoSynth (SAConLam refl)
        (DoSynth (SAZipAsc2 (TMArrZip1 TMConNum) (ETArrL ETTop) (ETArrL ETTop) (ALam refl MAArr (ASubsume SEHole TCRefl)))
        (DoSynth (SAZipAsc2 TMArrNextSib (ETArrR ETTop) (ETArrL ETTop) (ALam refl MAArr (ASubsume SEHole TCRefl)))
        (DoSynth (SAZipAsc2 (TMArrZip2 TMConNum) (ETArrR ETTop) (ETArrR ETTop) (ALam refl MAArr (ASubsume SEHole TCHole1)))
        (DoSynth (SAZipAsc2 TMArrParent2 ETTop (ETArrR ETTop) (ALam refl MAArr (ASubsume SEHole TCHole1)))
        (DoSynth (SAMove EMAscParent2)
        (DoSynth (SAMove EMAscFirstChild)
        (DoSynth (SAZipAsc1 (AAMove EMLamFirstChild))
        (DoSynth (SAZipAsc1 (AAZipLam refl MAArr (AASubsume EETop SEHole (SAConVar refl) TCRefl)))
        (DoSynth (SAZipAsc1 (AAZipLam refl MAArr (AASubsume EETop (SVar refl) (SAConPlus1 TCRefl) TCRefl)))
        (DoSynth (SAZipAsc1 (AAZipLam refl MAArr (AASubsume (EEPlusR EETop) (SPlus (ASubsume (SVar refl) TCRefl)
                                                            (ASubsume SEHole TCHole1))
                                                            (SAZipPlus2 (AASubsume EETop SEHole SAConNumlit TCRefl)) TCRefl)))
        DoRefl))))))))))

open import Nat
open import Prelude
open import List
open import core
open import judgemental-erase
open import sensibility
open import moveerase
open import checks

module examples where
  -- the function (λx. x + 1) where x is named "0".
  add1 : ė
  add1 = ·λ 0 (X 0 ·+ N 1)

  -- this is the derivation that fn has type num ==> num
  ex1 : ∅ ⊢ add1 <= (num ==> num)
  ex1 = ALam refl MAArr (ASubsume
                           (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume SNum TCRefl))
                           TCRefl)

  -- the derivation that when applied to the numeric argument 10 add1
  -- produces a num.
  ex2 : ∅ ⊢ (add1 ·: (num ==> num)) ∘ (N 10) => num
  ex2 = SAp (SAsc ex1) MAArr (ASubsume SNum TCRefl)

  -- the slightly longer derivation that argues that add1 applied to a
  -- variable that's known to be a num produces a num
  ex2b : (∅ ,, (1 , num)) ⊢ (add1 ·: (num ==> num)) ∘ (X 1) => num
  ex2b = SAp (SAsc (ALam refl MAArr (ASubsume
                                       (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume SNum TCRefl))
                                       TCRefl))) MAArr (ASubsume (SVar refl) TCRefl)

  -- eta-expanding addition to curry it gets num → num → num
  ex3 : ∅ ⊢ ·λ 0 ( (·λ 1 (X 0 ·+ X 1)) ·: (num ==> num)  )
               <= (num ==> (num ==> num))
  ex3 = ALam refl MAArr (ASubsume (SAsc (ALam refl MAArr (ASubsume
                                                            (SPlus (ASubsume (SVar refl) TCRefl) (ASubsume (SVar refl) TCRefl))
                                                            TCRefl))) TCRefl)

  -- applying three to four has type hole -- but there is no action that
  -- can fill the hole in the type so this term is forever incomplete.
  ex4 : ∅ ⊢ ((N 3) ·: ⦇-⦈) ∘ (N 4) => ⦇-⦈
  ex4 = SAp (SAsc (ASubsume SNum TCHole2)) MAHole (ASubsume SNum TCHole2)

  -- this module contains small examples that demonstrate the judgements
  -- and definitions in action. a few of them are directly from the paper,
  -- to aid in comparision between the on-paper notation and the
  -- corresponding agda syntax.

  -- these smaller derivations motivate the need for the zipper rules: you
  -- have to unzip down to the point of the structure where you want to
  -- apply an edit, do the local edit rule, and then put it back together
  -- around you
  talk0 :  ∅ ⊢ (▹ ⦇-⦈ ◃ ·+₁ ⦇-⦈) => num ~ construct (numlit 7) ~>
               (▹ N 7 ◃  ·+₁ ⦇-⦈) => num
  talk0 = SAZipPlus1 (AASubsume EETop SEHole SAConNumlit TCRefl)

  talk1 : ∅ ⊢ (·λ 0 ⦇-⦈ ·:₂ (▹ ⦇-⦈ ◃ ==>₁ ⦇-⦈)) => (⦇-⦈ ==> ⦇-⦈) ~ construct num ~>
              (·λ 0 ⦇-⦈ ·:₂ (▹ num ◃ ==>₁ ⦇-⦈)) => (num ==> ⦇-⦈)
  talk1 = SAZipAsc2 (TMArrZip1 TMConNum) (ETArrL ETTop) (ETArrL ETTop)
                    (ALam refl MAArr (ASubsume SEHole TCRefl))


  -- this is figure one from the paper in full detail
  fig1-l : List action
  fig1-l = construct (lam 0)
    :: construct num
    :: move parent
    :: move (child 2)
    :: construct num
    :: move parent
    :: move parent
    :: move (child 1)
    :: move (child 1)
    :: construct (var 0)
    :: construct plus
    :: construct (numlit 1)
    :: []


  figure1 : runsynth ∅ ▹ ⦇-⦈ ◃ ⦇-⦈ fig1-l (·λ 0 (X 0 ·+₂ ▹ N 1 ◃) ·:₁ (num ==> num)) (num ==> num)
  figure1 =
        DoSynth (SAConLam refl)
        (DoSynth (SAZipAsc2 (TMArrZip1 TMConNum) (ETArrL ETTop) (ETArrL ETTop) (ALam refl MAArr (ASubsume SEHole TCRefl)))
        (DoSynth (SAZipAsc2 TMArrParent1 ETTop (ETArrL ETTop)
                    (ALam refl MAArr (ASubsume SEHole TCRefl)))
        (DoSynth (SAZipAsc2 TMArrChild2 (ETArrR ETTop) ETTop
                    (ALam refl MAArr (ASubsume SEHole TCRefl)))
        (DoSynth (SAZipAsc2 (TMArrZip2 TMConNum) (ETArrR ETTop) (ETArrR ETTop) (ALam refl MAArr (ASubsume SEHole TCHole1)))
        (DoSynth (SAZipAsc2 TMArrParent2 ETTop (ETArrR ETTop) (ALam refl MAArr (ASubsume SEHole TCHole1)))
        (DoSynth (SAMove EMAscParent2)
        (DoSynth (SAMove EMAscChild1)
        (DoSynth (SAZipAsc1 (AAMove EMLamChild1))
        (DoSynth (SAZipAsc1 (AAZipLam refl MAArr (AASubsume EETop SEHole (SAConVar refl) TCRefl)))
        (DoSynth (SAZipAsc1 (AAZipLam refl MAArr (AASubsume EETop (SVar refl) (SAConPlus1 TCRefl) TCRefl)))
        (DoSynth (SAZipAsc1 (AAZipLam refl MAArr (AASubsume (EEPlusR EETop) (SPlus (ASubsume (SVar refl) TCRefl)
                                                            (ASubsume SEHole TCHole1))
                                                            (SAZipPlus2 (AASubsume EETop SEHole SAConNumlit TCRefl)) TCRefl)))
        DoRefl)))))))))))

  -- this is figure two from the paper
  incr : Nat
  incr = 0

  fig2-l : List action
  fig2-l =    construct (var incr)
           :: construct ap
           :: construct (var incr)
           :: construct ap
           :: construct (numlit 3)
           :: move parent
           :: move parent
           :: finish
           :: []

  figure2 : runsynth (∅ ,, (incr , num ==> num)) ▹ ⦇-⦈ ◃ ⦇-⦈ fig2-l (X incr ∘₂ ▹ X incr ∘ (N 3) ◃)  num
  figure2 =  DoSynth (SAConVar refl)
            (DoSynth (SAConApArr MAArr)
            (DoSynth (SAZipApAna MAArr (SVar refl) (AAConVar (λ ()) refl))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AASubsume (EENEHole EETop) (SNEHole (SVar refl)) (SAZipHole EETop (SVar refl) (SAConApArr MAArr)) TCHole1))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AASubsume (EENEHole (EEApR EETop)) (SNEHole (SAp (SVar refl) MAArr (ASubsume SEHole TCHole1))) (SAZipHole (EEApR EETop) (SAp (SVar refl) MAArr (ASubsume SEHole TCHole1)) (SAZipApAna MAArr (SVar refl)
                                                                                                                    (AASubsume EETop SEHole SAConNumlit TCRefl))) TCHole1))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AASubsume (EENEHole (EEApR EETop)) (SNEHole (SAp (SVar refl) MAArr (ASubsume SNum TCRefl))) (SAZipHole (EEApR EETop) (SAp (SVar refl) MAArr (ASubsume SNum TCRefl)) (SAMove EMApParent2)) TCHole1))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AAMove EMNEHoleParent))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AAFinish (ASubsume (SAp (SVar refl) MAArr (ASubsume SNum TCRefl)) TCRefl)))
             DoRefl)))) )))


  --- this demonstrates that the other ordering discussed is also fine. it
  --- results in different proof terms and actions but ultimately produces
  --- the same expression. there are many other lists of actions that would
  --- also work, these are just two.
  fig2alt-l : List action
  fig2alt-l =  construct (var incr)
           :: construct ap
           :: construct ap
           :: construct (numlit 3)
           :: move parent
           :: move (child 1)
           :: construct (var incr)
           :: move parent
           :: []

  figure2alt : runsynth (∅ ,, (incr , num ==> num)) ▹ ⦇-⦈ ◃ ⦇-⦈ fig2alt-l (X incr ∘₂ ▹ X incr ∘ (N 3) ◃)  num
  figure2alt = DoSynth (SAConVar refl)
            (DoSynth (SAConApArr MAArr)
            (DoSynth (SAZipApAna MAArr (SVar refl) (AASubsume EETop SEHole (SAConApArr MAHole) TCHole1))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AASubsume (EEApR EETop) (SAp SEHole MAHole (ASubsume SEHole TCRefl)) (SAZipApAna MAHole SEHole
                                                                                                                            (AASubsume EETop SEHole SAConNumlit TCHole2)) TCHole1))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AAMove EMApParent2))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AAMove EMApChild1))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AASubsume (EEApL EETop) (SAp SEHole MAHole (ASubsume SNum TCHole2)) (SAZipApArr MAArr EETop SEHole (SAConVar refl)
                                                                                                                           (ASubsume SNum TCRefl)) TCRefl))
            (DoSynth (SAZipApAna MAArr (SVar refl) (AAMove EMApParent1))
            ( DoRefl))))))))


  -- these motivates why actions aren't deterministic, and why it's
  -- reasonable to ban the derivations that we do. the things that differ
  -- in the term as a result of the appeal to subsumption in the second
  -- derivation aren't needed -- the ascription is redundant because the
  -- type is already pinned to num ==> num, so that's the only thing that
  -- could fill the holes produced.
  notdet1 : ∅ ⊢ ▹ ⦇-⦈ ◃ ~ construct (lam 0) ~> ·λ 0 ▹ ⦇-⦈ ◃ ⇐ (num ==> num)
  notdet1 = AAConLam1 refl MAArr

  notdet2 : ∅ ⊢ ▹ ⦇-⦈ ◃ ~ construct (lam 0) ~> ·λ 0 ⦇-⦈ ·:₂ (▹ ⦇-⦈ ◃ ==>₁ ⦇-⦈) ⇐ (num ==> num)
  notdet2 = AASubsume EETop SEHole (SAConLam refl) (TCArr TCHole1 TCHole1)

import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter
import QEC.Coding.FiniteAlternatingConstruction.RZDecoderAdapter
import QEC.Coding.FourDimensionalToricCode.Decoder.LevelTwoHistory

/-!
# Actual alternating histories stopping at physical C2

The steps are the actual indexed adapters and the base is the executable
level-two decoder. No step, correctness certificate, or history is supplied.
-/
namespace QEC.Coding.BDL26OwnerIncidenceMasks

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open MultiscaleDecoder
open scoped Classical

noncomputable def actualStep (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStep (indexedDecoderData S depth) i :=
  fun sigma => if h : i.val % 2 = 0 then BDL26RXDecoderAdapter.rxStepOutput S depth i h sigma
  else BDL26RZDecoderAdapter.rzStepOutput S depth i h sigma

theorem actualStep_rx (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) :
    actualStep S depth i = BDL26RXDecoderAdapter.rxStepOutput S depth i h := by
  funext sigma
  exact dif_pos h

theorem actualStep_rz (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : ¬i.val % 2 = 0) :
    actualStep S depth i = BDL26RZDecoderAdapter.rzStepOutput S depth i h := by
  funext sigma
  exact dif_neg h

theorem actualStep_relation (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    AssemblyStepRelation (indexedDecoderData S depth) i (actualStep S depth i) := by
  by_cases h : i.val % 2 = 0
  · rw [actualStep_rx S depth i h]
    exact BDL26RXDecoderAdapter.rxStepOutput_assembly_relation S depth i h
  · rw [actualStep_rz S depth i h]
    refine ⟨?_, ?_⟩
    · intro sigma
      rfl
    · intro sigma
      exact (BDL26RZDecoderAdapter.rzStepOutput S depth i h sigma).relation

noncomputable def actualAboveTwoSteps (S : OddScale) (n : Nat) :
    LevelTwoHistory.AboveTwoSteps (indexedDecoderData S (n + 2)) where
  step := fun i _ => actualStep S (n + 2) i
  relation := fun i _ => actualStep_relation S (n + 2) i

/-- The physical level-two carrier is definitionally the actual state-two code. -/
noncomputable def actualBaseDecode (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) :
    (indexedFamily S (n + 2)).Correction
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) :=
  BDL26LevelTwoDecoder.decode S sigma.val

theorem actualBaseDecode_rightInverse (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) :
    (indexedFamily S (n + 2)).coboundary1
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))
      (actualBaseDecode S n sigma) = sigma.val := by
  rw [indexedFamily_coboundary1]
  apply BDL26LevelTwoDecoder.decode_rightInverse
  have hs : sigma.val ∈ LinearMap.range ((indexedFamily S (n + 2)).coboundary1
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) := sigma.property
  rw [indexedFamily_coboundary1] at hs
  exact hs

noncomputable def actualBase (S : OddScale) (n : Nat) :
    AuditedBaseDecoder (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))) :=
  LevelTwoHistory.suffixBase _ (actualBaseDecode S n) (actualBaseDecode_rightInverse S n)

noncomputable def actualHistory (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    CorrectionHistory (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))) :=
  LevelTwoHistory.stoppedHistory _ (actualAboveTwoSteps S n) (actualBase S n) sigma

theorem actualHistory_length (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (actualHistory S n sigma).length = n + 1 :=
  LevelTwoHistory.stoppedHistory_length (n := n) (indexedDecoderData S (n + 2))
    (actualAboveTwoSteps S n) (actualBase S n) sigma

theorem actualHistory_syndrome (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2))
      (historyLiftedCorrection (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2)))
        (actualHistory S n sigma)) = sigma.val :=
  LevelTwoHistory.stoppedHistory_syndrome (n := n) (indexedDecoderData S (n + 2))
    (actualAboveTwoSteps S n) (actualBase S n) sigma

theorem actualHistory_readout_below_two (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
      (actualHistory S n sigma) i = 0 :=
  LevelTwoHistory.syndromeReadout_below_two _ _ i hi

/-- Suffix output copies exactly the actual adapter list, including zero pieces. -/
theorem actualSuffix_components (S : OddScale) (n : Nat) (i : StepIndex n)
    (sigma : (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))).family.Syndrome i.succ) :
    ((LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)).step i sigma).localComponents =
      (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) sigma).localComponents := rfl

theorem actualSuffix_supports (S : OddScale) (n : Nat) (i : StepIndex n)
    (sigma : (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))).family.Syndrome i.succ) :
    ((LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)).step i sigma).componentSupports =
      (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) sigma).componentSupports := rfl

theorem actualSuffix_coboundaries (S : OddScale) (n : Nat) (i : StepIndex n)
    (sigma : (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))).family.Syndrome i.succ) :
    ((LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)).step i sigma).componentCoboundaries =
      (actualStep S (n + 2) (LevelTwoHistory.physicalStep i) sigma).componentCoboundaries := rfl

end QEC.Coding.BDL26OwnerIncidenceMasks

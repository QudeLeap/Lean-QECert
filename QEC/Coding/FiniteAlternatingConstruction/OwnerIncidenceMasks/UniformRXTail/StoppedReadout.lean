import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.History

/-! # Zero-input readouts in the actual C2-stopped history -/
namespace QEC.Coding.BDL26UniformRXTail

open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

theorem actualStep_zero_coarse (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (hs : sigma.val = 0) :
    (actualStep S depth i sigma).coarse.val = 0 := by
  apply (HammingWeight_eq_zero_iff _).mp
  by_cases h : i.val % 2 = 0
  · rw [actualStep_rx S depth i h]
    have hw := BDL26RXDecoderAdapter.rxStepOutput_weight S depth i h sigma
    rw [hs, HammingWeight_zero] at hw
    omega
  · rw [actualStep_rz S depth i h]
    have hw := BDL26RZDecoderAdapter.rzStepOutput_weight S depth i h sigma
    rw [hs, HammingWeight_zero] at hw
    exact Nat.eq_zero_of_le_zero hw

theorem actualHistory_zero_inputs (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (hs : sigma.val = 0) :
    ∀ e ∈ actualHistory S n sigma, e.inputSyndrome.2.val = 0 := by
  exact LevelTwoHistory.stoppedHistory_zero_inputs
    (indexedDecoderData S (n + 2)) (actualAboveTwoSteps S n) (actualBase S n)
    (fun i _ s hz => actualStep_zero_coarse S (n + 2) i s hz) sigma hs

/-- Every physical readout is zero; length and correction snapshots are retained. -/
theorem actualHistory_zero_readout (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (hs : sigma.val = 0) (i : LevelIndex (n + 2)) :
    LevelTwoHistory.syndromeReadout (indexedDecoderData S (n + 2))
      (actualHistory S n sigma) i = 0 := by
  unfold LevelTwoHistory.syndromeReadout LevelTwoHistory.physicalInputSnapshots
  rw [List.map_map]
  apply List.sum_eq_zero
  intro w hw
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
  dsimp only [Function.comp_apply]
  split
  · rename_i h
    have hz := actualHistory_zero_inputs S n sigma hs e he
    cases h
    exact hz
  · rfl

end QEC.Coding.BDL26UniformRXTail

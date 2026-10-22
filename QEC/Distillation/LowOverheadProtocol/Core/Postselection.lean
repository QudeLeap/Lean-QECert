import QEC.Distillation.LowOverheadProtocol.Core.SyndromeDecoding

/-!
# HH18 coarse syndrome postselection

This module observes the actual finite HH18 joint-syndrome Kraus family only
through the source-level accepted/rejected distinction: the all-positive
syndrome is accepted and every other syndrome is rejected.  The resulting
instrument keeps the original physical branches, exposes their Born weights,
and forms a conditional density only from a strictly positive weight witness.

It deliberately stops before packaging the Kraus family as a channel, a total
decoder, a `DistillationRun`, an error or success estimate, and any
concatenation construction.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Postselection

open Coding Semantics
open Coding.PauliSymplectic
open HH18SyndromeDecoding
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

universe u

/-- Coarse-grain the full HH18 syndrome: only the all-positive syndrome is
accepted. -/
def syndromeOutcome (syndrome : Syndrome) : DistillationOutcome :=
  if syndrome = HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 then
    .accepted
  else
    .rejected

/-- The coarse accepted outcome is exactly the all-positive syndrome. -/
theorem syndromeOutcome_accepted_iff (syndrome : Syndrome) :
    syndromeOutcome syndrome = .accepted ↔
      syndrome = HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 := by
  simp [syndromeOutcome]

/-- The coarse rejected outcome is exactly every non-all-positive syndrome. -/
theorem syndromeOutcome_rejected_iff (syndrome : Syndrome) :
    syndromeOutcome syndrome = .rejected ↔
      syndrome ≠ HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4 := by
  simp [syndromeOutcome]

/-- The actual complete HH18 joint measurement, observed only as accept/reject. -/
noncomputable def postselectionInstrument :
    FiniteInstrument Syndrome DistillationOutcome PhysicalRegister PhysicalRegister where
  kraus := jointStabilizerKrausFamily
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)
  observe := syndromeOutcome

/-- Completeness comes from the real #759 joint-projector resolution. -/
theorem postselectionInstrument_complete :
    postselectionInstrument.kraus.Complete :=
  jointStabilizerKrausFamily_complete
    (HH18PuncturedReedMuller.checkGenerator 0 1 4)
    (HH18PuncturedReedMuller.checkGenerator_commutes
      HH18NoisyInput.hh18_15_1_0_admissible)

/-- The unnormalized physical branch retained by one coarse outcome. -/
noncomputable def rawPostselectionBranch (outcome : DistillationOutcome)
    (input : Operator PhysicalRegister) : Operator PhysicalRegister :=
  postselectionInstrument.branchOperator outcome input

/-- The same raw coarse endpoint on a normalized physical density input. -/
noncomputable def rawPostselectionEndpoint (outcome : DistillationOutcome)
    (rho : DensityOperator PhysicalRegister) : Operator PhysicalRegister :=
  rawPostselectionBranch outcome rho.toOperator

/-- The actual Born weight of one coarse postselection outcome. -/
noncomputable def postselectionWeight (outcome : DistillationOutcome)
    (rho : DensityOperator PhysicalRegister) : Real :=
  postselectionInstrument.bornWeight outcome rho

/-- Every coarse outcome weight is derived from the physical Kraus branch. -/
theorem postselectionWeight_nonneg (outcome : DistillationOutcome)
    (rho : DensityOperator PhysicalRegister) :
    0 ≤ postselectionWeight outcome rho :=
  postselectionInstrument.bornWeight_nonneg outcome rho

/-- Accepted and rejected weights exhaust the complete joint measurement. -/
theorem postselectionWeight_sum (rho : DensityOperator PhysicalRegister) :
    postselectionWeight .accepted rho + postselectionWeight .rejected rho = 1 := by
  have h := postselectionInstrument.sum_bornWeight_eq_one
    postselectionInstrument_complete rho
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at h
  simpa [postselectionWeight] using h

/-- A zero-weight coarse endpoint remains its literal raw zero operator. -/
theorem rawPostselectionEndpoint_eq_zero_of_weight_eq_zero
    (outcome : DistillationOutcome) (rho : DensityOperator PhysicalRegister)
    (hzero : postselectionWeight outcome rho = 0) :
    rawPostselectionEndpoint outcome rho = 0 := by
  simpa [rawPostselectionEndpoint, rawPostselectionBranch, postselectionWeight] using
    (postselectionInstrument.branchOperator_eq_zero_of_bornWeight_eq_zero
      outcome rho hzero)

/-- Normalize a coarse endpoint only after proving its actual Born weight positive. -/
noncomputable def postselectionConditional (rho : DensityOperator PhysicalRegister)
    (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    DensityOperator PhysicalRegister :=
  postselectionInstrument.conditionalDensity outcome rho hpos

/-- The normalized branch is exactly the inverse-weight scaling of its raw endpoint. -/
@[simp] theorem postselectionConditional_toOperator
    (rho : DensityOperator PhysicalRegister) (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    (postselectionConditional rho outcome hpos).toOperator =
      ((postselectionWeight outcome rho : Complex)⁻¹) •
        rawPostselectionEndpoint outcome rho :=
  rfl

/-- Weighting a positive conditional density recovers the physical raw endpoint. -/
theorem postselectionWeight_smul_conditional_toOperator
    (rho : DensityOperator PhysicalRegister) (outcome : DistillationOutcome)
    (hpos : 0 < postselectionWeight outcome rho) :
    (postselectionWeight outcome rho : Complex) •
        (postselectionConditional rho outcome hpos).toOperator =
      rawPostselectionEndpoint outcome rho := by
  simpa [postselectionWeight, postselectionConditional,
    rawPostselectionEndpoint, rawPostselectionBranch] using
      (postselectionInstrument.bornWeight_smul_conditionalDensity_toOperator
        outcome rho hpos)

/-- Coarse acceptance retains exactly the existing all-positive injected endpoint. -/
theorem rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    rawPostselectionBranch .accepted (injectedBranchOperator error outcomes) =
      rawAcceptedEndpoint error outcomes := by
  classical
  unfold rawPostselectionBranch postselectionInstrument rawAcceptedEndpoint
    rawSyndromeBranch fullSyndromeInstrument
  simp only [FiniteInstrument.branchOperator_apply]
  apply Finset.sum_congr rfl
  intro syndrome _hsyndrome
  by_cases hsyndrome : syndrome =
      HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4
  · subst syndrome
    simp [syndromeOutcome]
  · simp [syndromeOutcome, hsyndrome]

/-- Coarse rejection retains exactly the finite sum of all non-all-positive branches. -/
theorem rawPostselectionBranch_rejected_eq_rawRejectedEndpoint
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    rawPostselectionBranch .rejected (injectedBranchOperator error outcomes) =
      rawRejectedEndpoint error outcomes := by
  classical
  unfold rawPostselectionBranch postselectionInstrument rawRejectedEndpoint
    rawSyndromeBranch fullSyndromeInstrument
  simp only [FiniteInstrument.branchOperator_apply]
  apply Finset.sum_congr rfl
  intro syndrome _hsyndrome
  by_cases hsyndrome : syndrome =
      HH18PuncturedReedMuller.allPositiveSyndrome 0 1 4
  · subst syndrome
    simp [syndromeOutcome]
  · simp [syndromeOutcome, hsyndrome]
    symm
    erw [Fintype.sum_eq_single syndrome]
    · exact if_pos rfl
    · intro other hother
      exact if_neg hother

end HH18Postselection
end Distillation
end QEC

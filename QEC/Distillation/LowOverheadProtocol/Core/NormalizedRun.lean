import QEC.Distillation.LowOverheadProtocol.Core.PhysicalEndpoint
import QEC.Distillation.LowOverheadProtocol.Core.Decoder

/-!
# HH18 normalized physical and decoded run

This layer turns the concrete raw endpoints into a total physical run and then
postprocesses it with the actual CPTP decoder.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instNormalizedRunClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The complete one-level HH18 operation including resource consumption,
syndrome/postselection, and total logical decoding. -/
noncomputable def decodedOperation : QuantumChannel PhysicalRegister LogicalRegister :=
  QuantumChannel.comp decoderChannel physicalOperation

/-! ## Resource-dependent normalized branches and run -/

/-- Normalize a physical endpoint only when its actual Born weight is
positive. -/
noncomputable def endpointConditional
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome)
    (hpos : 0 < endpointWeight inputs outcome) : DensityOperator PhysicalRegister :=
  HH18Postselection.postselectionInstrument.conditionalDensity outcome
    (resourcePreSyndromeState inputs) hpos

@[simp] theorem endpointConditional_toOperator
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome)
    (hpos : 0 < endpointWeight inputs outcome) :
    (endpointConditional inputs outcome hpos).toOperator =
      ((endpointWeight inputs outcome : Complex)⁻¹) • rawEndpoint inputs outcome :=
  rfl

/-- A physical density used only to make a zero-probability interface branch
total; it is not a claimed rejected HH18 history. -/
noncomputable def endpointFallback : DensityOperator PhysicalRegister :=
  DensityOperator.pureDensity (errorBranchState 0) (errorBranchState_normSq 0)

/-- The endpoint conditional at positive mass, with the above purely
interface-level completion at zero mass. -/
noncomputable def endpointCompletion
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome) : DensityOperator PhysicalRegister :=
  if hpos : 0 < endpointWeight inputs outcome then
    endpointConditional inputs outcome hpos
  else endpointFallback

theorem rawEndpoint_eq_zero_of_weight_eq_zero
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome)
    (hzero : endpointWeight inputs outcome = 0) :
    rawEndpoint inputs outcome = 0 :=
  HH18Postselection.postselectionInstrument.branchOperator_eq_zero_of_bornWeight_eq_zero
    outcome (resourcePreSyndromeState inputs) hzero

/-- Weighting either normalized/completed branch reconstructs its literal raw
operator. -/
theorem endpointWeight_smul_completion_toOperator
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome) :
    (endpointWeight inputs outcome : Complex) •
        (endpointCompletion inputs outcome).toOperator = rawEndpoint inputs outcome := by
  classical
  by_cases hpos : 0 < endpointWeight inputs outcome
  · rw [endpointCompletion, dif_pos hpos]
    simpa [endpointWeight, endpointConditional, rawEndpoint] using
      HH18Postselection.postselectionInstrument.bornWeight_smul_conditionalDensity_toOperator
        outcome (resourcePreSyndromeState inputs) hpos
  · rw [endpointCompletion, dif_neg hpos]
    have hzero : endpointWeight inputs outcome = 0 :=
      le_antisymm (not_lt.mp hpos) (endpointWeight_nonneg inputs outcome)
    rw [hzero, rawEndpoint_eq_zero_of_weight_eq_zero inputs outcome hzero]
    simp

/-- The complete supplied-resource physical operation before decoding. -/
noncomputable def resourceSyndromeOperation : QuantumChannel PhysicalRegister PhysicalRegister :=
  physicalOperation

/-- The complete raw channel is the convex mixture of its actual accepted and
rejected normalized branches, without assuming either branch has positive
mass globally. -/
theorem resourceSyndromeOperation_output_decomposition
    (inputs : ResourceInput resourceCount QubitSpace) :
    resourceSyndromeOperation.mapDensity (prepareMeasuredResources inputs) =
      outcomeMixture (endpointWeight inputs .accepted)
        (endpointWeight_nonneg inputs .accepted)
        (by
          have hsum := endpointWeights_sum inputs
          linarith [endpointWeight_nonneg inputs .rejected])
        (endpointCompletion inputs .accepted)
        (endpointCompletion inputs .rejected) := by
  apply DensityOperator.ext_toOperator
  rw [resourceSyndromeOperation, physicalOperation, QuantumChannel.comp_mapDensity]
  change (((HH18Postselection.postselectionInstrument.kraus.toQuantumChannel
      HH18Postselection.postselectionInstrument_complete).mapDensity
        (resourcePreSyndromeState inputs)).toOperator = _)
  rw [← HH18Postselection.postselectionInstrument.sum_branchOperator_eq_mapDensity_toOperator
    HH18Postselection.postselectionInstrument_complete (resourcePreSyndromeState inputs)]
  change (∑ outcome, rawEndpoint inputs outcome) = _
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide]
  have hreject : 1 - endpointWeight inputs .accepted =
      endpointWeight inputs .rejected := by
    linarith [endpointWeights_sum inputs]
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide, hreject]
  rw [← endpointWeight_smul_completion_toOperator inputs .accepted,
    ← endpointWeight_smul_completion_toOperator inputs .rejected]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  rfl

/-- The parameter-free, physical one-level HH18 run.  It consumes every
supplied resource through the explicit `S` rotation, phase measurement,
finite word record, and syndrome channel above. -/
noncomputable def resourceSyndromeRun
    (inputs : ResourceInput resourceCount QubitSpace) :
    DistillationRun QubitSpace PhysicalRegister PhysicalRegister where
  resourceCount := resourceCount
  noisyInput := inputs
  prepareInput := prepareMeasuredResources
  operation := resourceSyndromeOperation
  successProbability := endpointWeight inputs .accepted
  success_nonneg := endpointWeight_nonneg inputs .accepted
  success_le_one := by
    have hsum := endpointWeights_sum inputs
    linarith [endpointWeight_nonneg inputs .rejected]
  acceptedOutput := endpointCompletion inputs .accepted
  rejectedOutput := endpointCompletion inputs .rejected
  output_decomposition := resourceSyndromeOperation_output_decomposition inputs

/-- The same actual run after the total CPTP logical decoder. -/
noncomputable def resourceDecodedRun
    (inputs : ResourceInput resourceCount QubitSpace) :
    DistillationRun QubitSpace PhysicalRegister LogicalRegister :=
  (resourceSyndromeRun inputs).postprocess decoderChannel

theorem resourceDecodedRun_operation
    (inputs : ResourceInput resourceCount QubitSpace) :
    (resourceDecodedRun inputs).operation = decodedOperation :=
  rfl

/-- At positive accepted Born mass, the decoded run reports the actual
decoded accepted conditional, not its zero-mass technical completion. -/
theorem resourceDecodedRun_acceptedOutput
    (inputs : ResourceInput resourceCount QubitSpace)
    (hpos : 0 < endpointWeight inputs .accepted) :
    (resourceDecodedRun inputs).acceptedOutput =
      decoderChannel.mapDensity (endpointConditional inputs .accepted hpos) := by
  change decoderChannel.mapDensity (endpointCompletion inputs .accepted) = _
  simp [endpointCompletion, hpos]

end HH18Protocol
end Distillation
end QEC

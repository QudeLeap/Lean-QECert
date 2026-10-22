import QEC.Distillation.LowOverheadProtocol.Parameterized.SuccessResidual
import QEC.Distillation.LowOverheadProtocol.Parameterized.Decoder

/-!
# Parameterized HH18 normalized run

This layer turns the parameterized raw physical endpoints into a total
`DistillationRun`, then postprocesses it with the actual total decoder.  A
zero-weight branch has an explicitly documented interface completion; the
physical conditional density itself is formed only with a positive Born-weight
witness.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instNormalizedRunClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The complete parameterized HH18 operation including actual resource
consumption, coarse postselection, and total logical decoding. -/
noncomputable def decodedOperation {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    QuantumChannel (PhysicalRegister m w) (LogicalRegister m w) :=
  QuantumChannel.comp (decoderChannel h) (physicalOperation h hdegree)

/-- Normalize a parameterized physical endpoint only under its actual positive
Born-weight witness. -/
noncomputable def endpointConditional {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome)
    (hpos : 0 < endpointWeight h hdegree inputs outcome) :
    DensityOperator (PhysicalRegister m w) :=
  postselectionConditional h (resourcePreSyndromeState h hdegree inputs) outcome hpos

@[simp] theorem endpointConditional_toOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome)
    (hpos : 0 < endpointWeight h hdegree inputs outcome) :
    (endpointConditional h hdegree inputs outcome hpos).toOperator =
      ((endpointWeight h hdegree inputs outcome : Complex)⁻¹) •
        rawEndpoint h hdegree inputs outcome :=
  rfl

/-- A normalized physical density used only to totalize the public run
interface at a zero-probability branch.  It is not asserted to be a physical
conditional history of that branch. -/
noncomputable def endpointFallback {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    DensityOperator (PhysicalRegister m w) :=
  DensityOperator.pureDensity (errorBranchState h hdegree 0)
    (errorBranchState_normSq h hdegree 0)

/-- The physical conditional at positive Born mass, with the explicitly
interface-only fallback at zero mass. -/
noncomputable def endpointCompletion {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) : DensityOperator (PhysicalRegister m w) :=
  if hpos : 0 < endpointWeight h hdegree inputs outcome then
    endpointConditional h hdegree inputs outcome hpos
  else endpointFallback h hdegree

theorem rawEndpoint_eq_zero_of_weight_eq_zero {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome)
    (hzero : endpointWeight h hdegree inputs outcome = 0) :
    rawEndpoint h hdegree inputs outcome = 0 := by
  simpa [rawEndpoint, endpointWeight] using
    rawPostselectionEndpoint_eq_zero_of_weight_eq_zero h outcome
      (resourcePreSyndromeState h hdegree inputs) hzero

/-- Weighting either normalized/completed endpoint reconstructs its literal
raw operator. -/
theorem endpointWeight_smul_completion_toOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (endpointWeight h hdegree inputs outcome : Complex) •
        (endpointCompletion h hdegree inputs outcome).toOperator =
      rawEndpoint h hdegree inputs outcome := by
  classical
  by_cases hpos : 0 < endpointWeight h hdegree inputs outcome
  · rw [endpointCompletion, dif_pos hpos]
    simpa [endpointWeight, endpointConditional, rawEndpoint] using
      postselectionWeight_smul_conditional_toOperator h
        (resourcePreSyndromeState h hdegree inputs) outcome hpos
  · rw [endpointCompletion, dif_neg hpos]
    have hzero : endpointWeight h hdegree inputs outcome = 0 :=
      le_antisymm (not_lt.mp hpos)
        (endpointWeight_nonneg h hdegree inputs outcome)
    rw [hzero, rawEndpoint_eq_zero_of_weight_eq_zero h hdegree inputs outcome hzero]
    simp

/-- The complete supplied-resource physical operation before total decoding. -/
noncomputable def resourceSyndromeOperation {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    QuantumChannel (PhysicalRegister m w) (PhysicalRegister m w) :=
  physicalOperation h hdegree

/-- The physical channel output decomposes into its accepted and rejected
completed endpoints without assuming either branch is globally positive. -/
theorem resourceSyndromeOperation_output_decomposition {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (resourceSyndromeOperation h hdegree).mapDensity
      (prepareMeasuredResources m w inputs) =
      outcomeMixture (endpointWeight h hdegree inputs .accepted)
        (endpointWeight_nonneg h hdegree inputs .accepted)
        (by
          have hsum := endpointWeights_sum h hdegree inputs
          linarith [endpointWeight_nonneg h hdegree inputs .rejected])
        (endpointCompletion h hdegree inputs .accepted)
        (endpointCompletion h hdegree inputs .rejected) := by
  apply DensityOperator.ext_toOperator
  rw [resourceSyndromeOperation, physicalOperation, QuantumChannel.comp_mapDensity]
  change (((postselectionInstrument h).kraus.toQuantumChannel
      (postselectionInstrument_complete h)).mapDensity
        (resourcePreSyndromeState h hdegree inputs)).toOperator = _
  rw [← (postselectionInstrument h).sum_branchOperator_eq_mapDensity_toOperator
    (postselectionInstrument_complete h)
    (resourcePreSyndromeState h hdegree inputs)]
  change (∑ outcome, rawEndpoint h hdegree inputs outcome) = _
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide]
  have hreject : 1 - endpointWeight h hdegree inputs .accepted =
      endpointWeight h hdegree inputs .rejected := by
    linarith [endpointWeights_sum h hdegree inputs]
  simp [outcomeMixture, DensityOperator.convexCombinationOperator,
    branchState, outcomeWeight,
    show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide, hreject]
  rw [← endpointWeight_smul_completion_toOperator h hdegree inputs .accepted,
    ← endpointWeight_smul_completion_toOperator h hdegree inputs .rejected]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  rfl

/-- The parameterized physical one-level HH18 run.  Its preparation field is
the actual measured-resource record map applied to the supplied resource
family, not an input-independent state. -/
noncomputable def resourceSyndromeRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    DistillationRun QubitSpace (PhysicalRegister m w) (PhysicalRegister m w) where
  resourceCount := physicalInputCount m w
  noisyInput := inputs
  prepareInput := prepareMeasuredResources m w
  operation := resourceSyndromeOperation h hdegree
  successProbability := endpointWeight h hdegree inputs .accepted
  success_nonneg := endpointWeight_nonneg h hdegree inputs .accepted
  success_le_one := by
    have hsum := endpointWeights_sum h hdegree inputs
    linarith [endpointWeight_nonneg h hdegree inputs .rejected]
  acceptedOutput := endpointCompletion h hdegree inputs .accepted
  rejectedOutput := endpointCompletion h hdegree inputs .rejected
  output_decomposition := resourceSyndromeOperation_output_decomposition h hdegree inputs

/-- The same actual parameterized run postprocessed through the total finite
Kraus decoder. -/
noncomputable def resourceDecodedRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    DistillationRun QubitSpace (PhysicalRegister m w) (LogicalRegister m w) :=
  (resourceSyndromeRun h hdegree inputs).postprocess (decoderChannel h)

theorem resourceDecodedRun_operation {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    (resourceDecodedRun h hdegree inputs).operation = decodedOperation h hdegree :=
  rfl

/-- For actual noisy resources, the accepted decoded output is the decoder
applied to the real positive conditional endpoint, never its fallback. -/
theorem resourceDecodedRun_acceptedOutput_noisyResources {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput =
      (decoderChannel h).mapDensity
        (endpointConditional h hdegree (noisyResources m w epsilon) .accepted
          (endpointWeight_accepted_pos h hdegree epsilon)) := by
  change (decoderChannel h).mapDensity
    (endpointCompletion h hdegree (noisyResources m w epsilon) .accepted) = _
  simp [endpointCompletion, endpointWeight_accepted_pos h hdegree epsilon]

end HH18Parameterized
end Distillation
end QEC

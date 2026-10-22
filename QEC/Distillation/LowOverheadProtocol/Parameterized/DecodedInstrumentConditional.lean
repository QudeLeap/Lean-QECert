import QEC.Distillation.LowOverheadProtocol.Parameterized.DecodedInstrument
import QEC.Distillation.LowOverheadProtocol.Parameterized.NormalizedRun
import QEC.Semantics.Instruments.TensorPower.BranchOperator
/-!
# Conditional operators of the parameterized HH18 decoded instrument

This layer identifies each actual decoded coarse branch with the decoder
applied to its physical postselection branch.  For the genuine noisy input,
the positive accepted conditional density is therefore exactly the already
constructed normalized accepted decoded output.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument

attribute [local instance 100] Fintype.ofFinite

/-- Coarsening away the two unit observations changes no decoded branch
operator. -/
theorem decodedInstrument_branchOperator_eq_decodedRawInstrument
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (decodedInstrument h hdegree).branchOperator outcome A =
      (decodedRawInstrument h hdegree).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A := by
  classical
  unfold FiniteInstrument.branchOperator
  apply Finset.sum_congr rfl
  intro index _
  simp [decodedInstrument, decodedRawInstrument,
    resourcePostselectionInstrument, FiniteInstrument.bindDependent]

/-- The decoded raw branch is the actual decoder channel applied to the
retained physical resource/postselection branch. -/
theorem decodedRawInstrument_branchOperator_eq_decoder
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (outcome : DistillationOutcome) (A : Operator (PhysicalRegister m w)) :
    (decodedRawInstrument h hdegree).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A =
      decoderChannel h
        ((resourcePostselectionInstrument h hdegree).branchOperator
          ⟨PUnit.unit, outcome⟩ A) := by
  change
    ((resourcePostselectionInstrument h hdegree).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument (decoderChannel h))).branchOperator
        ⟨⟨PUnit.unit, outcome⟩, PUnit.unit⟩ A = _
  rw [bindDependent_branchOperator_punit]
  exact QuantumChannel.toFiniteInstrument_inducedMap_apply (decoderChannel h) _

/-- On an actual measured resource family, a decoded coarse branch is its
literal Born weight times the normalized/completed decoded conditional
output. -/
theorem decodedInstrument_branchOperator_prepareMeasuredResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    (decodedInstrument h hdegree).branchOperator outcome
        (prepareMeasuredResources m w inputs).toOperator =
      (endpointWeight h hdegree inputs outcome : Complex) •
        ((resourceDecodedRun h hdegree inputs).conditionalOutput outcome).toOperator := by
  rw [decodedInstrument_branchOperator_eq_decodedRawInstrument,
    decodedRawInstrument_branchOperator_eq_decoder,
    resourcePostselectionInstrument_branchOperator]
  change decoderChannel h (rawEndpoint h hdegree inputs outcome) = _
  calc
    decoderChannel h (rawEndpoint h hdegree inputs outcome) =
        decoderChannel h
          ((endpointWeight h hdegree inputs outcome : Complex) •
            (endpointCompletion h hdegree inputs outcome).toOperator) := by
          rw [endpointWeight_smul_completion_toOperator]
    _ = (endpointWeight h hdegree inputs outcome : Complex) •
        decoderChannel h
          (endpointCompletion h hdegree inputs outcome).toOperator := by
          exact map_smul (decoderChannel h).toLinearMap _ _
    _ = _ := by
      cases outcome <;> rfl

/-- The genuine positive accepted conditional density of the decoded finite
instrument is exactly the physical normalized accepted decoded output. -/
theorem decodedInstrument_acceptedConditionalDensity_noisyResources
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (decodedInstrument h hdegree).conditionalDensity .accepted
        (prepareMeasuredResources m w (noisyResources m w epsilon))
        (by
          rw [decodedInstrument_bornWeight_prepareMeasuredResources]
          exact endpointWeight_accepted_pos h hdegree epsilon) =
      (resourceDecodedRun h hdegree
        (noisyResources m w epsilon)).acceptedOutput := by
  apply DensityOperator.ext_toOperator
  rw [FiniteInstrument.conditionalDensity_toOperator,
    decodedInstrument_branchOperator_prepareMeasuredResources,
    decodedInstrument_bornWeight_prepareMeasuredResources]
  change
    ((endpointWeight h hdegree (noisyResources m w epsilon) .accepted : Complex)⁻¹) •
        ((endpointWeight h hdegree (noisyResources m w epsilon) .accepted : Complex) •
          (resourceDecodedRun h hdegree
            (noisyResources m w epsilon)).acceptedOutput.toOperator) = _
  rw [← mul_smul]
  simp [ne_of_gt (endpointWeight_accepted_pos h hdegree epsilon)]

end HH18Parameterized
end Distillation
end QEC

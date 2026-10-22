import QEC.Distillation.LowOverheadProtocol.Parameterized.DecodedErrorSupport
import QEC.Distillation.LowOverheadProtocol.Parameterized.NormalizedRun

/-!
# Parameterized HH18 decoded-error bridge

This layer converts the parameterized accepted physical endpoint into a
trace-norm error bound for its decoded logical output.  Every finite expansion
is over the one named `physicalErrorWords m w` support; it introduces no
concrete carrier enumeration.
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

universe u v w

attribute [local instance 100] Fintype.ofFinite

local instance instDecodedBridgeClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The total decoder maps the error-free physical branch to the actual
parameterized logical-`T` target. -/
theorem decoderChannel_zeroErrorBranch_eq_ideal {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    decoderChannel h (errorBranchOperator h hdegree (0 : PhysicalErrorWord m w)) =
      (idealLogicalTOutput m w).toOperator := by
  change decoderChannel h (InnerProductSpace.rankOne Complex
    (HH18NoisyInput.zErrorOperator (0 : PhysicalErrorWord m w)
      (physicalTInvBranch h hdegree))
    (HH18NoisyInput.zErrorOperator (0 : PhysicalErrorWord m w)
      (physicalTInvBranch h hdegree))).toLinearMap = _
  have hbranch :
      HH18NoisyInput.zErrorOperator (0 : PhysicalErrorWord m w)
          (physicalTInvBranch h hdegree) = physicalTInvBranch h hdegree := by
    rw [HH18NoisyInput.zErrorOperator]
    change PauliSymplectic.toQubitOperator
        (PauliSymplectic.binaryOne (ι := PhysicalSite m w))
        (physicalTInvBranch h hdegree) = _
    rw [PauliSymplectic.toQubitOperator_one]
    simp
  rw [hbranch]
  exact decoderChannel_rankOne_physicalTInv_eq_idealLogicalTOutput h hdegree

/-- The normalized decoded density arising from one physical error word. -/
noncomputable def decodedErrorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) : DensityOperator (LogicalRegister m w) :=
  (decoderChannel h).mapDensity
    (DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error))

@[simp] theorem decodedErrorBranch_toOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (decodedErrorBranch h hdegree error).toOperator =
      decoderChannel h (errorBranchOperator h hdegree error) := by
  change decoderChannel h
      (DensityOperator.pureDensity (errorBranchState h hdegree error)
        (errorBranchState_normSq h hdegree error)).toOperator = _
  rw [errorBranchDensity_to_errorBranchOperator h hdegree error]

/-- Every decoded physical-error branch is within trace norm two of the
ideal logical density. -/
theorem decodedErrorBranch_traceError_le_two {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    outputTraceError (decodedErrorBranch h hdegree error) (idealLogicalTOutput m w) ≤ 2 := by
  unfold outputTraceError
  calc
    traceNorm ((decodedErrorBranch h hdegree error).toOperator -
        (idealLogicalTOutput m w).toOperator) ≤
        traceNorm (decodedErrorBranch h hdegree error).toOperator +
          traceNorm (-(idealLogicalTOutput m w).toOperator) := by
      simpa [sub_eq_add_neg] using
        traceNorm_add_le (decodedErrorBranch h hdegree error).toOperator
          (-(idealLogicalTOutput m w).toOperator)
    _ = 2 := by
      rw [DensityOperator.traceNorm_eq_one, traceNorm_neg,
        DensityOperator.traceNorm_eq_one]
      norm_num

private theorem rawAcceptedEndpoint_eq_physicalErrorWords {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint h hdegree (noisyResources m w epsilon) .accepted =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            errorBranchOperator h hdegree error
        else 0) :=
  rawAcceptedEndpoint_noisyResources_eq_errorWordSum h hdegree epsilon

private theorem acceptedBernoulliMass_eq_physicalErrorWords (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedBernoulliMass w r m epsilon =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then HH18NoisyInput.errorWordWeight epsilon error else 0) :=
  rfl

private theorem acceptedBernoulliMass_cast_eq_physicalErrorWords (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (acceptedBernoulliMass w r m epsilon : Complex) =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex)
        else 0) := by
  exact complex_of_real_sum_of_explicit_support
    (physicalErrorWords m w)
    (acceptedBernoulliMass w r m epsilon)
    (HH18NoisyInput.errorWordWeight epsilon)
    (Accepts w r m)
    (acceptedBernoulliMass_eq_physicalErrorWords w r m epsilon)

private theorem rawAcceptedResidualErrorMass_eq_physicalErrorWords (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawAcceptedResidualErrorMass w r m epsilon =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error ∧ error ≠ 0 then
          HH18NoisyInput.errorWordWeight epsilon error
        else 0) :=
  rfl

private theorem decodedRawAcceptedEndpoint_eq_physicalErrorWords {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            decoderChannel h (errorBranchOperator h hdegree error)
        else 0) := by
  exact linearMap_apply_selected_sum_of_explicit_support
    (physicalErrorWords m w)
    (decoderChannel h).toLinearMap
    (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted)
    (fun error => (HH18NoisyInput.errorWordWeight epsilon error : Complex))
    (Accepts w r m)
    (errorBranchOperator h hdegree)
    (fun error => decoderChannel h (errorBranchOperator h hdegree error))
    (rawAcceptedEndpoint_eq_physicalErrorWords h hdegree epsilon)
    (fun error => rfl)

/-- The decoded contribution of accepted nonzero physical words, centered at
the ideal logical density. -/
noncomputable def acceptedResidualDecodedDifference {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Operator (LogicalRegister m w) :=
  (physicalErrorWords m w).sum (fun error =>
    if Accepts w r m error ∧ error ≠ 0 then
      (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
        (decoderChannel h (errorBranchOperator h hdegree error) -
          (idealLogicalTOutput m w).toOperator)
    else 0)

private theorem acceptedResidualDecodedDifference_eq_physicalErrorWords {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualDecodedDifference h hdegree epsilon =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error ∧ error ≠ 0 then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            (decoderChannel h (errorBranchOperator h hdegree error) -
              (idealLogicalTOutput m w).toOperator)
        else 0) :=
  rfl

/-- The decoded residual has trace norm at most twice its actual unnormalized
accepted nonzero-word mass. -/
theorem traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    traceNorm (acceptedResidualDecodedDifference h hdegree epsilon) ≤
      2 * rawAcceptedResidualErrorMass w r m epsilon := by
  exact weighted_residual_traceNorm_of_explicit_support
    (physicalErrorWords m w)
    (HH18NoisyInput.errorWordWeight epsilon)
    (fun error => Accepts w r m error ∧ error ≠ 0)
    (fun error => decoderChannel h (errorBranchOperator h hdegree error))
    (idealLogicalTOutput m w).toOperator
    (acceptedResidualDecodedDifference h hdegree epsilon)
    (rawAcceptedResidualErrorMass w r m epsilon)
    (acceptedResidualDecodedDifference_eq_physicalErrorWords h hdegree epsilon)
    (rawAcceptedResidualErrorMass_eq_physicalErrorWords w r m epsilon)
    (HH18NoisyInput.errorWordWeight_nonneg epsilon)
    (fun error => by
      simpa [outputTraceError, decodedErrorBranch_toOperator] using
        decodedErrorBranch_traceError_le_two h hdegree error)

/-- The decoded accepted endpoint is the error-free logical density plus its
centered accepted nonzero-word residual. -/
theorem decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) -
        (acceptedBernoulliMass w r m epsilon : Complex) •
          (idealLogicalTOutput m w).toOperator =
      acceptedResidualDecodedDifference h hdegree epsilon := by
  exact centered_sum_of_explicit_support
    (physicalErrorWords m w)
    (fun error => (HH18NoisyInput.errorWordWeight epsilon error : Complex))
    (Accepts w r m)
    (fun error => decoderChannel h (errorBranchOperator h hdegree error))
    0
    (idealLogicalTOutput m w).toOperator
    (decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted))
    (acceptedResidualDecodedDifference h hdegree epsilon)
    (acceptedBernoulliMass w r m epsilon : Complex)
    (decodedRawAcceptedEndpoint_eq_physicalErrorWords h hdegree epsilon)
    (acceptedBernoulliMass_cast_eq_physicalErrorWords w r m epsilon)
    (acceptedResidualDecodedDifference_eq_physicalErrorWords h hdegree epsilon)
    (decoderChannel_zeroErrorBranch_eq_ideal h hdegree)

/-- The actual positive accepted decoded output has trace error controlled by
twice the actual normalized accepted residual. -/
theorem acceptedOutputTraceError_le_two_mul_acceptedResidual {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤ 2 * acceptedResidualError h hdegree epsilon := by
  have hsuccess : 0 < endpointWeight h hdegree (noisyResources m w epsilon) .accepted :=
    endpointWeight_accepted_pos h hdegree epsilon
  rw [resourceDecodedRun_acceptedOutput_noisyResources h hdegree epsilon]
  unfold outputTraceError
  rw [QuantumChannel.mapDensity_toOperator, endpointConditional_toOperator, map_smul]
  rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  have hrewrite :
      ((acceptedBernoulliMass w r m epsilon : Complex)⁻¹) •
          decoderChannel h (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted) -
        (idealLogicalTOutput m w).toOperator =
      (acceptedBernoulliMass w r m epsilon : Complex)⁻¹ •
        acceptedResidualDecodedDifference h hdegree epsilon := by
    rw [← decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual h hdegree epsilon]
    have hne : (acceptedBernoulliMass w r m epsilon : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (acceptedBernoulliMass_pos h epsilon))
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrewrite]
  have hmass :=
    traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass h hdegree epsilon
  have hsuccessReal : 0 < acceptedBernoulliMass w r m epsilon :=
    acceptedBernoulliMass_pos h epsilon
  have hnormalized := FiniteDecodedTrace.normalized_residual_traceNorm_le
    (acceptedBernoulliMass w r m epsilon) (rawAcceptedResidualErrorMass w r m epsilon)
    (acceptedResidualDecodedDifference h hdegree epsilon) hsuccessReal hmass
  have hratio :
      2 * (rawAcceptedResidualErrorMass w r m epsilon /
        acceptedBernoulliMass w r m epsilon) =
        2 * acceptedResidualError h hdegree epsilon := by
    unfold acceptedResidualError
    rw [endpointWeight_accepted_eq_acceptedBernoulliMass h hdegree epsilon]
  rwa [hratio] at hnormalized

/-- The decoded trace error has the explicit finite-coefficient distance-power
bound inherited from the accepted residual. -/
theorem acceptedOutputTraceError_le_two_mul_residualCoefficient {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤
        2 * residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by
  calc
    outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) ≤ 2 * acceptedResidualError h hdegree epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual h hdegree epsilon
    _ ≤ 2 * (residualCoefficient w r m * epsilon.1 ^ codeDistance r w) := by
      exact mul_le_mul_of_nonneg_left
        (acceptedResidualError_le_residualCoefficient h hdegree epsilon) (by norm_num)
    _ = 2 * residualCoefficient w r m * epsilon.1 ^ codeDistance r w := by ring

/-- The decoded trace error has the source-facing `(n * epsilon)^d` bound. -/
theorem acceptedOutputTraceError_le_two_mul_sourceScaled {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    outputTraceError
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
      (idealLogicalTOutput m w) ≤
        2 * residualCoefficient w r m *
          ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w := by
  calc
    outputTraceError
        (resourceDecodedRun h hdegree (noisyResources m w epsilon)).acceptedOutput
        (idealLogicalTOutput m w) ≤ 2 * acceptedResidualError h hdegree epsilon :=
      acceptedOutputTraceError_le_two_mul_acceptedResidual h hdegree epsilon
    _ ≤ 2 * (residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w) := by
      exact mul_le_mul_of_nonneg_left
        (acceptedResidualError_le_sourceScaled h hdegree epsilon) (by norm_num)
    _ = 2 * residualCoefficient w r m *
        ((physicalInputCount m w : ℝ) * epsilon.1) ^ codeDistance r w := by ring

end HH18Parameterized
end Distillation
end QEC

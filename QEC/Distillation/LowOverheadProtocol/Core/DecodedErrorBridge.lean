import QEC.Distillation.Core.FiniteDecodedTrace
import QEC.Distillation.LowOverheadProtocol.Core.PhysicalEndpoint
import QEC.Distillation.LowOverheadProtocol.Core.Decoder
import QEC.Distillation.LowOverheadProtocol.Core.NormalizedRun

/-!
# HH18 decoded-error bridge

This isolated module converts the actual finite HH18 accepted physical branch
into a trace-norm error bound for the decoded logical output.  It consumes the
physical protocol constructed in `HH18Protocol` and keeps finite-family
centering separate from the resource/channel elaboration route.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

universe u v w

attribute [local instance 100] Fintype.ofFinite

local instance instDecodedBridgeClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The total decoder applied to the error-free accepted physical branch is
the source-selected logical `T` density. -/
theorem decoderChannel_zeroErrorBranch_eq_ideal :
    decoderChannel
        (HH18SyndromeDecoding.errorBranchOperator (0 : PhysicalErrorWord)) =
      idealLogicalTOutput.toOperator := by
  change decoderChannel
      (InnerProductSpace.rankOne Complex
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord))
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord))).toLinearMap = _
  have hbranch :
      HH18NoisyInput.hh18PhysicalTInvErrorBranch (0 : PhysicalErrorWord) =
        ambientEncodingIsometry idealLogicalTOutputState := by
    rw [HH18NoisyInput.hh18PhysicalTInvErrorBranch,
      HH18NoisyInput.zErrorOperator]
    change PauliSymplectic.toQubitOperator (PauliSymplectic.binaryOne (ι := PhysicalSite))
        HH18NoisyInput.hh18PhysicalTInvBranch = _
    rw [PauliSymplectic.toQubitOperator_one]
    change HH18NoisyInput.hh18PhysicalTInvBranch =
      HH18NoisyInput.hh18_15_1_0_encodedCode.encode
        (HH18PuncturedReedMuller.logicalT 0 4 HH18NoisyInput.hh18LogicalPlusInput)
    exact HH18NoisyInput.hh18PhysicalTInvBranch_eq_logicalT
  rw [hbranch, decoderChannel_rankOne_encoded]
  rfl

/-- The normalized decoded density arising from one physical error word. -/
noncomputable def decodedErrorBranch (error : PhysicalErrorWord) :
    DensityOperator LogicalRegister :=
  decoderChannel.mapDensity
    (DensityOperator.pureDensity (errorBranchState error)
      (errorBranchState_normSq error))

@[simp] theorem decodedErrorBranch_toOperator (error : PhysicalErrorWord) :
    (decodedErrorBranch error).toOperator =
      decoderChannel (HH18SyndromeDecoding.errorBranchOperator error) := by
  change decoderChannel
      (DensityOperator.pureDensity (errorBranchState error)
        (errorBranchState_normSq error)).toOperator = _
  rw [errorBranchDensity_to_errorBranchOperator]

/-- Every decoded physical-error branch lies within trace norm two of the
ideal density. -/
theorem decodedErrorBranch_traceError_le_two (error : PhysicalErrorWord) :
    hh18OutputTraceError (decodedErrorBranch error) idealLogicalTOutput ≤ 2 := by
  unfold hh18OutputTraceError
  calc
    traceNorm ((decodedErrorBranch error).toOperator - idealLogicalTOutput.toOperator) ≤
        traceNorm (decodedErrorBranch error).toOperator +
          traceNorm (-idealLogicalTOutput.toOperator) := by
      simpa [sub_eq_add_neg] using
        traceNorm_add_le (decodedErrorBranch error).toOperator
          (-idealLogicalTOutput.toOperator)
    _ = 2 := by
      rw [DensityOperator.traceNorm_eq_one, traceNorm_neg,
        DensityOperator.traceNorm_eq_one]
      norm_num

private theorem complex_of_real_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] (support : Finset ι)
    (mass : ℝ) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected]
    (hmass : mass = support.sum (fun i =>
      if selected i then weight i else 0)) :
    (mass : Complex) = support.sum (fun i =>
      if selected i then (weight i : Complex) else 0) := by
  rw [hmass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hselected : selected i <;> simp [hselected]

private theorem weighted_residual_traceNorm_of_explicit_support
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (support : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (residual : Operator H) (residualMass : ℝ)
    (hresidual : residual = support.sum (fun i =>
      if selected i then (weight i : Complex) • (branch i - center) else 0))
    (hmass : residualMass = support.sum (fun i =>
      if selected i then weight i else 0))
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm residual ≤ 2 * residualMass := by
  rw [hresidual, hmass]
  calc
    traceNorm (support.sum (fun i =>
        if selected i then (weight i : Complex) • (branch i - center) else 0)) ≤
        support.sum (fun i => if selected i then 2 * weight i else 0) := by
      simpa [mul_comm] using
        FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
          support weight selected branch center hweight hbranch
    _ = 2 * support.sum (fun i => if selected i then weight i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hselected : selected i <;> simp [hselected]

private theorem centered_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (support : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι) (center raw residual : M)
    (mass : R)
    (hraw : raw = support.sum (fun i =>
      if accepts i then weight i • branch i else 0))
    (hmass : mass = support.sum (fun i =>
      if accepts i then weight i else 0))
    (hresidual : residual = support.sum (fun i =>
      if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0))
    (hzero : branch zeroIndex = center) :
    raw - mass • center = residual := by
  rw [hraw, hmass, hresidual]
  exact FiniteCentering.finset_centered_sum_eq_nonzero_residual
    support weight accepts branch zeroIndex center hzero

private theorem linearMap_apply_selected_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (support : Finset ι) (linearMap : Operator H →ₗ[Complex] Operator K)
    (input : Operator H) (weight : ι → Complex) (selected : ι → Prop)
    [DecidablePred selected] (inputBranch : ι → Operator H) (outputBranch : ι → Operator K)
    (hinput : input = support.sum (fun i =>
      if selected i then weight i • inputBranch i else 0))
    (hpointwise : ∀ i, linearMap (inputBranch i) = outputBranch i) :
    linearMap input = support.sum (fun i =>
      if selected i then weight i • outputBranch i else 0) := by
  rw [hinput, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hselected : selected i
  · simp only [if_pos hselected]
    rw [map_smul, hpointwise i]
  · simp only [if_neg hselected, map_zero]

private theorem rawAcceptedEndpoint_eq_physicalErrorWords
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint (noisyResources epsilon) .accepted =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            HH18SyndromeDecoding.errorBranchOperator error
        else 0) := by
  exact rawAcceptedEndpoint_noisyResources_eq_errorWordSum epsilon

private theorem rawSuccessMass_eq_physicalErrorWords
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawSuccessMass epsilon =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          HH18NoisyInput.errorWordWeight epsilon error
        else 0) := by
  rfl

private theorem rawSuccessMass_cast_eq_physicalErrorWords
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (rawSuccessMass epsilon : Complex) =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex)
        else 0) := by
  exact complex_of_real_sum_of_explicit_support
    physicalErrorWords
    (rawSuccessMass epsilon)
    (HH18NoisyInput.errorWordWeight epsilon)
    HH18SyndromeDecoding.Accepts
    (rawSuccessMass_eq_physicalErrorWords epsilon)

private theorem rawAcceptedResidualErrorMass_eq_physicalErrorWords
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawAcceptedResidualErrorMass epsilon =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error ∧ error ≠ 0 then
          HH18NoisyInput.errorWordWeight epsilon error
        else 0) := by
  rfl

private theorem decodedRawAcceptedEndpoint_eq_physicalErrorWords
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel (rawEndpoint (noisyResources epsilon) .accepted) =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            decoderChannel (HH18SyndromeDecoding.errorBranchOperator error)
        else 0) := by
  exact linearMap_apply_selected_sum_of_explicit_support
    physicalErrorWords
    decoderChannel.toLinearMap
    (rawEndpoint (noisyResources epsilon) .accepted)
    (fun error => (HH18NoisyInput.errorWordWeight epsilon error : Complex))
    HH18SyndromeDecoding.Accepts
    HH18SyndromeDecoding.errorBranchOperator
    (fun error => decoderChannel (HH18SyndromeDecoding.errorBranchOperator error))
    (rawAcceptedEndpoint_eq_physicalErrorWords epsilon)
    (fun error => rfl)

/-- The decoded contribution of accepted nonzero physical words, centered at
the ideal logical density. -/
noncomputable def acceptedResidualDecodedDifference
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : Operator LogicalRegister :=
  physicalErrorWords.sum (fun error =>
    if HH18SyndromeDecoding.Accepts error ∧ error ≠ 0 then
      (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
        (decoderChannel (HH18SyndromeDecoding.errorBranchOperator error) -
          idealLogicalTOutput.toOperator)
    else 0)

private theorem acceptedResidualDecodedDifference_eq_physicalErrorWords
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualDecodedDifference epsilon =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error ∧ error ≠ 0 then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            (decoderChannel (HH18SyndromeDecoding.errorBranchOperator error) -
              idealLogicalTOutput.toOperator)
        else 0) := by
  rfl

/-- Trace norm of the decoded residual is at most twice its actual conditional
physical-word mass before normalization. -/
theorem traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    traceNorm (acceptedResidualDecodedDifference epsilon) ≤
      2 * rawAcceptedResidualErrorMass epsilon := by
  exact weighted_residual_traceNorm_of_explicit_support
    physicalErrorWords
    (HH18NoisyInput.errorWordWeight epsilon)
    (fun error => HH18SyndromeDecoding.Accepts error ∧ error ≠ 0)
    (fun error => decoderChannel (HH18SyndromeDecoding.errorBranchOperator error))
    idealLogicalTOutput.toOperator
    (acceptedResidualDecodedDifference epsilon)
    (rawAcceptedResidualErrorMass epsilon)
    (acceptedResidualDecodedDifference_eq_physicalErrorWords epsilon)
    (rawAcceptedResidualErrorMass_eq_physicalErrorWords epsilon)
    (HH18NoisyInput.errorWordWeight_nonneg epsilon)
    (fun error => by
      simpa [hh18OutputTraceError, decodedErrorBranch_toOperator] using
        decodedErrorBranch_traceError_le_two error)

/-- The actual decoded accepted endpoint is the error-free logical density
plus precisely the centered accepted nonzero-word residual. -/
theorem decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    decoderChannel (rawEndpoint (noisyResources epsilon) .accepted) -
        (rawSuccessMass epsilon : Complex) • idealLogicalTOutput.toOperator =
      acceptedResidualDecodedDifference epsilon := by
  exact centered_sum_of_explicit_support
    physicalErrorWords
    (fun error => (HH18NoisyInput.errorWordWeight epsilon error : Complex))
    HH18SyndromeDecoding.Accepts
    (fun error => decoderChannel (HH18SyndromeDecoding.errorBranchOperator error))
    0
    idealLogicalTOutput.toOperator
    (decoderChannel (rawEndpoint (noisyResources epsilon) .accepted))
    (acceptedResidualDecodedDifference epsilon)
    (rawSuccessMass epsilon : Complex)
    (decodedRawAcceptedEndpoint_eq_physicalErrorWords epsilon)
    (rawSuccessMass_cast_eq_physicalErrorWords epsilon)
    (acceptedResidualDecodedDifference_eq_physicalErrorWords epsilon)
    decoderChannel_zeroErrorBranch_eq_ideal

/-- Honest bridge from the decoded accepted output's actual trace-norm error
to the physically proved accepted nonzero-word residual. -/
theorem acceptedOutputTraceError_le_two_mul_acceptedResidual
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    hh18OutputTraceError
      (resourceDecodedRun (noisyResources epsilon)).acceptedOutput
      idealLogicalTOutput ≤ 2 * acceptedResidualError epsilon := by
  have hsuccess : 0 < endpointWeight (noisyResources epsilon) .accepted :=
    endpointWeight_accepted_pos epsilon
  rw [resourceDecodedRun_acceptedOutput (noisyResources epsilon) hsuccess]
  unfold hh18OutputTraceError
  rw [QuantumChannel.mapDensity_toOperator, endpointConditional_toOperator, map_smul]
  rw [endpointWeight_accepted_eq_rawSuccessMass]
  have hrewrite :
      ((rawSuccessMass epsilon : Complex)⁻¹) •
          decoderChannel (rawEndpoint (noisyResources epsilon) .accepted) -
        idealLogicalTOutput.toOperator =
      (rawSuccessMass epsilon : Complex)⁻¹ •
        acceptedResidualDecodedDifference epsilon := by
    rw [← decodedRawAcceptedEndpoint_sub_success_ideal_eq_residual epsilon]
    have hne : (rawSuccessMass epsilon : Complex) ≠ 0 := by
      exact_mod_cast (ne_of_gt (rawSuccessMass_pos epsilon))
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrewrite]
  have hmass := traceNorm_acceptedResidualDecodedDifference_le_two_mul_rawMass epsilon
  have hsuccessReal : 0 < rawSuccessMass epsilon := rawSuccessMass_pos epsilon
  have hnormalized := FiniteDecodedTrace.normalized_residual_traceNorm_le
    (rawSuccessMass epsilon) (rawAcceptedResidualErrorMass epsilon)
    (acceptedResidualDecodedDifference epsilon) hsuccessReal hmass
  have hratio :
      2 * (rawAcceptedResidualErrorMass epsilon / rawSuccessMass epsilon) =
        2 * acceptedResidualError epsilon := by
      unfold acceptedResidualError
      field_simp [ne_of_gt hsuccessReal]
  rwa [hratio] at hnormalized

end HH18Protocol
end Distillation
end QEC

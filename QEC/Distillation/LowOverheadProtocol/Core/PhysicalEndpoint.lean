import QEC.Distillation.LowOverheadProtocol.Core.ResourceConsumer

/-!
# HH18 concrete physical endpoint analysis

This layer derives raw accepted endpoints, success, and residual mass only from
the actual measured-resource word consumer and the HH18 syndrome instrument.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Protocol

open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators

universe u

attribute [local instance 100] Fintype.ofFinite

local instance instEndpointClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The unconditioned one-level HH18 operation is a composition of the actual
resource consumer and the complete postselection Kraus family. -/
noncomputable def physicalOperation : QuantumChannel PhysicalRegister PhysicalRegister :=
  QuantumChannel.comp
    (HH18Postselection.postselectionInstrument.kraus.toQuantumChannel
      HH18Postselection.postselectionInstrument_complete)
    resourceConsumerChannel

/-- The literal unnormalized accepted or rejected raw endpoint of the physical
protocol on a supplied independent resource family. -/
noncomputable def rawEndpoint
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome) : Operator PhysicalRegister :=
  HH18Postselection.postselectionInstrument.branchOperator outcome
    (resourcePreSyndromeState inputs).toOperator

/-- The actual Born weight of a raw accepted or rejected endpoint. -/
noncomputable def endpointWeight
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome) : ℝ :=
  HH18Postselection.postselectionInstrument.bornWeight outcome
    (resourcePreSyndromeState inputs)

theorem endpointWeight_nonneg
    (inputs : ResourceInput resourceCount QubitSpace)
    (outcome : DistillationOutcome) : 0 ≤ endpointWeight inputs outcome :=
  HH18Postselection.postselectionInstrument.bornWeight_nonneg outcome _

theorem endpointWeights_sum
    (inputs : ResourceInput resourceCount QubitSpace) :
    endpointWeight inputs .accepted + endpointWeight inputs .rejected = 1 := by
  exact HH18Postselection.postselectionWeight_sum (resourcePreSyndromeState inputs)

theorem rawEndpoints_reconstruct
    (inputs : ResourceInput resourceCount QubitSpace) :
    rawEndpoint inputs .accepted + rawEndpoint inputs .rejected =
      (physicalOperation.mapDensity (prepareMeasuredResources inputs)).toOperator := by
  have h := HH18Postselection.postselectionInstrument.sum_branchOperator_eq_mapDensity_toOperator
    HH18Postselection.postselectionInstrument_complete
    (resourcePreSyndromeState inputs)
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at h
  rw [Finset.sum_pair (by decide)] at h
  unfold physicalOperation
  rw [QuantumChannel.comp_mapDensity]
  exact h

/-! ## Concrete noisy-error endpoint expansion -/

private theorem linearMap_apply_input_of_explicit_support
    {ι H K : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (linearMap : Operator H →ₗ[Complex] Operator K) (input : Operator H)
    (weight : ι → Complex) (inputSummand : ι → Operator H)
    (outputSummand : ι → Operator K)
    (hinput : input = support.sum (fun i => weight i • inputSummand i))
    (hpointwise : ∀ i, linearMap (inputSummand i) = outputSummand i) :
    linearMap input = support.sum (fun i => weight i • outputSummand i) := by
  rw [hinput]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, hpointwise i]

private theorem realTrace_input_of_explicit_support
    {ι H : Type u} (support : Finset ι)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (input : Operator H) (inputSummand : ι → Operator H) (realSummand : ι → ℝ)
    (hinput : input = support.sum inputSummand)
    (hpointwise : ∀ i, Complex.re (LinearMap.trace Complex H (inputSummand i)) =
      realSummand i) :
    Complex.re (LinearMap.trace Complex H input) = support.sum realSummand := by
  rw [hinput, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact hpointwise i

private noncomputable def postselectionBranchLinearMap
    (outcome : DistillationOutcome) :
    Operator PhysicalRegister →ₗ[Complex] Operator PhysicalRegister where
  toFun := HH18Postselection.postselectionInstrument.branchOperator outcome
  map_add' := by
    intro left right
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hobserve : HH18Postselection.postselectionInstrument.observe index = outcome
    · simp only [hobserve, if_true]
      ext psi
      simp [LinearMap.comp_apply, map_add]
    · simp [hobserve]
  map_smul' := by
    intro scalar operator
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hobserve : HH18Postselection.postselectionInstrument.observe index = outcome
    · simp only [hobserve, if_true]
      ext psi
      simp [LinearMap.comp_apply]
    · simp [hobserve]

private theorem postselectionBranchLinearMap_apply
    (outcome : DistillationOutcome) (operator : Operator PhysicalRegister) :
    postselectionBranchLinearMap outcome operator =
      HH18Postselection.postselectionInstrument.branchOperator outcome operator :=
  rfl

private theorem postselection_accepted_errorBranch
    (error : PhysicalErrorWord) :
    HH18Postselection.postselectionInstrument.branchOperator .accepted
      (DensityOperator.pureDensity (errorBranchState error)
        (errorBranchState_normSq error)).toOperator =
      if HH18SyndromeDecoding.Accepts error then
        HH18SyndromeDecoding.errorBranchOperator error
      else 0 := by
  rw [errorBranchDensity_to_errorBranchOperator]
  nth_rw 1 [← HH18SyndromeDecoding.injectedBranchOperator_eq_errorBranchOperator error 0]
  change HH18Postselection.rawPostselectionBranch .accepted
      (HH18SyndromeDecoding.injectedBranchOperator error 0) = _
  rw [HH18Postselection.rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint]
  by_cases haccept : HH18SyndromeDecoding.Accepts error
  · rw [HH18SyndromeDecoding.rawAcceptedEndpoint_of_accepts error 0 haccept,
      if_pos haccept]
  · rw [HH18SyndromeDecoding.rawAcceptedEndpoint_of_rejects error 0 haccept,
      if_neg haccept]

private theorem postselection_rejected_errorBranch
    (error : PhysicalErrorWord) :
    HH18Postselection.postselectionInstrument.branchOperator .rejected
      (DensityOperator.pureDensity (errorBranchState error)
        (errorBranchState_normSq error)).toOperator =
      if HH18SyndromeDecoding.Accepts error then 0
      else HH18SyndromeDecoding.errorBranchOperator error := by
  rw [errorBranchDensity_to_errorBranchOperator]
  nth_rw 1 [← HH18SyndromeDecoding.injectedBranchOperator_eq_errorBranchOperator error 0]
  change HH18Postselection.rawPostselectionBranch .rejected
      (HH18SyndromeDecoding.injectedBranchOperator error 0) = _
  rw [HH18Postselection.rawPostselectionBranch_rejected_eq_rawRejectedEndpoint]
  by_cases haccept : HH18SyndromeDecoding.Accepts error
  · rw [HH18SyndromeDecoding.rawRejectedEndpoint_of_accepts error 0 haccept,
      if_pos haccept]
  · rw [HH18SyndromeDecoding.rawRejectedEndpoint_of_rejects error 0 haccept,
      if_neg haccept]

/-- The actual noisy accepted endpoint is the finite sum of exactly the
accepted physical error branches under the derived independent word law. -/
theorem rawAcceptedEndpoint_noisyResources_eq_errorWordSum
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint (noisyResources epsilon) .accepted =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            HH18SyndromeDecoding.errorBranchOperator error
        else 0) := by
  change postselectionBranchLinearMap .accepted
      (resourceConsumerChannel
        (prepareMeasuredResources (noisyResources epsilon)).toOperator) = _
  simpa only [measuredErrorWordProbability_noisyResources, smul_ite, smul_zero] using
    linearMap_apply_input_of_explicit_support physicalErrorWords
      (postselectionBranchLinearMap .accepted)
      (resourceConsumerChannel
        (prepareMeasuredResources (noisyResources epsilon)).toOperator)
      (fun error =>
        (measuredErrorWordProbability (noisyResources epsilon) error : Complex))
      (fun error =>
        (DensityOperator.pureDensity (errorBranchState error)
          (errorBranchState_normSq error)).toOperator)
      (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          HH18SyndromeDecoding.errorBranchOperator error
        else 0)
      (resourceConsumerChannel_prepares_branchMixture (noisyResources epsilon))
      (fun error => by
        rw [postselectionBranchLinearMap_apply,
          postselection_accepted_errorBranch])

/-- The actual noisy rejected endpoint is the finite sum of exactly the
rejected physical error branches under the derived independent word law. -/
theorem rawRejectedEndpoint_noisyResources_eq_errorWordSum
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint (noisyResources epsilon) .rejected =
      physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then 0
        else (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          HH18SyndromeDecoding.errorBranchOperator error) := by
  change postselectionBranchLinearMap .rejected
      (resourceConsumerChannel
        (prepareMeasuredResources (noisyResources epsilon)).toOperator) = _
  simpa only [measuredErrorWordProbability_noisyResources, smul_ite, smul_zero] using
    linearMap_apply_input_of_explicit_support physicalErrorWords
      (postselectionBranchLinearMap .rejected)
      (resourceConsumerChannel
        (prepareMeasuredResources (noisyResources epsilon)).toOperator)
      (fun error =>
        (measuredErrorWordProbability (noisyResources epsilon) error : Complex))
      (fun error =>
        (DensityOperator.pureDensity (errorBranchState error)
          (errorBranchState_normSq error)).toOperator)
      (fun error =>
        if HH18SyndromeDecoding.Accepts error then 0
        else HH18SyndromeDecoding.errorBranchOperator error)
      (resourceConsumerChannel_prepares_branchMixture (noisyResources epsilon))
      (fun error => by
        rw [postselectionBranchLinearMap_apply,
          postselection_rejected_errorBranch])

/-- The raw Bernoulli mass of precisely the physical error words accepted by
the concrete HH18 stabilizer measurement. -/
noncomputable def rawSuccessMass (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  physicalErrorWords.sum (fun error =>
    if HH18SyndromeDecoding.Accepts error then
      HH18NoisyInput.errorWordWeight epsilon error
    else 0)

/-- The accepted Born weight is exactly the accepted sum under the derived
independent physical error law. -/
theorem endpointWeight_accepted_eq_rawSuccessMass
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    endpointWeight (noisyResources epsilon) .accepted = rawSuccessMass epsilon := by
  rw [endpointWeight, FiniteInstrument.bornWeight]
  change Complex.re (LinearMap.trace Complex PhysicalRegister
    (rawEndpoint (noisyResources epsilon) .accepted)) = rawSuccessMass epsilon
  exact realTrace_input_of_explicit_support physicalErrorWords
    (rawEndpoint (noisyResources epsilon) .accepted)
    (fun error =>
      if HH18SyndromeDecoding.Accepts error then
        (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          HH18SyndromeDecoding.errorBranchOperator error
      else 0)
    (fun error =>
      if HH18SyndromeDecoding.Accepts error then
        HH18NoisyInput.errorWordWeight epsilon error
      else 0)
    (rawAcceptedEndpoint_noisyResources_eq_errorWordSum epsilon)
    (fun error => by
      by_cases haccept : HH18SyndromeDecoding.Accepts error
      · simp only [haccept, if_true, map_smul]
        rw [← errorBranchDensity_to_errorBranchOperator]
        rw [(DensityOperator.pureDensity (errorBranchState error)
          (errorBranchState_normSq error)).trace_one]
        simp
      · simp [haccept])

/-- The all-zero physical error word has its literal product Bernoulli mass
over the fifteen input resources. -/
theorem allZeroErrorWordWeight
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    HH18NoisyInput.errorWordWeight epsilon (0 : PhysicalErrorWord) =
      (1 - epsilon.1) ^ resourceCount := by
  simp [HH18NoisyInput.errorWordWeight, HH18NoisyInput.bitErrorWeight,
    resourceCount]

/-- The actual accepted mass contains the nonnegative all-zero physical
summand; this is a local one-block statement and makes no simultaneous-batch
success assumption. -/
theorem rawSuccessMass_allZeroWord_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 - epsilon.1) ^ resourceCount ≤ rawSuccessMass epsilon := by
  classical
  rw [rawSuccessMass]
  calc
    (1 - epsilon.1) ^ resourceCount =
        if HH18SyndromeDecoding.Accepts (0 : PhysicalErrorWord) then
          HH18NoisyInput.errorWordWeight epsilon (0 : PhysicalErrorWord)
        else 0 := by
      rw [if_pos HH18SyndromeDecoding.accepts_zero]
      exact (allZeroErrorWordWeight epsilon).symm
    _ ≤ physicalErrorWords.sum (fun error =>
        if HH18SyndromeDecoding.Accepts error then
          HH18NoisyInput.errorWordWeight epsilon error
        else 0) := by
      exact Finset.single_le_sum
        (s := physicalErrorWords)
        (f := fun error : PhysicalErrorWord =>
          if HH18SyndromeDecoding.Accepts error then
            HH18NoisyInput.errorWordWeight epsilon error
          else 0)
        (fun error _ => by
          by_cases haccept : HH18SyndromeDecoding.Accepts error
          · simp [haccept, HH18NoisyInput.errorWordWeight_nonneg epsilon error]
          · simp [haccept])
        (mem_physicalErrorWords 0)

/-- The actual HH18 success probability is positive throughout the declared
diagonal-noise domain, so accepted normalization never relies on a surrogate
success assumption. -/
theorem rawSuccessMass_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < rawSuccessMass epsilon := by
  have hfactor : 0 < 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  exact lt_of_lt_of_le (pow_pos hfactor _) (rawSuccessMass_allZeroWord_le epsilon)

/-- The actual accepted endpoint has positive Born mass for every allowed
independent diagonal input distribution. -/
theorem endpointWeight_accepted_pos
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < endpointWeight (noisyResources epsilon) .accepted := by
  rw [endpointWeight_accepted_eq_rawSuccessMass]
  exact rawSuccessMass_pos epsilon

/-- Conditional before normalization, this is the literal mass of accepted
nonzero physical error words.  The HH18 distance proof below derives its
cubic suppression from the stabilizer checks. -/
noncomputable def rawAcceptedResidualErrorMass
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  physicalErrorWords.sum (fun error =>
    if HH18SyndromeDecoding.Accepts error ∧ error ≠ 0 then
      HH18NoisyInput.errorWordWeight epsilon error
    else 0)

theorem rawAcceptedResidualErrorMass_nonneg
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 ≤ rawAcceptedResidualErrorMass epsilon := by
  unfold rawAcceptedResidualErrorMass
  apply Finset.sum_nonneg
  intro error _
  by_cases hresidual : HH18SyndromeDecoding.Accepts error ∧ error ≠ 0
  · simp [hresidual, HH18NoisyInput.errorWordWeight_nonneg epsilon error]
  · simp [hresidual]

/-- The actual Bernoulli weight of any word with three or more diagonal
errors is at most its cubic error monomial on the declared noise interval. -/
theorem errorWordWeight_le_cube_of_hammingWeight_ge_three
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (error : PhysicalErrorWord)
    (hweight : 3 ≤ HammingWeight error) :
    HH18NoisyInput.errorWordWeight epsilon error ≤ epsilon.1 ^ 3 := by
  rw [HH18NoisyInput.errorWordWeight_eq_hammingWeight]
  have hepsilon_nonneg : 0 ≤ epsilon.1 := epsilon.property.1
  have hepsilon_le_one : epsilon.1 ≤ 1 := by
    linarith [epsilon.property.2]
  have hclean_nonneg : 0 ≤ 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  have hclean_le_one : 1 - epsilon.1 ≤ 1 := by
    linarith [epsilon.property.1]
  calc
    epsilon.1 ^ HammingWeight error *
        (1 - epsilon.1) ^ (Fintype.card PhysicalSite - HammingWeight error) ≤
      epsilon.1 ^ HammingWeight error * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ hclean_nonneg hclean_le_one) (pow_nonneg hepsilon_nonneg _)
    _ = epsilon.1 ^ HammingWeight error := by ring
    _ ≤ epsilon.1 ^ 3 := by
      exact pow_le_pow_of_le_one hepsilon_nonneg hepsilon_le_one hweight

/-- The real finite error-history type has exactly the binary words over the
fifteen physical resource sites. -/
theorem physicalErrorWord_card : Fintype.card PhysicalErrorWord = 2 ^ resourceCount := by
  simp [PhysicalErrorWord, HH18NoisyInput.PhysicalErrorWord, resourceCount]

/-- The residual accepted error mass is bounded using only the actual HH18
acceptance predicate.  Each surviving nonzero word has Hamming weight at
least three by the code's proved distance route. -/
theorem rawAcceptedResidualErrorMass_le_card_cube
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawAcceptedResidualErrorMass epsilon ≤
      (Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3 := by
  unfold rawAcceptedResidualErrorMass
  calc
    (physicalErrorWords.sum (fun error =>
      if HH18SyndromeDecoding.Accepts error ∧ error ≠ 0 then
        HH18NoisyInput.errorWordWeight epsilon error
      else 0)) ≤
        physicalErrorWords.sum (fun _error => epsilon.1 ^ 3) := by
      apply Finset.sum_le_sum
      intro error _
      by_cases hresidual : HH18SyndromeDecoding.Accepts error ∧ error ≠ 0
      · rw [if_pos hresidual]
        exact errorWordWeight_le_cube_of_hammingWeight_ge_three epsilon error
          (HH18SyndromeDecoding.accepted_nonzero_hammingWeight_ge_three error
            hresidual.2 hresidual.1)
      · simp [hresidual, pow_nonneg epsilon.property.1]
    _ = physicalErrorWords.card * epsilon.1 ^ 3 := by simp
    _ = (Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3 := by
      rw [physicalErrorWords_card]

/-- The success denominator is explicitly bounded below by the all-zero
physical branch throughout the stated interval. -/
theorem rawSuccessMass_half_power_le
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    (1 / 2 : ℝ) ^ resourceCount ≤ rawSuccessMass epsilon := by
  calc
    (1 / 2 : ℝ) ^ resourceCount ≤ (1 - epsilon.1) ^ resourceCount := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [epsilon.property.2]
    _ ≤ rawSuccessMass epsilon := rawSuccessMass_allZeroWord_le epsilon

/-- The actual normalized residual error of the accepted HH18 physical
branch.  This is a conditional probability derived from the resource-word
distribution and never a caller-provided error field. -/
noncomputable def acceptedResidualError
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  rawAcceptedResidualErrorMass epsilon / rawSuccessMass epsilon

/-- A finite coefficient derived from the real word type and actual success
lower bound.  With `resourceCount = 15`, it is independent of epsilon. -/
noncomputable def residualCubicCoefficient : ℝ :=
  (Fintype.card PhysicalErrorWord : ℝ) / (1 / 2 : ℝ) ^ resourceCount

/-- The HH18 distance-three route gives a genuine cubic accepted-error bound
from the physical Bernoulli histories: for fixed `n = 15`, this is
`O((n * epsilon)^3)`. -/
theorem acceptedResidualError_le_cubic
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    acceptedResidualError epsilon ≤ residualCubicCoefficient * epsilon.1 ^ 3 := by
  unfold acceptedResidualError residualCubicCoefficient
  have hsuccess : 0 < rawSuccessMass epsilon := rawSuccessMass_pos epsilon
  have hmass : 0 ≤ rawAcceptedResidualErrorMass epsilon :=
    rawAcceptedResidualErrorMass_nonneg epsilon
  have hcube : 0 ≤ (Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3 := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg epsilon.property.1 _)
  calc
    rawAcceptedResidualErrorMass epsilon / rawSuccessMass epsilon ≤
        ((Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3) /
          rawSuccessMass epsilon := by
      exact div_le_div_of_nonneg_right
        (rawAcceptedResidualErrorMass_le_card_cube epsilon) hsuccess.le
    _ ≤ ((Fintype.card PhysicalErrorWord : ℝ) * epsilon.1 ^ 3) /
          ((1 / 2 : ℝ) ^ resourceCount) := by
      exact div_le_div_of_nonneg_left hcube
        (by positivity) (rawSuccessMass_half_power_le epsilon)
    _ = residualCubicCoefficient * epsilon.1 ^ 3 := by
      unfold residualCubicCoefficient
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

end HH18Protocol
end Distillation
end QEC

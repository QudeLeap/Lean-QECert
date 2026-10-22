import QEC.Distillation.LowOverheadProtocol.Parameterized.Postselection
import QEC.Distillation.LowOverheadProtocol.Parameterized.ResourceConsumer
import QEC.Distillation.LowOverheadProtocol.Parameterized.EndpointSupport

/-!
# Parameterized HH18 physical endpoint

This layer composes the actual finite resource-word consumer with the coarse
HH18 postselection channel.  It exposes literal raw accepted and rejected
endpoints, their Born weights, and their exact symbolic Bernoulli expansions
over the one named physical-error-word support.  It stops before positivity,
residual bounds, decoding, or a protocol run.
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

universe u

attribute [local instance 100] Fintype.ofFinite

local instance instEndpointClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The physical state entering parameterized HH18 syndrome postselection,
obtained by consuming the actual measured resource record. -/
noncomputable def resourcePreSyndromeState {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    DensityOperator (PhysicalRegister m w) :=
  (resourceConsumerChannel h hdegree).mapDensity
    (prepareMeasuredResources m w inputs)

/-- The pure physical resource-consumer branch is exactly the syndrome-layer
operator for the same physical error word. -/
theorem errorBranchDensity_to_errorBranchOperator {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (DensityOperator.pureDensity (errorBranchState h hdegree error)
      (errorBranchState_normSq h hdegree error)).toOperator =
      errorBranchOperator h hdegree error := by
  rw [DensityOperator.pureDensity_toOperator]
  rfl

/-- The unconditioned one-level parameterized HH18 operation is the complete
coarse postselection channel after actual resource-word consumption. -/
noncomputable def physicalOperation {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m) :
    QuantumChannel (PhysicalRegister m w) (PhysicalRegister m w) :=
  QuantumChannel.comp
    ((postselectionInstrument h).kraus.toQuantumChannel
      (postselectionInstrument_complete h))
    (resourceConsumerChannel h hdegree)

/-- The literal unnormalized accepted or rejected raw endpoint on a supplied
parameterized resource family. -/
noncomputable def rawEndpoint {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) : Operator (PhysicalRegister m w) :=
  rawPostselectionEndpoint h outcome (resourcePreSyndromeState h hdegree inputs)

/-- The actual Born weight of one raw endpoint. -/
noncomputable def endpointWeight {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) : ℝ :=
  postselectionWeight h outcome (resourcePreSyndromeState h hdegree inputs)

theorem endpointWeight_nonneg {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (outcome : DistillationOutcome) :
    0 ≤ endpointWeight h hdegree inputs outcome :=
  postselectionWeight_nonneg h outcome (resourcePreSyndromeState h hdegree inputs)

theorem endpointWeights_sum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    endpointWeight h hdegree inputs .accepted +
      endpointWeight h hdegree inputs .rejected = 1 := by
  simpa [endpointWeight] using
    postselectionWeight_sum h (resourcePreSyndromeState h hdegree inputs)

/-- The two literal raw endpoints reconstruct the complete composed physical
operation on the actual measured resource record. -/
theorem rawEndpoints_reconstruct {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace) :
    rawEndpoint h hdegree inputs .accepted + rawEndpoint h hdegree inputs .rejected =
      ((physicalOperation h hdegree).mapDensity
        (prepareMeasuredResources m w inputs)).toOperator := by
  have hsum := (postselectionInstrument h).sum_branchOperator_eq_mapDensity_toOperator
    (postselectionInstrument_complete h)
    (resourcePreSyndromeState h hdegree inputs)
  rw [show (Finset.univ : Finset DistillationOutcome) =
      {.accepted, .rejected} by decide] at hsum
  simpa [rawEndpoint, rawPostselectionEndpoint, rawPostselectionBranch,
    resourcePreSyndromeState, physicalOperation, QuantumChannel.comp_mapDensity] using hsum

private noncomputable def postselectionBranchLinearMap {w r m : Nat}
    (h : Admissible w r m) (outcome : DistillationOutcome) :
    Operator (PhysicalRegister m w) →ₗ[Complex] Operator (PhysicalRegister m w) where
  toFun := fun operator => (postselectionInstrument h).branchOperator outcome operator
  map_add' := by
    intro left right
    classical
    simp only [FiniteInstrument.branchOperator_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hobserve : (postselectionInstrument h).observe index = outcome
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
    by_cases hobserve : (postselectionInstrument h).observe index = outcome
    · simp only [hobserve, if_true]
      ext psi
      simp [LinearMap.comp_apply]
    · simp [hobserve]

private theorem postselectionBranchLinearMap_apply {w r m : Nat}
    (h : Admissible w r m) (outcome : DistillationOutcome)
    (operator : Operator (PhysicalRegister m w)) :
    postselectionBranchLinearMap h outcome operator =
      (postselectionInstrument h).branchOperator outcome operator :=
  rfl

private theorem postselection_accepted_errorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (postselectionInstrument h).branchOperator .accepted
      (DensityOperator.pureDensity (errorBranchState h hdegree error)
        (errorBranchState_normSq h hdegree error)).toOperator =
      if Accepts w r m error then errorBranchOperator h hdegree error else 0 := by
  rw [errorBranchDensity_to_errorBranchOperator h hdegree error]
  nth_rw 1 [← injectedBranchOperator_eq_errorBranchOperator h hdegree error 0]
  change rawPostselectionBranch h .accepted
      (injectedBranchOperator h error 0) = _
  rw [rawPostselectionBranch_accepted_eq_rawAcceptedEndpoint h error 0]
  by_cases haccept : Accepts w r m error
  · rw [rawAcceptedEndpoint_of_accepts h hdegree error 0 haccept, if_pos haccept]
  · rw [rawAcceptedEndpoint_of_rejects h hdegree error 0 haccept, if_neg haccept]

private theorem postselection_rejected_errorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    (postselectionInstrument h).branchOperator .rejected
      (DensityOperator.pureDensity (errorBranchState h hdegree error)
        (errorBranchState_normSq h hdegree error)).toOperator =
      if Accepts w r m error then 0 else errorBranchOperator h hdegree error := by
  rw [errorBranchDensity_to_errorBranchOperator h hdegree error]
  nth_rw 1 [← injectedBranchOperator_eq_errorBranchOperator h hdegree error 0]
  change rawPostselectionBranch h .rejected
      (injectedBranchOperator h error 0) = _
  rw [rawPostselectionBranch_rejected_eq_rawRejectedEndpoint h error 0]
  by_cases haccept : Accepts w r m error
  · rw [rawRejectedEndpoint_of_accepts h hdegree error 0 haccept, if_pos haccept]
  · rw [rawRejectedEndpoint_of_rejects h hdegree error 0 haccept, if_neg haccept]

/-- The actual noisy accepted endpoint is the finite sum of exactly the
accepted physical error branches under the derived independent word law. -/
theorem rawAcceptedEndpoint_noisyResources_eq_errorWordSum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint h hdegree (noisyResources m w epsilon) .accepted =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then
          (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
            errorBranchOperator h hdegree error
        else 0) := by
  change postselectionBranchLinearMap h .accepted
      (resourceConsumerChannel h hdegree
        (prepareMeasuredResources m w (noisyResources m w epsilon)).toOperator) = _
  simpa only [measuredErrorWordProbability_noisyResources, smul_ite, smul_zero] using
    linearMap_apply_input_of_explicit_support
      (physicalErrorWords m w)
      (postselectionBranchLinearMap h .accepted)
      (resourceConsumerChannel h hdegree
        (prepareMeasuredResources m w (noisyResources m w epsilon)).toOperator)
      (fun error => (measuredErrorWordProbability m w
        (noisyResources m w epsilon) error : Complex))
      (fun error => (DensityOperator.pureDensity (errorBranchState h hdegree error)
        (errorBranchState_normSq h hdegree error)).toOperator)
      (fun error => if Accepts w r m error then errorBranchOperator h hdegree error else 0)
      (resourceConsumerChannel_prepareMeasuredResources h hdegree
        (noisyResources m w epsilon))
      (fun error => by
        rw [postselectionBranchLinearMap_apply,
          postselection_accepted_errorBranch])

/-- The actual noisy rejected endpoint is the finite sum of exactly the
rejected physical error branches under the derived independent word law. -/
theorem rawRejectedEndpoint_noisyResources_eq_errorWordSum {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    rawEndpoint h hdegree (noisyResources m w epsilon) .rejected =
      (physicalErrorWords m w).sum (fun error =>
        if Accepts w r m error then 0
        else (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          errorBranchOperator h hdegree error) := by
  change postselectionBranchLinearMap h .rejected
      (resourceConsumerChannel h hdegree
        (prepareMeasuredResources m w (noisyResources m w epsilon)).toOperator) = _
  simpa only [measuredErrorWordProbability_noisyResources, smul_ite, smul_zero] using
    linearMap_apply_input_of_explicit_support
      (physicalErrorWords m w)
      (postselectionBranchLinearMap h .rejected)
      (resourceConsumerChannel h hdegree
        (prepareMeasuredResources m w (noisyResources m w epsilon)).toOperator)
      (fun error => (measuredErrorWordProbability m w
        (noisyResources m w epsilon) error : Complex))
      (fun error => (DensityOperator.pureDensity (errorBranchState h hdegree error)
        (errorBranchState_normSq h hdegree error)).toOperator)
      (fun error => if Accepts w r m error then 0 else errorBranchOperator h hdegree error)
      (resourceConsumerChannel_prepareMeasuredResources h hdegree
        (noisyResources m w epsilon))
      (fun error => by
        rw [postselectionBranchLinearMap_apply,
          postselection_rejected_errorBranch])

/-- The Bernoulli mass of exactly the physical error words accepted by the
actual parameterized HH18 syndrome measurement. -/
noncomputable def acceptedBernoulliMass (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) : ℝ :=
  (physicalErrorWords m w).sum (fun error =>
    if Accepts w r m error then HH18NoisyInput.errorWordWeight epsilon error else 0)

/-- The actual accepted Born weight is exactly the accepted symbolic Bernoulli
mass, with no lower-bound or residual estimate asserted here. -/
theorem endpointWeight_accepted_eq_acceptedBernoulliMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    endpointWeight h hdegree (noisyResources m w epsilon) .accepted =
      acceptedBernoulliMass w r m epsilon := by
  rw [endpointWeight, postselectionWeight, FiniteInstrument.bornWeight]
  change Complex.re (LinearMap.trace Complex (PhysicalRegister m w)
    (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted)) =
      acceptedBernoulliMass w r m epsilon
  exact realTrace_input_of_explicit_support
    (physicalErrorWords m w)
    (rawEndpoint h hdegree (noisyResources m w epsilon) .accepted)
    (fun error =>
      if Accepts w r m error then
        (HH18NoisyInput.errorWordWeight epsilon error : Complex) •
          errorBranchOperator h hdegree error
      else 0)
    (fun error =>
      if Accepts w r m error then HH18NoisyInput.errorWordWeight epsilon error else 0)
    (rawAcceptedEndpoint_noisyResources_eq_errorWordSum h hdegree epsilon)
    (fun error => by
      by_cases haccept : Accepts w r m error
      · simp only [haccept, if_true, map_smul]
        rw [← errorBranchDensity_to_errorBranchOperator h hdegree error]
        rw [(DensityOperator.pureDensity (errorBranchState h hdegree error)
          (errorBranchState_normSq h hdegree error)).trace_one]
        simp
      · simp [haccept])

end HH18Parameterized
end Distillation
end QEC

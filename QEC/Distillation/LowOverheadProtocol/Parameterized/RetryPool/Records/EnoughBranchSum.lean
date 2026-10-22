import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Records.AcceptedProduct
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.SuccessEvent

/-!
# Enough-event branch sum for the parameterized HH18 retry pool

Every actual enough observed pool history has already been shown to produce
its genuine Born-product weight times one fixed accepted-product density.  This
layer sums that finite event and identifies its scalar with the existing
measured `decodedRetryPoolEnoughMass`.  The identity is unnormalized and uses
no externally supplied success probability.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instEnoughBranchSumClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Summing every genuinely enough retry-pool branch on the noisy product
input gives the measured enough mass times the fixed accepted-product
operator.  No branch is normalized in this identity. -/
theorem decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (attempts required : Nat) :
    (∑ outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts => PUnit,
      if decodedRetryPoolOutcomeEnough attempts required outcome = true then
        (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
          outcome
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
            attempts).toOperator
      else 0) =
      (decodedRetryPoolEnoughMass h hdegree attempts required
        (tensorPowerProductInput
          (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit
          attempts) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          required).toOperator := by
  classical
  let input := tensorPowerProductInput
    (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit attempts
  let accepted := decodedRetryPoolAcceptedProductDensity
    h hdegree epsilon rhoUnit required
  have hbranches :
      (∑ outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts => PUnit,
        if decodedRetryPoolOutcomeEnough attempts required outcome = true then
          (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
            outcome input.toOperator
        else 0) =
        ∑ history : tensorPowerHistory DistillationOutcome attempts,
          if required ≤
              (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card then
            (tensorPowerBornProduct (decodedInstrument h hdegree)
              (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
              history : Complex) • accepted.toOperator
          else 0 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro history _
    simp only [Fintype.sum_unique]
    by_cases henough : required ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card
    · rw [if_pos henough]
      have houtcome :
          decodedRetryPoolOutcomeEnough attempts required
            ⟨history, PUnit.unit⟩ = true := by
        simp [decodedRetryPoolOutcomeEnough, henough]
      rw [if_pos houtcome]
      simpa [input, accepted] using
        decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
          h hdegree epsilon rhoUnit attempts required history henough
    · rw [if_neg henough]
      have houtcome : ¬
          decodedRetryPoolOutcomeEnough attempts required
            ⟨history, PUnit.unit⟩ = true := by
        simp [decodedRetryPoolOutcomeEnough, henough]
      rw [if_neg houtcome]
  have hmass :
      (decodedRetryPoolEnoughMass h hdegree attempts required input : Complex) =
        ∑ history : tensorPowerHistory DistillationOutcome attempts,
          if required ≤
              (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card then
            (tensorPowerBornProduct (decodedInstrument h hdegree)
              (prepareMeasuredResources m w (noisyResources m w epsilon)) attempts
              history : Complex)
          else 0 := by
    unfold decodedRetryPoolEnoughMass
    rw [Finset.sum_filter, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro history _
    by_cases henough : required ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card
    · rw [if_pos henough, if_pos henough]
      exact congrArg Complex.ofReal
        (decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput
          h hdegree attempts required
          (noisyResources m w epsilon) rhoUnit history)
    · simp [henough]
  rw [hbranches, hmass, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro history _
  by_cases henough : required ≤
      (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card
  · simp [henough, accepted]
  · simp [henough]

end HH18Parameterized
end Distillation
end QEC

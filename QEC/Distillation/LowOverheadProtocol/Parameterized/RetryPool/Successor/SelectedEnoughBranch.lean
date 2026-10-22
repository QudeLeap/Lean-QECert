import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Records.EnoughBranchSum
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.BranchProduct
import QEC.Semantics.Instruments.Branches.ChannelFirstFilteredBranchOperator
import QEC.Semantics.Instruments.TensorPower.FilteredMarginalBranchOperator
/-!
# One selected enough branch of a physical HH18 successor stage

For a genuine accepted parent product, this layer selects one logical port of
the actual joint routed successor input, sums every sibling pool outcome, and
retains only histories for which that selected retry pool is genuinely enough.
The resulting unnormalized operator is the measured enough mass at the true
routed next rate times the next accepted-product operator.  No independence
between logical ports and no normalized conditional branch is used.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

/-- The selected actual successor-pool observation contains enough accepted
decoded trials. -/
def decodedRetryPoolSuccessorStageSelectedPoolEnough
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (outcome : decodedRetryPoolSuccessorStageOutcome m w z q stage hstage) : Bool :=
  decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
      (tensorPowerHistoryAt _ (logicalOutputCount m w) outcome.2
        (decodedRetryPoolLogicalSiteFinEquiv m w port))

/-- The actual correlated joint input supplied to every successor retry pool
after routing one genuine accepted parent product. -/
noncomputable def decodedRetryPoolSuccessorStageJointInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (decodedRetryPoolSuccessorNestedInputCarrier
      m w z q stage hstage) :=
  (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).mapDensity
    (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
      (decodedRetryPoolBackwardSchedule m w z q stage))

/-- The literal noisy product input at one selected successor port. -/
noncomputable def decodedRetryPoolSuccessorStageSelectedNextInput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DensityOperator (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)) :=
  tensorPowerProductInput
    (prepareMeasuredResources m w
      (noisyResources m w
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)))
    rhoUnit
    (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)

/-- The true selected marginal of the correlated routed successor input is
the literal noisy product at that port's next physical rate. -/
theorem decodedRetryPoolSuccessorStage_selectedJointInput_coordinate
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolSuccessorStageJointInput
          h hdegree epsilon z q stage hstage rhoUnit).toOperator =
      (decodedRetryPoolSuccessorStageSelectedNextInput
        h hdegree epsilon z q stage hstage port hhalf rhoUnit).toOperator := by
  change
    ((tensorPowerCoordinateOperator (logicalOutputCount m w)
      (decodedRetryPoolLogicalSiteFinEquiv m w port)).mapDensity
        (decodedRetryPoolSuccessorStageJointInput
          h hdegree epsilon z q stage hstage rhoUnit)).toOperator = _
  rw [tensorPowerCoordinateOperator_mapDensity]
  exact congrArg DensityOperator.toOperator
    (by
      simpa [decodedRetryPoolSuccessorStageJointInput,
        decodedRetryPoolSuccessorStageSelectedNextInput] using
        decodedRetryPoolSuccessorNestedInputChannel_inputMarginal_acceptedProduct
          h hdegree epsilon z q stage hstage port hhalf rhoUnit)

/-- The global unnormalized successor-stage operator obtained by retaining
only the selected pool's enough event before taking any output marginal. -/
noncomputable def decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Operator (tensorPowerCarrier
      (QubitRegister (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  ∑ outcome : decodedRetryPoolSuccessorStageOutcome m w z q stage hstage,
    if decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q stage hstage port outcome = true then
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q stage hstage).branchOperator outcome
          (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q stage)).toOperator
    else 0

/-- The same global operator after regrouping the unit-observed route into the
actual tensor-power retry-pool history sum. -/
noncomputable def decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Operator (tensorPowerCarrier
      (QubitRegister (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  ∑ history : tensorPowerHistory
      (Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩) => PUnit)
      (logicalOutputCount m w),
    if decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        (tensorPowerHistoryAt _ (logicalOutputCount m w) history
          (decodedRetryPoolLogicalSiteFinEquiv m w port)) = true then
      ((decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩)).tensorPower
            (logicalOutputCount m w)).branchOperator history
              (decodedRetryPoolSuccessorStageJointInput
                h hdegree epsilon z q stage hstage rhoUnit).toOperator
    else 0

/-- The channel-first physical successor sum is exactly its routed
tensor-history form. -/
theorem decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
        h hdegree epsilon z q stage hstage port rhoUnit := by
  unfold decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
    decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
    decodedRetryPoolSuccessorStageSelectedPoolEnough
    decodedRetryPoolSuccessorStageJointInput
    decodedRetryPoolSuccessorStageInstrument
  exact toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq
    (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage)
    ((decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).tensorPower (logicalOutputCount m w))
    (fun history => decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
      (tensorPowerHistoryAt _ (logicalOutputCount m w) history
        (decodedRetryPoolLogicalSiteFinEquiv m w port)) = true)
    (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
      (decodedRetryPoolBackwardSchedule m w z q stage)).toOperator

/-- The unnormalized selected output branch obtained from the global
selected-enough event operator. -/
noncomputable def decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w)) :=
  tensorPowerCoordinateOperator (logicalOutputCount m w)
    (decodedRetryPoolLogicalSiteFinEquiv m w port)
    (decodedRetryPoolSuccessorStageSelectedEnoughGlobalOperator
      h hdegree epsilon z q stage hstage port rhoUnit)

/-- The selected output branch may use the compiled routed-history form of the
same global unnormalized operator. -/
theorem decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
          h hdegree epsilon z q stage hstage port rhoUnit) := by
  unfold decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
  rw [decodedRetryPoolSuccessorStage_selectedEnoughGlobalOperator_eq_routed]

/-- The local enough-event branch sum of the successor retry pool on an
arbitrary unnormalized input operator. -/
noncomputable def decodedRetryPoolSuccessorStageLocalEnoughOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (tensorPowerCarrier (PhysicalRegister m w)
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩) × LogicalSite m w)) :=
  ∑ outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩) => PUnit,
    if decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        outcome = true then
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩)).branchOperator outcome A
    else 0

/-- Retaining the selected output coordinate after the routed global sum
leaves the local enough-event branch sum on the true input marginal. -/
theorem decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq_local
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      decodedRetryPoolSuccessorStageLocalEnoughOperator h hdegree z q stage hstage
        (tensorPowerCoordinateOperator (logicalOutputCount m w)
          (decodedRetryPoolLogicalSiteFinEquiv m w port)
          (decodedRetryPoolSuccessorStageJointInput
            h hdegree epsilon z q stage hstage rhoUnit).toOperator) := by
  rw [decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq]
  unfold decodedRetryPoolSuccessorStageSelectedEnoughRoutedOperator
    decodedRetryPoolSuccessorStageLocalEnoughOperator
  exact tensorPower_coordinateOperator_branchOperator_filter_sum_eq
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (decodedRetryPoolInstrument_complete h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (fun outcome => decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
      outcome = true)
    (logicalOutputCount m w)
    (decodedRetryPoolSuccessorStageJointInput
      h hdegree epsilon z q stage hstage rhoUnit).toOperator
    (decodedRetryPoolLogicalSiteFinEquiv m w port)

/-- Retaining one actual enough successor pool while summing all sibling
observations yields its measured enough mass times the genuine next accepted
product.  The joint routed successor input may be arbitrarily correlated. -/
theorem decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolSuccessorStageSelectedEnoughBranchOperator
        h hdegree epsilon z q stage hstage port rhoUnit =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree epsilon z q stage hstage port hhalf rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).toOperator := by
  rw [decodedRetryPoolSuccessorStage_selectedEnoughBranchOperator_eq_local]
  rw [decodedRetryPoolSuccessorStage_selectedJointInput_coordinate
    h hdegree epsilon z q stage hstage port hhalf rhoUnit]
  unfold decodedRetryPoolSuccessorStageLocalEnoughOperator
  simpa [decodedRetryPoolSuccessorStageSelectedNextInput] using
    decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
      h hdegree
      (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)
      rhoUnit
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)

end HH18Parameterized
end Distillation
end QEC

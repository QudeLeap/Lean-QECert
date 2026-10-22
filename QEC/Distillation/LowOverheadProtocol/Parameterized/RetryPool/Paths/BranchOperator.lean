import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Paths.SuccessEvent
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.SuccessMassRecurrence
import QEC.Semantics.Instruments.Sequential.NestedFilteredMarginalBranchOperator
/-!
# Unnormalized successful branch on one routed physical path

The operator below sums the actual physical protocol histories whose literal
ancestor path succeeds and then traces every off-path output.  Its recursive
evaluation is a product of measured retry-pool enough masses multiplying the
genuine accepted-product density at the reached routed rate.  No retained
branch is normalized and no sibling-product hypothesis is used.
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

/-- The physical unnormalized successful-event operator retained at one
literal routed output path. -/
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage < z)
    (path : routedDepthOutputSlots m w stage)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
        LogicalSite m w)) :=
  nestedTensorCoordinateOperator
    (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
        LogicalSite m w))
    (logicalOutputCount m w) stage
    ((decodedRetryPoolNestedPathEquiv m w stage).symm path)
    (∑ outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage hstage,
      if decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage hstage path outcome = true then
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage hstage).branchOperator outcome rho.toOperator
      else 0)

/-- The measured scalar accumulated along one routed path. -/
noncomputable def decodedRetryPoolProtocolPathEnoughMassAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (stage : Nat) -> (hstage : stage < z) ->
      routedDepthOutputSlots m w stage -> Real
  | 0, hzero, _ =>
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hzero epsilon rhoUnit)
  | stage + 1, hstage, path =>
      let priorPath := routedDepthOutputPathInit m w stage path
      let port := routedDepthOutputPathLast m w stage path
      let priorRate :=
        routedDepthPathRate h hdegree epsilon hsmall stage priorPath
      let hhalf :=
        routedDepthPathNextHalf h hdegree epsilon hsmall priorPath port
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage (by omega) priorPath *
        decodedRetryPoolEnoughMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree priorRate z q ⟨stage, by omega⟩ hstage port hhalf
            rhoUnit)

@[simp] theorem decodedRetryPoolProtocolPathEnoughMassAux_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : routedDepthOutputSlots m w 0) :
    decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit 0 hz path =
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) :=
  rfl

@[simp] theorem decodedRetryPoolProtocolPathEnoughMassAux_succ
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : routedDepthOutputSlots m w (stage + 1)) :
    decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit (stage + 1) hstage path =
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage (by omega)
            (routedDepthOutputPathInit m w stage path) *
        decodedRetryPoolEnoughMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (routedDepthOutputPathInit m w stage path))
            z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (routedDepthOutputPathInit m w stage path)
              (routedDepthOutputPathLast m w stage path))
            rhoUnit) :=
  rfl

/-- Every recursively accumulated physical enough-event mass is
nonnegative. -/
theorem decodedRetryPoolProtocolPathEnoughMassAux_nonneg
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      0 ≤ decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit stage hstage path := by
  intro stage
  induction stage with
  | zero =>
      intro hstage path
      rw [decodedRetryPoolProtocolPathEnoughMassAux_zero]
      exact decodedRetryPoolEnoughMass_nonneg h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hstage⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hstage epsilon rhoUnit)
  | succ stage ih =>
      intro hstage path
      rw [decodedRetryPoolProtocolPathEnoughMassAux_succ]
      exact mul_nonneg
        (ih (by omega) (routedDepthOutputPathInit m w stage path))
        (decodedRetryPoolEnoughMass_nonneg h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (routedDepthOutputPathInit m w stage path))
            z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (routedDepthOutputPathInit m w stage path)
              (routedDepthOutputPathLast m w stage path))
            rhoUnit))

/-- Every recursively accumulated physical enough-event mass is at most the
complete root Born mass. -/
theorem decodedRetryPoolProtocolPathEnoughMassAux_le_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit stage hstage path ≤ 1 := by
  intro stage
  induction stage with
  | zero =>
      intro hstage path
      rw [decodedRetryPoolProtocolPathEnoughMassAux_zero]
      exact decodedRetryPoolEnoughMass_le_one h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hstage⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hstage epsilon rhoUnit)
  | succ stage ih =>
      intro hstage path
      rw [decodedRetryPoolProtocolPathEnoughMassAux_succ]
      let nextMass := decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall stage
            (routedDepthOutputPathInit m w stage path))
          z q ⟨stage, by omega⟩ hstage
          (routedDepthOutputPathLast m w stage path)
          (routedDepthPathNextHalf h hdegree epsilon hsmall
            (routedDepthOutputPathInit m w stage path)
            (routedDepthOutputPathLast m w stage path))
          rhoUnit)
      calc
        decodedRetryPoolProtocolPathEnoughMassAux
              h hdegree epsilon hsmall z q rhoUnit stage (by omega)
                (routedDepthOutputPathInit m w stage path) * nextMass ≤
            1 * nextMass :=
          mul_le_mul_of_nonneg_right
            (ih (by omega) (routedDepthOutputPathInit m w stage path))
            (decodedRetryPoolEnoughMass_nonneg h hdegree
              (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
              (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
              (decodedRetryPoolSuccessorStageSelectedNextInput
                h hdegree
                (routedDepthPathRate h hdegree epsilon hsmall stage
                  (routedDepthOutputPathInit m w stage path))
                z q ⟨stage, by omega⟩ hstage
                (routedDepthOutputPathLast m w stage path)
                (routedDepthPathNextHalf h hdegree epsilon hsmall
                  (routedDepthOutputPathInit m w stage path)
                  (routedDepthOutputPathLast m w stage path))
                rhoUnit))
        _ = nextMass := one_mul nextMass
        _ ≤ 1 := decodedRetryPoolEnoughMass_le_one h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (routedDepthOutputPathInit m w stage path))
            z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (routedDepthOutputPathInit m w stage path)
              (routedDepthOutputPathLast m w stage path))
            rhoUnit)

private theorem decodedRetryPoolNestedPathEquiv_symm_succ
    (m w stage : Nat)
    (path : routedDepthOutputSlots m w (stage + 1)) :
    (decodedRetryPoolNestedPathEquiv m w (stage + 1)).symm path =
      ((decodedRetryPoolNestedPathEquiv m w stage).symm
          (routedDepthOutputPathInit m w stage path),
        decodedRetryPoolLogicalSiteFinEquiv m w
          (routedDepthOutputPathLast m w stage path)) := by
  apply (decodedRetryPoolNestedPathEquiv m w (stage + 1)).injective
  simp only [Equiv.apply_symm_apply,
    decodedRetryPoolNestedPathEquiv_append, Equiv.symm_apply_apply]
  exact (routedDepthOutputPath_append_init_last m w stage path).symm

/-- The selected successor-port enough-event operator on an arbitrary
unnormalized predecessor-path input. -/
noncomputable def decodedRetryPoolProtocolPathSuccessorEnoughOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage, by omega⟩) × LogicalSite m w))) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage + 1, hstage⟩) × LogicalSite m w)) :=
  tensorPowerCoordinateOperator (logicalOutputCount m w)
    (decodedRetryPoolLogicalSiteFinEquiv m w port)
    (∑ successorOutcome : decodedRetryPoolSuccessorStageOutcome
        m w z q ⟨stage, by omega⟩ hstage,
      if decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage port successorOutcome = true then
        (decodedRetryPoolSuccessorStageInstrument
          h hdegree z q ⟨stage, by omega⟩ hstage).branchOperator
            successorOutcome A
      else 0)

/-- The arbitrary-input selected successor operator is complex-linear. -/
theorem decodedRetryPoolProtocolPathSuccessorEnoughOperator_smul
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w) (c : Complex)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage, by omega⟩) × LogicalSite m w))) :
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port (c • A) =
      c • decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port A := by
  classical
  unfold decodedRetryPoolProtocolPathSuccessorEnoughOperator
  rw [← map_smul, Finset.smul_sum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro successorOutcome _
  by_cases hsuccess :
      decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q ⟨stage, by omega⟩ hstage port successorOutcome = true
  · simp only [hsuccess, if_true]
    exact branchOperator_smul
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q ⟨stage, by omega⟩ hstage)
      successorOutcome c A
  · simp [hsuccess]

/-- On a genuine accepted predecessor product, the arbitrary-input selected
successor operator is the measured next-pool enough mass times the genuine
next accepted product. -/
theorem
    decodedRetryPoolProtocolPathSuccessorEnoughOperator_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage port
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage, by omega⟩)).toOperator =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree epsilon z q ⟨stage, by omega⟩ hstage port hhalf
          rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree
          (selectedLogicalPortNextInputRate
            h hdegree epsilon port hhalf)
          rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)).toOperator := by
  exact decodedRetryPoolSuccessorStage_selectedEnoughBranch_sum
    h hdegree epsilon z q ⟨stage, by omega⟩ hstage port hhalf rhoUnit

/-- The root successful-event operator before any recursive path layer. -/
noncomputable def decodedRetryPoolProtocolRootSuccessfulBranchOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) ×
        LogicalSite m w)) :=
  ∑ outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz,
    if decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        outcome = true then
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)).branchOperator
          outcome rho.toOperator
    else 0

/-- On the genuine noisy root input, the root successful-event operator is
the measured root enough mass times the accepted-product density. -/
theorem decodedRetryPoolProtocolRootSuccessfulBranchOperator_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolRootSuccessfulBranchOperator h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)).toOperator := by
  exact
    (decodedRetryPool_enoughBranch_sum_eq_enoughMass_smul_acceptedProduct
      h hdegree epsilon rhoUnit
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩))

/-- Recursive evaluator for the same selected-path successful event.  This
definition is kept separate from the global history sum so recursive proofs
never normalize the complete dependent protocol expression. -/
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    (stage : Nat) -> (hstage : stage < z) ->
      routedDepthOutputSlots m w stage ->
      Operator (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage, hstage⟩) ×
          LogicalSite m w))
  | 0, hzero, _ =>
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hzero rho
  | stage + 1, hstage, path =>
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage
          (routedDepthOutputPathLast m w stage path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
            h hdegree z q hz rho stage (by omega)
              (routedDepthOutputPathInit m w stage path))

@[simp] theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) (path : routedDepthOutputSlots m w 0) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
        h hdegree z q hz rho 0 hz path =
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hz rho :=
  rfl

@[simp] theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_succ
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) (path : routedDepthOutputSlots m w (stage + 1)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
        h hdegree z q hz rho (stage + 1) hstage path =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q stage hstage
          (routedDepthOutputPathLast m w stage path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
            h hdegree z q hz rho stage (by omega)
              (routedDepthOutputPathInit m w stage path)) :=
  rfl

/-- The recursive evaluator is its recursively measured enough mass times the
genuine accepted-product density at the reached routed rate. -/
private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
          h hdegree z q hz
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit)
            stage hstage path =
        (decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage hstage path : Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, hstage⟩)).toOperator := by
  intro stage
  induction stage with
  | zero =>
      intro hzero path
      rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_zero]
      exact decodedRetryPoolProtocolRootSuccessfulBranchOperator_eq
        h hdegree epsilon z q hzero rhoUnit
  | succ stage ih =>
      intro hstage path
      let priorPath := routedDepthOutputPathInit m w stage path
      let port := routedDepthOutputPathLast m w stage path
      let priorRate :=
        routedDepthPathRate h hdegree epsilon hsmall stage priorPath
      let hhalf :=
        routedDepthPathNextHalf h hdegree epsilon hsmall priorPath port
      let priorMass := decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit stage (by omega) priorPath
      let nextMass := decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
        (decodedRetryPoolSuccessorStageSelectedNextInput
          h hdegree priorRate z q ⟨stage, by omega⟩ hstage port hhalf
          rhoUnit)
      let nextAccepted := decodedRetryPoolAcceptedProductDensity h hdegree
        (selectedLogicalPortNextInputRate
          h hdegree priorRate port hhalf)
        rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage + 1, hstage⟩)
      rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_succ]
      rw [ih (by omega) priorPath]
      rw [decodedRetryPoolProtocolPathSuccessorEnoughOperator_smul]
      rw [decodedRetryPoolProtocolPathSuccessorEnoughOperator_acceptedProduct
        h hdegree priorRate z q stage hstage port hhalf rhoUnit]
      rw [smul_smul]
      have hrate :
          routedDepthPathRate h hdegree epsilon hsmall (stage + 1) path =
            selectedLogicalPortNextInputRate
              h hdegree priorRate port hhalf := by
        rw [← routedDepthOutputPath_append_init_last m w stage path]
        exact routedDepthPathRate_append_eq_nextInputRate
          h hdegree epsilon hsmall priorPath port
      change ((priorMass : Complex) * (nextMass : Complex)) •
          nextAccepted.toOperator =
        (decodedRetryPoolProtocolPathEnoughMassAux
              h hdegree epsilon hsmall z q rhoUnit (stage + 1) hstage path :
                Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall (stage + 1) path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage + 1, hstage⟩)).toOperator
      simp only [decodedRetryPoolProtocolPathEnoughMassAux_succ,
        priorPath, port, priorRate, priorMass, nextMass,
        nextAccepted, hrate, Complex.ofReal_mul]

/-- Every successful physical routed-path branch is its recursively measured
enough mass multiplying the genuine accepted-product density at that path's
actual reached rate. -/
theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
          h hdegree z q hz
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit)
            stage hstage path =
        (decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage hstage path : Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, hstage⟩)).toOperator := by
  intro stage hstage path
  exact decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq
    h hdegree epsilon hsmall z q hz rhoUnit stage hstage path

end HH18Parameterized
end Distillation
end QEC

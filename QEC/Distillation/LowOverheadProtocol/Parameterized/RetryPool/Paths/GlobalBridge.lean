import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Paths.BranchOperator

/-!
# Global-history bridge for one successful physical routed path

The complete protocol stores every predecessor observation and one nested
successor history.  This layer first retains the predecessor nested leaf,
then its newest tensor coordinate.  That two-step marginal is exactly the
recursive physical path operator, so the compiled measured-mass/product
identity applies to the original whole-history event as well.
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

private theorem decodedRetryPoolNestedPathEquiv_symm_succ_global
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

/-- Before retaining the newest selected logical port, retain the complete
successor-stage output at the selected predecessor nested path. -/
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (tensorPowerCarrier
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          ⟨previous.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  bindNestedFilteredCoordinateOperator
    (logicalOutputCount m w) previous.1
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz previous.1 previous.2)
    (decodedRetryPoolSuccessorStageInstrument
      h hdegree z q previous hstage)
    (fun priorOutcome =>
      decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q previous.1 previous.2
          (routedDepthOutputPathInit m w previous.1 path) priorOutcome = true)
    (fun successorOutcome =>
      decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q previous hstage
          (routedDepthOutputPathLast m w previous.1 path) successorOutcome = true)
    ((decodedRetryPoolNestedPathEquiv m w previous.1).symm
      (routedDepthOutputPathInit m w previous.1 path))
    rho.toOperator

/-- The complete selected-successor enough-event operator before tracing to
its nominated logical port. -/
noncomputable def decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (previous : Fin z) (hstage : previous.1 + 1 < z)
    (port : LogicalSite m w)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        previous) × LogicalSite m w))) :
    Operator (tensorPowerCarrier
      (QubitRegister
        (Fin (decodedRetryPoolBackwardSchedule m w z q
          ⟨previous.1 + 1, hstage⟩) × LogicalSite m w))
      (logicalOutputCount m w)) :=
  filteredBranchOperatorSum
    (decodedRetryPoolSuccessorStageInstrument
      h hdegree z q previous hstage)
    (fun successorOutcome =>
      decodedRetryPoolSuccessorStageSelectedPoolEnough
        m w z q previous hstage port successorOutcome = true)
    A

/-- The preceding whole-history path marginal, with its carrier exposed
syntactically for the selected successor instrument. -/
noncomputable def decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (priorPath : routedDepthOutputSlots m w previous.1)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        previous) × LogicalSite m w)) :=
  nestedFilteredPredecessorCoordinateOperator
    (logicalOutputCount m w) previous.1
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz previous.1 previous.2)
    (fun priorOutcome =>
      decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q previous.1 previous.2 priorPath priorOutcome = true)
    ((decodedRetryPoolNestedPathEquiv m w previous.1).symm priorPath)
    rho.toOperator

/-- For an explicitly appended path, the outer selected predecessor marginal
is the local selected-successor branch sum applied to the original global
predecessor path marginal. -/
private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux_append_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (priorPath : routedDepthOutputSlots m w previous.1)
    (port : LogicalSite m w)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
        h hdegree z q hz previous hstage
          (routedDepthOutputPathAppend m w previous.1 priorPath port) rho =
      decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
        h hdegree z q previous hstage port
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
            h hdegree z q hz previous priorPath rho) := by
  classical
  simpa only [
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux,
    decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator,
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux,
    routedDepthOutputPathInit_append, routedDepthOutputPathLast_append] using
    (bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
      (logicalOutputCount m w) previous.1
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz previous.1 previous.2)
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q previous hstage)
      (decodedRetryPoolSuccessorStageInstrument_complete
        h hdegree z q previous hstage)
      (fun priorOutcome =>
        decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q previous.1 previous.2 priorPath priorOutcome = true)
      (fun successorOutcome =>
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q previous hstage port successorOutcome = true)
      ((decodedRetryPoolNestedPathEquiv m w previous.1).symm priorPath)
      rho.toOperator)

private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_outer
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz (previous.1 + 1) hstage path rho =
      tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w
          (routedDepthOutputPathLast m w previous.1 path))
        (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
          h hdegree z q hz previous hstage path rho) := by
  classical
  rcases previous with ⟨stage, hprevious⟩
  unfold decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
  rw [decodedRetryPoolNestedPathEquiv_symm_succ_global m w stage path]
  rw [nestedTensorCoordinateOperator_succ]
  apply congrArg
    (tensorPowerCoordinateOperator (logicalOutputCount m w)
      (decodedRetryPoolLogicalSiteFinEquiv m w
        (routedDepthOutputPathLast m w stage path)))
  unfold decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
    bindNestedFilteredCoordinateOperator
  rw [decodedRetryPoolProtocolInstrumentAux_succ]
  simp only [decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ,
    Bool.and_eq_true]
  unfold decodedRetryPoolProtocolSuccessorInstrumentAux
    decodedRetryPoolNestedSuccessorStageInstrument
  rfl

private theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (priorPath : routedDepthOutputSlots m w previous.1)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
        h hdegree z q hz previous priorPath rho =
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz previous.1 previous.2 priorPath rho := by
  rcases previous with ⟨stage, hprevious⟩
  unfold decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
    nestedFilteredPredecessorCoordinateOperator
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
  rfl

private theorem
    decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (previous : Fin z) (hstage : previous.1 + 1 < z)
    (port : LogicalSite m w)
    (A : Operator (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q previous) ×
        LogicalSite m w))) :
    tensorPowerCoordinateOperator (logicalOutputCount m w)
        (decodedRetryPoolLogicalSiteFinEquiv m w port)
        (decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
          h hdegree z q previous hstage port A) =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q previous.1 hstage port A := by
  rcases previous with ⟨stage, hprevious⟩
  unfold decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
    decodedRetryPoolProtocolPathSuccessorEnoughOperator
    filteredBranchOperatorSum
  rfl

/-- The original whole-history selected path marginal obeys the same literal
successor recurrence as the recursive physical path operator. -/
theorem decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (previous : Fin z)
    (hstage : previous.1 + 1 < z)
    (path : routedDepthOutputSlots m w (previous.1 + 1))
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz (previous.1 + 1) hstage path rho =
      decodedRetryPoolProtocolPathSuccessorEnoughOperator
        h hdegree z q previous.1 hstage
          (routedDepthOutputPathLast m w previous.1 path)
          (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
            h hdegree z q hz previous.1 previous.2
              (routedDepthOutputPathInit m w previous.1 path) rho) := by
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_outer]
  have houter :
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
          h hdegree z q hz previous hstage path rho =
        decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator
          h hdegree z q previous hstage
            (routedDepthOutputPathLast m w previous.1 path)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux
              h hdegree z q hz previous
                (routedDepthOutputPathInit m w previous.1 path) rho) := by
    calc
      _ = decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
          h hdegree z q hz previous hstage
            (routedDepthOutputPathAppend m w previous.1
              (routedDepthOutputPathInit m w previous.1 path)
              (routedDepthOutputPathLast m w previous.1 path)) rho := by
          apply congrArg (fun selectedPath =>
            decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux
              h hdegree z q hz previous hstage selectedPath rho)
          exact
            (routedDepthOutputPath_append_init_last
              m w previous.1 path).symm
      _ = _ :=
        decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalOuterAux_append_eq
          h hdegree z q hz previous hstage
            (routedDepthOutputPathInit m w previous.1 path)
            (routedDepthOutputPathLast m w previous.1 path) rho
  rw [houter]
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalPriorAux_eq]
  exact decodedRetryPoolProtocolPathSuccessorEnoughGlobalOperator_eq
    h hdegree z q previous hstage
      (routedDepthOutputPathLast m w previous.1 path)
      (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz previous.1 previous.2
          (routedDepthOutputPathInit m w previous.1 path) rho)

private theorem decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_zero
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (path : routedDepthOutputSlots m w 0)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz 0 hz path rho =
      decodedRetryPoolProtocolRootSuccessfulBranchOperator
        h hdegree z q hz rho := by
  rfl

/-- The selected marginal of the original complete physical-history event is
exactly its OOM-safe recursive finite-instrument construction. -/
theorem decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz stage hstage path rho =
        decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
          h hdegree z q hz rho stage hstage path := by
  intro stage
  induction stage with
  | zero =>
      intro hzero path
      rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_zero]
      rfl
  | succ stage ih =>
      intro hstage path
      rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_succ
        h hdegree z q hz ⟨stage, by omega⟩ hstage path rho]
      rw [ih (by omega) (routedDepthOutputPathInit m w stage path)]
      rfl

/-- Consequently the original whole-history selected path event is its
measured enough-mass product times the genuine reached accepted product. -/
theorem
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz stage hstage path
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) =
        (decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage hstage path : Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, hstage⟩)).toOperator := by
  intro stage hstage path
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_recursive]
  exact
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct
      h hdegree epsilon hsmall z q hz rhoUnit stage hstage path

end HH18Parameterized
end Distillation
end QEC

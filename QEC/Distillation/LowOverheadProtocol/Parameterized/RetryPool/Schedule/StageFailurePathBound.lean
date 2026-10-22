import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Paths.GlobalBridge
import QEC.Semantics.Instruments.Sequential.NestedFilteredMarginalBranchOperator
/-!
# Routed-path bound for one physical retry-stage failure

The literal global predecessor-success/new-stage-failure event is relaxed to
one charged failing nested leaf.  At that leaf, global predecessor success is
replaced only by the weaker literal selected routed-path success that it
implies.  The result is an operator-level sum over true unnormalized path
marginals, with no normalization or sibling-independence premise.
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

local instance instStageFailurePathBoundClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The concrete output carrier of one base successor-stage instrument. -/
abbrev decodedRetryPoolSuccessorStageOutputCarrier
    (m w z q stage : Nat) (hstage : stage + 1 < z) :=
  tensorPowerCarrier
    (QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage + 1, hstage⟩) × LogicalSite m w))
    (logicalOutputCount m w)

/-- The real successor-stage failure trace charged to one literal nested
path of the original global physical history. -/
noncomputable def decodedRetryPoolProtocolPathFailureTraceAux
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (path : nestedTensorPath (logicalOutputCount m w) stage)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) : Real :=
  Complex.re (LinearMap.trace Complex
    (decodedRetryPoolSuccessorStageOutputCarrier m w z q stage hstage)
    (filteredBranchOperatorSum
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (fun successorOutcome =>
        decodedRetryPoolSuccessorStageRoutingGood
          m w z q ⟨stage, by omega⟩ hstage successorOutcome ≠ true)
      (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
        h hdegree z q hz stage (by omega)
          (decodedRetryPoolNestedPathEquiv m w stage path) rho)))

/-- The actual global stage-routing failure mass is bounded by a sum of local
successor-stage failure traces on the genuine unnormalized predecessor-path
operators. -/
theorem decodedRetryPoolProtocolStageRoutingFailureMass_le_pathFailureTraceSum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier
      m w z q hz)) :
    decodedRetryPoolProtocolStageRoutingFailureMass
        h hdegree z q hz stage hstage rho <=
      ∑ path : nestedTensorPath (logicalOutputCount m w) stage,
        decodedRetryPoolProtocolPathFailureTraceAux
          h hdegree z q hz stage hstage path rho := by
  classical
  have hbound :=
    bind_nestedTensor_bornWeight_first_implies_path_and_any_failure_le_filteredBranchTrace
      (logicalOutputCount m w) stage
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega))
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (decodedRetryPoolSuccessorStageInstrument_complete
        h hdegree z q ⟨stage, by omega⟩ hstage)
      (fun priorOutcome =>
        decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) priorOutcome = true)
      (fun path priorOutcome =>
        decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage (by omega)
            (decodedRetryPoolNestedPathEquiv m w stage path) priorOutcome = true)
      (fun successorOutcome =>
        decodedRetryPoolSuccessorStageRoutingGood
          m w z q ⟨stage, by omega⟩ hstage successorOutcome ≠ true)
      (fun priorOutcome path hglobal =>
        decodedRetryPoolProtocolSuccessfulRoutingAux_implies_path
          m w z q stage (by omega) priorOutcome hglobal
            (decodedRetryPoolNestedPathEquiv m w stage path))
      rho
  rw [Finset.sum_filter] at hbound
  have hbound' :
      (∑ outcome : Sigma fun _ : decodedRetryPoolProtocolOutcomeAux
            m w z q stage (by omega) =>
          nestedTensorHistory
            (decodedRetryPoolSuccessorStageOutcome
              m w z q ⟨stage, by omega⟩ hstage)
            (logicalOutputCount m w) stage,
        if decodedRetryPoolProtocolSuccessfulRoutingAux
              m w z q stage (by omega) outcome.1 = true ∧
            nestedTensorHistoryAll
              (decodedRetryPoolSuccessorStageRoutingGood
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage outcome.2 ≠ true then
          ((decodedRetryPoolProtocolInstrumentAux
              h hdegree z q hz stage (by omega)).bind
            (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
              h hdegree z q stage hstage)).bornWeight outcome rho
        else 0) <=
        ∑ path : nestedTensorPath (logicalOutputCount m w) stage,
          Complex.re (LinearMap.trace Complex
            (decodedRetryPoolSuccessorStageOutputCarrier m w z q stage hstage)
            (filteredBranchOperatorSum
              (decodedRetryPoolSuccessorStageInstrument
                h hdegree z q ⟨stage, by omega⟩ hstage)
              (fun successorOutcome =>
                decodedRetryPoolSuccessorStageRoutingGood
                  m w z q ⟨stage, by omega⟩ hstage successorOutcome ≠ true)
              (nestedFilteredPredecessorCoordinateOperator
                (logicalOutputCount m w) stage
                (decodedRetryPoolProtocolInstrumentAux
                  h hdegree z q hz stage (by omega))
                (fun priorOutcome =>
                  decodedRetryPoolProtocolPathSuccessfulRoutingAux
                    m w z q stage (by omega)
                      (decodedRetryPoolNestedPathEquiv m w stage path)
                      priorOutcome = true)
                path rho.toOperator))) := by
    simpa only [nestedTensorHistoryAll_ne_true_iff_exists,
      decodedRetryPoolProtocolSuccessorInstrumentAux,
      decodedRetryPoolNestedSuccessorStageInstrument,
      decodedRetryPoolSuccessorStageOutputCarrier] using hbound
  unfold decodedRetryPoolProtocolStageRoutingFailureMass
  rw [Finset.sum_filter, decodedRetryPoolProtocolInstrumentAux_succ]
  refine hbound'.trans_eq ?_
  apply Finset.sum_congr rfl
  intro path _
  unfold decodedRetryPoolProtocolPathFailureTraceAux
    decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
    nestedFilteredPredecessorCoordinateOperator
  rw [(decodedRetryPoolNestedPathEquiv m w stage).symm_apply_apply]

/-- On the genuine noisy root input, one routed-path failure trace is bounded
by the true shortage masses of the physical successor pools at that path's
reached rate.  The predecessor branch remains unnormalized; its mass is
dropped only using the proved physical probability bound `mass ≤ 1`. -/
theorem decodedRetryPoolProtocolPathFailureTraceAux_le_portShortageSum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : nestedTensorPath (logicalOutputCount m w) stage) :
    decodedRetryPoolProtocolPathFailureTraceAux
        h hdegree z q hz stage hstage path
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) ≤
      ∑ port : LogicalSite m w,
        decodedRetryPoolShortageMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (decodedRetryPoolNestedPathEquiv m w stage path))
            z q ⟨stage, by omega⟩ hstage port
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (decodedRetryPoolNestedPathEquiv m w stage path) port)
            rhoUnit) := by
  classical
  let routedPath := decodedRetryPoolNestedPathEquiv m w stage path
  let rate := routedDepthPathRate h hdegree epsilon hsmall stage routedPath
  let mass := decodedRetryPoolProtocolPathEnoughMassAux
    h hdegree epsilon hsmall z q rhoUnit stage (by omega) routedPath
  let failureMass :=
    ∑ outcome ∈ Finset.univ.filter
        (fun successorOutcome : decodedRetryPoolSuccessorStageOutcome
            m w z q ⟨stage, by omega⟩ hstage =>
          decodedRetryPoolSuccessorStageRoutingGood
            m w z q ⟨stage, by omega⟩ hstage successorOutcome ≠ true),
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q ⟨stage, by omega⟩ hstage).bornWeight outcome
          (decodedRetryPoolAcceptedProductDensity h hdegree rate rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, by omega⟩))
  have hfailureMassNonneg : 0 ≤ failureMass := by
    dsimp [failureMass]
    exact Finset.sum_nonneg fun outcome _ =>
      (decodedRetryPoolSuccessorStageInstrument
        h hdegree z q ⟨stage, by omega⟩ hstage).bornWeight_nonneg outcome
          (decodedRetryPoolAcceptedProductDensity h hdegree rate rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, by omega⟩))
  have hmassLe : mass ≤ 1 := by
    exact decodedRetryPoolProtocolPathEnoughMassAux_le_one
      h hdegree epsilon hsmall z q rhoUnit stage (by omega) routedPath
  have hfailure := decodedRetryPoolSuccessorStageFailureMass_le_portShortageSum
    h hdegree rate z q ⟨stage, by omega⟩ hstage
    (fun port => routedDepthPathNextHalf h hdegree epsilon hsmall routedPath port)
    rhoUnit
  unfold decodedRetryPoolProtocolPathFailureTraceAux
  rw [decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
    h hdegree epsilon hsmall z q hz rhoUnit stage (by omega) routedPath]
  rw [filteredBranchOperatorSum_trace_re_smul_real]
  change mass * failureMass ≤ _
  calc
    mass * failureMass ≤ 1 * failureMass :=
      mul_le_mul_of_nonneg_right hmassLe hfailureMassNonneg
    _ = failureMass := one_mul failureMass
    _ ≤ _ := hfailure

/-- One routed-path failure trace is bounded by one copy of the physical
successor-stage envelope budget. -/
theorem decodedRetryPoolProtocolPathFailureTraceAux_le_pathBudget
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : nestedTensorPath (logicalOutputCount m w) stage) :
    decodedRetryPoolProtocolPathFailureTraceAux
        h hdegree z q hz stage hstage path
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) ≤
      (logicalOutputCount m w : Real) *
        decodedRetryPoolDyadicDenominator (stage + 1) *
        physicalInputCount m w *
        routedDepthErrorEnvelope w r m epsilon (stage + 1) := by
  classical
  let routedPath := decodedRetryPoolNestedPathEquiv m w stage path
  let rate := routedDepthPathRate h hdegree epsilon hsmall stage routedPath
  let required := decodedRetryPoolBackwardSchedule m w z q
    ⟨stage + 1, hstage⟩
  let perPortBudget : Real :=
    decodedRetryPoolDyadicDenominator (stage + 1) *
      physicalInputCount m w *
      routedDepthErrorEnvelope w r m epsilon (stage + 1)
  have hport (port : LogicalSite m w) :
      decodedRetryPoolShortageMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          required
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree rate z q ⟨stage, by omega⟩ hstage port
              (routedDepthPathNextHalf
                h hdegree epsilon hsmall routedPath port)
            rhoUnit) ≤ perPortBudget := by
    let nextRate := selectedLogicalPortNextInputRate h hdegree rate port
      (routedDepthPathNextHalf h hdegree epsilon hsmall routedPath port)
    have hshortage := decodedRetryPoolDyadicShortageMass_le_noisyResources
      h hdegree nextRate rhoUnit (stage + 1) required
    have hrate := routedDepthPathRate_le_errorEnvelope
      h hdegree epsilon hsmall (stage + 1)
        (routedDepthOutputPathAppend m w stage routedPath port)
    rw [routedDepthPathRate_append_eq_nextInputRate] at hrate
    calc
      decodedRetryPoolShortageMass h hdegree
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage + 1, hstage⟩)
            required
            (decodedRetryPoolSuccessorStageSelectedNextInput
              h hdegree rate z q ⟨stage, by omega⟩ hstage port
                (routedDepthPathNextHalf
                  h hdegree epsilon hsmall routedPath port)
              rhoUnit) ≤
          (decodedRetryPoolDyadicDenominator (stage + 1) : Real) *
            physicalInputCount m w * nextRate.1 := by
        simpa [decodedRetryPoolBackwardAttempts,
          decodedRetryPoolSuccessorStageSelectedNextInput,
          nextRate] using hshortage
      _ ≤ perPortBudget := by
        exact mul_le_mul_of_nonneg_left hrate
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    decodedRetryPoolProtocolPathFailureTraceAux
          h hdegree z q hz stage hstage path
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) ≤
        ∑ port : LogicalSite m w,
          decodedRetryPoolShortageMass h hdegree
            (decodedRetryPoolBackwardAttempts m w z q
              ⟨stage + 1, hstage⟩)
            required
            (decodedRetryPoolSuccessorStageSelectedNextInput
              h hdegree rate z q ⟨stage, by omega⟩ hstage port
                (routedDepthPathNextHalf
                  h hdegree epsilon hsmall routedPath port)
              rhoUnit) := by
      simpa [routedPath, rate, required] using
        decodedRetryPoolProtocolPathFailureTraceAux_le_portShortageSum
          h hdegree epsilon hsmall z q hz stage hstage rhoUnit path
    _ ≤ ∑ _port : LogicalSite m w, perPortBudget :=
      Finset.sum_le_sum fun port _ => hport port
    _ = (logicalOutputCount m w : Real) *
          decodedRetryPoolDyadicDenominator (stage + 1) *
          physicalInputCount m w *
          routedDepthErrorEnvelope w r m epsilon (stage + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [logicalOutputCount, perPortBudget]
      ring

/-- The literal global predecessor-success/new-stage-failure mass is bounded
by the existing aggregate physical shortage budget at the appended stage. -/
theorem
    decodedRetryPoolProtocolStageRoutingFailureMass_le_stageAggregateShortageBudget
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolStageRoutingFailureMass
        h hdegree z q hz stage hstage
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) ≤
      decodedRetryPoolStageAggregateShortageBudget
        w r m epsilon (stage + 1) := by
  classical
  let pathBudget : Real :=
    (logicalOutputCount m w : Real) *
      decodedRetryPoolDyadicDenominator (stage + 1) *
      physicalInputCount m w *
      routedDepthErrorEnvelope w r m epsilon (stage + 1)
  calc
    decodedRetryPoolProtocolStageRoutingFailureMass
          h hdegree z q hz stage hstage
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) ≤
        ∑ path : nestedTensorPath (logicalOutputCount m w) stage,
          decodedRetryPoolProtocolPathFailureTraceAux
            h hdegree z q hz stage hstage path
              (decodedRetryPoolPhysicalProtocolNoisyRootInput
                m w z q hz epsilon rhoUnit) :=
      decodedRetryPoolProtocolStageRoutingFailureMass_le_pathFailureTraceSum
        h hdegree z q hz stage hstage
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit)
    _ ≤ ∑ _path : nestedTensorPath (logicalOutputCount m w) stage,
          pathBudget :=
      Finset.sum_le_sum fun path _ => by
        simpa [pathBudget] using
          decodedRetryPoolProtocolPathFailureTraceAux_le_pathBudget
            h hdegree epsilon hsmall z q hz stage hstage rhoUnit path
    _ = decodedRetryPoolStageAggregateShortageBudget
          w r m epsilon (stage + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [decodedRetryPoolNestedPath_card]
      unfold decodedRetryPoolStageAggregateShortageBudget
      push_cast
      simp only [pathBudget]
      ring

end HH18Parameterized
end Distillation
end QEC

import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.StageFailurePathBound

/-!
# Physical retry-pool success lower bound

This module telescopes the exact physical successful-prefix recurrence.  The
root shortage and every literal successor-stage routing failure are charged
to the already-derived finite budget, yielding a uniform lower bound for the
accepted Born mass of the complete physical protocol.
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

/-- Through every bounded physical stage, the successful-routing mass is at
least one minus the sum of the literal aggregate shortage budgets already
incurred. -/
theorem decodedRetryPoolProtocolSuccessfulRoutingMassAux_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z),
      1 - (∑ incurred : Fin (stage + 1),
          decodedRetryPoolStageAggregateShortageBudget
            w r m epsilon incurred.1) ≤
        decodedRetryPoolProtocolSuccessfulRoutingMassAux
          h hdegree z q hz stage hstage
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) := by
  intro stage
  induction stage with
  | zero =>
      intro hstage
      simpa using
        decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_lower_bound
          h hdegree z q hstage epsilon rhoUnit
  | succ stage ih =>
      intro hstage
      have hprevious := ih (by omega)
      have hpartition :=
        decodedRetryPoolProtocolSuccessfulRoutingMassAux_succ_add_failure
          h hdegree z q hz stage hstage
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit)
      have hfailure :=
        decodedRetryPoolProtocolStageRoutingFailureMass_le_stageAggregateShortageBudget
          h hdegree epsilon hsmall z q hz stage hstage rhoUnit
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      linarith

/-- The accepted Born mass of the complete physical protocol is bounded below
by one minus the sum of all finite stage budgets. -/
theorem decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    1 - (∑ stage : Fin z,
        decodedRetryPoolStageAggregateShortageBudget
          w r m epsilon stage.1) ≤
      decodedRetryPoolPhysicalProtocolSuccessMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by
  cases z with
  | zero => omega
  | succ depth =>
      rw [decodedRetryPoolPhysicalProtocolSuccessMass_eq_aux]
      have hterminal :=
        decodedRetryPoolProtocolSuccessfulRoutingMassAux_lower_bound
          h hdegree epsilon hsmall (depth + 1) q hz rhoUnit depth (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hterminal

/-- In the source-derived pooling domain, the genuine complete physical
protocol succeeds with Born mass at least three quarters, uniformly at every
positive finite depth and terminal batch size. -/
theorem decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_three_quarters_le
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (3 / 4 : Real) ≤
      decodedRetryPoolPhysicalProtocolSuccessMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by
  have hsmall :=
    decodedRetryPoolInitialPoolingDomain_implies_routedDepthInitialSmallDomain
      epsilon hpool
  have hlower := decodedRetryPoolPhysicalProtocolSuccessMass_noisyRoot_lower_bound
    h hdegree epsilon hsmall z q hz rhoUnit
  have hbudget := decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter
    h epsilon hpool z
  linarith

end HH18Parameterized
end Distillation
end QEC

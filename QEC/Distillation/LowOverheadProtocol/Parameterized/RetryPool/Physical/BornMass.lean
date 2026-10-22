import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.SuccessEvent
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Schedule.SuccessBudget
import QEC.Semantics.Instruments.Sequential.BornMass
/-!
# Born-mass marginals of the physical HH18 retry protocol

This internal layer applies source-neutral sequential trace preservation to
the actual recursive retry-pool instrument.  Completing a physical successor
stage preserves every visible prefix history's Born mass exactly.  Later
union bounds may therefore charge a stage-local failure without changing the
mass already assigned to earlier observations.
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

/-- Summing all actual observations of the next complete physical stage
recovers exactly the Born mass of the supplied predecessor history. -/
theorem decodedRetryPoolProtocolInstrumentAux_bornWeight_prefix_succ_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage (by omega)) :
    (∑ nextOutcome : nestedTensorHistory
        (decodedRetryPoolSuccessorStageOutcome
          m w z q ⟨stage, by omega⟩ hstage)
        (logicalOutputCount m w) stage,
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage).bornWeight
          ⟨outcome, nextOutcome⟩ rho) =
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega)).bornWeight outcome rho := by
  change
    (∑ nextOutcome,
      ((decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).bind
        (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
          h hdegree z q stage hstage)).bornWeight
            ⟨outcome, nextOutcome⟩ rho) = _
  exact bind_bornWeight_fst_sum
    (decodedRetryPoolProtocolInstrumentAux
      h hdegree z q hz stage (by omega))
    (fun _ => decodedRetryPoolProtocolSuccessorInstrumentAux
      h hdegree z q stage hstage)
    (fun _ => decodedRetryPoolNestedSuccessorStageInstrument_complete
      h hdegree z q ⟨stage, by omega⟩ hstage)
    outcome rho

/-- Completing the next physical stage also preserves the total Born mass of
the histories whose retained predecessor prefix already routes successfully.
This statement filters only on the prefix and sums every new observation; it
does not assert that the new sibling pools are independent. -/
theorem decodedRetryPoolProtocolInstrumentAux_bornWeight_good_prefix_succ_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    (∑ nextOutcome ∈ Finset.univ.filter
        (fun nextOutcome : decodedRetryPoolProtocolOutcomeAux
            m w z q (stage + 1) hstage =>
          decodedRetryPoolProtocolSuccessfulRoutingAux
            m w z q stage (by omega) nextOutcome.1 = true),
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage).bornWeight nextOutcome rho) =
      ∑ outcome ∈ Finset.univ.filter
          (fun outcome : decodedRetryPoolProtocolOutcomeAux
              m w z q stage (by omega) =>
            decodedRetryPoolProtocolSuccessfulRoutingAux
              m w z q stage (by omega) outcome = true),
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz stage (by omega)).bornWeight outcome rho := by
  classical
  rw [Finset.sum_filter]
  change
    (∑ x : Sigma fun _ : decodedRetryPoolProtocolOutcomeAux
        m w z q stage (by omega) =>
        nestedTensorHistory
          (decodedRetryPoolSuccessorStageOutcome
            m w z q ⟨stage, by omega⟩ hstage)
          (logicalOutputCount m w) stage,
      if decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) x.1 = true then
        (decodedRetryPoolProtocolInstrumentAux
          h hdegree z q hz (stage + 1) hstage).bornWeight x rho
      else 0) = _
  rw [Fintype.sum_sigma, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hgood :
      decodedRetryPoolProtocolSuccessfulRoutingAux
        m w z q stage (by omega) outcome = true
  · simp only [hgood, if_true]
    exact decodedRetryPoolProtocolInstrumentAux_bornWeight_prefix_succ_sum
      h hdegree z q hz stage hstage rho outcome
  · simp [hgood]

end HH18Parameterized
end Distillation
end QEC

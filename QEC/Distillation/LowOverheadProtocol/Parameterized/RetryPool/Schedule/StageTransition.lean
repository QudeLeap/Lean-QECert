import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.HandoffInstrument

/-!
# Parameterized HH18 decoded retry-pool stage transition

This internal physical layer runs the actual next-stage decoded retry pool on
every logical branch of the nested successor carrier.  It binds the complete
successor handoff to a literal tensor power of the next pool, retaining the
raw and observed histories of both stages.
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

/-- The actual raw Kraus history of all next-stage retry pools, one for every
logical branch supplied by the predecessor stage. -/
abbrev decodedRetryPoolStageTransitionNextRawHistory {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerHistory
    (decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w)

/-- The complete transition raw index retains the predecessor handoff branch
and every actual next-stage pool branch. -/
abbrev decodedRetryPoolStageTransitionRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ :
      decodedRetryPoolSuccessorHandoffRawIndex h hdegree z q stage hstage =>
    decodedRetryPoolStageTransitionNextRawHistory h hdegree z q stage hstage

/-- The visible history of all next-stage decoded pools. -/
abbrev decodedRetryPoolStageTransitionNextOutcome
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerHistory
    (Sigma fun _ : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩) => PUnit)
    (logicalOutputCount m w)

/-- The complete visible transition outcome retains the predecessor handoff
observation followed by every next-stage pool observation. -/
abbrev decodedRetryPoolStageTransitionOutcome
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : decodedRetryPoolSuccessorHandoffOutcome m w z q stage =>
    decodedRetryPoolStageTransitionNextOutcome m w z q stage hstage

/-- The literal selected-output carrier of all next-stage decoded pools. -/
abbrev decodedRetryPoolStageTransitionOutputCarrier
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  tensorPowerCarrier
    (Qubit.QubitRegister
      (Fin (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩) ×
        LogicalSite m w))
    (logicalOutputCount m w)

/-- The actual physical stage transition: complete predecessor pool/handoff,
then the actual next-stage pool independently applied as a tensor operation to
each logical branch of the (possibly correlated) nested input density. -/
noncomputable def decodedRetryPoolStageTransitionInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (decodedRetryPoolStageTransitionRawIndex h hdegree z q stage hstage)
      (decodedRetryPoolStageTransitionOutcome m w z q stage hstage)
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))
      (decodedRetryPoolStageTransitionOutputCarrier m w z q stage hstage) :=
  (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).bindDependent
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))

/-- The visible transition result is exactly the predecessor handoff outcome
followed by the actual observed histories of all next-stage pools. -/
theorem decodedRetryPoolStageTransitionInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : decodedRetryPoolSuccessorHandoffRawIndex
      h hdegree z q stage hstage)
    (secondHistory : decodedRetryPoolStageTransitionNextRawHistory
      h hdegree z q stage hstage) :
    (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondHistory⟩ =
      ⟨(decodedRetryPoolSuccessorHandoffInstrument
          h hdegree z q stage hstage).observe firstIndex,
        ((decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).tensorPower
              (logicalOutputCount m w)).observe secondHistory⟩ := by
  exact FiniteInstrument.bindDependent_observe
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage)
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    firstIndex secondHistory

/-- Completeness is inherited from the predecessor handoff and the tensor
power of the actual complete next-stage decoded pool. -/
theorem decodedRetryPoolStageTransitionInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).kraus.Complete := by
  exact FiniteInstrument.bindDependent_complete
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage)
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩)).tensorPower
          (logicalOutputCount m w))
    (decodedRetryPoolSuccessorHandoffInstrument_complete
      h hdegree z q stage hstage)
    (fun _ =>
      (decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩)).tensorPower_complete
            (decodedRetryPoolInstrument_complete h hdegree
              (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
              (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
            (logicalOutputCount m w))

/-- Every physical input density has normalized total observed mass under the
complete two-stage transition. -/
theorem decodedRetryPoolStageTransitionInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))) :
    ∑ outcome,
        (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).bornWeight
          outcome rho = 1 :=
  (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).sum_bornWeight_eq_one
    (decodedRetryPoolStageTransitionInstrument_complete h hdegree z q stage hstage) rho

end HH18Parameterized
end Distillation
end QEC

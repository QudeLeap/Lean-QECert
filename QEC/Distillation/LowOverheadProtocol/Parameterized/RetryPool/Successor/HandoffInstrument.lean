import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Successor.Regrouping
import QEC.Semantics.Channels.Instrument
/-!
# Parameterized HH18 decoded retry-pool successor handoff instrument

This internal physical layer binds an actual decoded retry pool to the
constructed successor preparation/routing/regrouping channel.  The resulting complete
finite instrument retains the pool's observed history and outputs the literal
nested carrier consumed by the next retry-pool layer.
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

/-- The literal dependent raw index of the current decoded retry pool followed
by one chosen Kraus index of the constructed physical successor handoff. -/
abbrev decodedRetryPoolSuccessorHandoffRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :=
  Sigma fun _ : decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage) =>
    Fin ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount)

/-- The visible successor-handoff outcome retains the actual current-stage
decoded pool history and appends only the unit observation of the total
physical preparation/routing/regrouping channel. -/
abbrev decodedRetryPoolSuccessorHandoffOutcome
    (m w z q : Nat) (stage : Fin z) :=
  Sigma fun _ :
      (Sigma fun _ : tensorPowerHistory DistillationOutcome
        (decodedRetryPoolBackwardAttempts m w z q stage) => PUnit) =>
    PUnit

/-- The complete physical handoff instrument from one scheduled retry pool to
the literal nested next-stage input carrier. -/
noncomputable def decodedRetryPoolSuccessorHandoffInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    FiniteInstrument
      (decodedRetryPoolSuccessorHandoffRawIndex h hdegree z q stage hstage)
      (decodedRetryPoolSuccessorHandoffOutcome m w z q stage)
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))
      (decodedRetryPoolSuccessorNestedInputCarrier m w z q stage hstage) :=
  (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage)).bindDependent
    (fun _ => QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))

/-- The handoff observation is precisely the current pool observation followed
by the unit observation of the physical successor channel. -/
theorem decodedRetryPoolSuccessorHandoffInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (secondIndex : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount)) :
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondIndex⟩ =
      ⟨(decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q stage)
          (decodedRetryPoolBackwardSchedule m w z q stage)).observe firstIndex,
        PUnit.unit⟩ := by
  change
    ((decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q stage)
        (decodedRetryPoolBackwardSchedule m w z q stage)).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument
        (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))).observe
      ⟨firstIndex, secondIndex⟩ = _
  exact FiniteInstrument.bindDependent_observe
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (fun _ => QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    firstIndex secondIndex

/-- Completeness follows from the actual retry-pool completeness and the
chosen finite Kraus representation of the constructed CPTP handoff. -/
theorem decodedRetryPoolSuccessorHandoffInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).kraus.Complete := by
  change
    ((decodedRetryPoolInstrument h hdegree
        (decodedRetryPoolBackwardAttempts m w z q stage)
        (decodedRetryPoolBackwardSchedule m w z q stage)).bindDependent
      (fun _ => QuantumChannel.toFiniteInstrument
        (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))).kraus.Complete
  exact FiniteInstrument.bindDependent_complete
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (fun _ => QuantumChannel.toFiniteInstrument
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))
    (decodedRetryPoolInstrument_complete h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (fun _ => QuantumChannel.toFiniteInstrument_complete
      (decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage))

/-- Every density input has normalized total observable Born mass under the
complete current-pool-to-successor physical handoff. -/
theorem decodedRetryPoolSuccessorHandoffInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))) :
    ∑ outcome,
        (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).bornWeight
          outcome rho = 1 :=
  (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).sum_bornWeight_eq_one
    (decodedRetryPoolSuccessorHandoffInstrument_complete h hdegree z q stage hstage) rho

end HH18Parameterized
end Distillation
end QEC

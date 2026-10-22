import QEC.Distillation.Core.FiniteInstrumentBinaryRun
import QEC.Distillation.LowOverheadProtocol.Parameterized.RetryPool.Physical.Protocol

/-!
# Parameterized HH18 physical successful-routing event

This layer defines success directly on the visible outcomes of the complete
physical retry-pool instrument. Every scheduled pool on every retained logical
path must contain enough actual accepted decoded trials. The corresponding
success mass is the accepted Born mass of the binary-coarsened instrument.
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

/-- Boolean conjunction over the literal right-nested finite tensor history. -/
def tensorPowerHistoryAll {alpha : Type*} (predicate : alpha -> Bool) :
    (attempts : Nat) -> tensorPowerHistory alpha attempts -> Bool
  | 0, _ => true
  | attempts + 1, history =>
      predicate history.1 && tensorPowerHistoryAll predicate attempts history.2

/-- The recursive Boolean conjunction holds exactly when the predicate holds
at every literal tensor coordinate. -/
theorem tensorPowerHistoryAll_eq_true_iff {alpha : Type*}
    (predicate : alpha -> Bool) :
    ∀ (attempts : Nat) (history : tensorPowerHistory alpha attempts),
      tensorPowerHistoryAll predicate attempts history = true ↔
        ∀ trial : Fin attempts,
          predicate (tensorPowerHistoryAt alpha attempts history trial) = true := by
  intro attempts
  induction attempts with
  | zero =>
      intro history
      constructor
      · intro _ trial
        exact Fin.elim0 trial
      · intro _
        rfl
  | succ attempts ih =>
      rintro ⟨head, tail⟩
      change (predicate head && tensorPowerHistoryAll predicate attempts tail) = true ↔ _
      simp only [Bool.and_eq_true]
      rw [ih tail]
      constructor
      · rintro ⟨hhead, htail⟩ trial
        refine Fin.cases ?_ ?_ trial
        · exact hhead
        · intro tailTrial
          exact htail tailTrial
      · intro hall
        constructor
        · exact hall 0
        · intro tailTrial
          exact hall tailTrial.succ

/-- Failure of the recursive Boolean conjunction is witnessed by one actual
tensor coordinate. -/
theorem tensorPowerHistoryAll_ne_true_iff_exists {alpha : Type*}
    (predicate : alpha -> Bool) (attempts : Nat)
    (history : tensorPowerHistory alpha attempts) :
    tensorPowerHistoryAll predicate attempts history ≠ true ↔
      ∃ trial : Fin attempts,
        predicate (tensorPowerHistoryAt alpha attempts history trial) ≠ true := by
  constructor
  · intro hfailure
    by_contra hnoWitness
    apply hfailure
    apply (tensorPowerHistoryAll_eq_true_iff predicate attempts history).2
    intro trial
    by_contra htrial
    exact hnoWitness ⟨trial, htrial⟩
  · rintro ⟨trial, htrial⟩ hall
    exact htrial
      ((tensorPowerHistoryAll_eq_true_iff predicate attempts history).1 hall trial)

/-- Boolean conjunction over every leaf of a recursively nested tensor history. -/
def nestedTensorHistoryAll {alpha : Type*} (predicate : alpha -> Bool)
    (branches : Nat) : (depth : Nat) -> nestedTensorHistory alpha branches depth -> Bool
  | 0, outcome => predicate outcome
  | depth + 1, history =>
      nestedTensorHistoryAll
        (fun layer => tensorPowerHistoryAll predicate branches layer)
        branches depth history

/-- The nested Boolean conjunction holds exactly when its predicate holds at
every leaf selected by an actual nested tensor path. -/
theorem nestedTensorHistoryAll_eq_true_iff {alpha : Type*}
    (predicate : alpha -> Bool) (branches : Nat) :
    ∀ (depth : Nat) (history : nestedTensorHistory alpha branches depth),
      nestedTensorHistoryAll predicate branches depth history = true ↔
        ∀ path : nestedTensorPath branches depth,
          predicate
            (nestedTensorHistoryAt alpha branches depth history path) = true := by
  intro depth
  induction depth generalizing alpha predicate with
  | zero =>
      intro history
      constructor
      · intro h path
        exact h
      · intro hall
        exact hall PUnit.unit
  | succ depth ih =>
      intro history
      constructor
      · intro h path
        have hprefix :
            ∀ pathPrefix : nestedTensorPath branches depth,
              tensorPowerHistoryAll predicate branches
                  (nestedTensorHistoryAt (tensorPowerHistory alpha branches)
                    branches depth history pathPrefix) = true :=
          (ih
            (alpha := tensorPowerHistory alpha branches)
            (predicate := fun layer =>
              tensorPowerHistoryAll predicate branches layer)
            history).1 (by simpa [nestedTensorHistoryAll] using h)
        have hleaf :=
          (tensorPowerHistoryAll_eq_true_iff predicate branches
            (nestedTensorHistoryAt (tensorPowerHistory alpha branches)
              branches depth history path.1)).1
            (hprefix path.1) path.2
        simpa [nestedTensorHistoryAt] using hleaf
      · intro hall
        have hprefix :
            ∀ pathPrefix : nestedTensorPath branches depth,
              tensorPowerHistoryAll predicate branches
                  (nestedTensorHistoryAt (tensorPowerHistory alpha branches)
                    branches depth history pathPrefix) = true := by
          intro pathPrefix
          apply (tensorPowerHistoryAll_eq_true_iff predicate branches _).2
          intro trial
          simpa [nestedTensorHistoryAt] using hall (pathPrefix, trial)
        have h :=
          (ih
            (alpha := tensorPowerHistory alpha branches)
            (predicate := fun layer =>
              tensorPowerHistoryAll predicate branches layer)
            history).2 hprefix
        simpa [nestedTensorHistoryAll] using h

/-- Failure of the nested Boolean conjunction is witnessed by one actual leaf
path. -/
theorem nestedTensorHistoryAll_ne_true_iff_exists {alpha : Type*}
    (predicate : alpha -> Bool) (branches depth : Nat)
    (history : nestedTensorHistory alpha branches depth) :
    nestedTensorHistoryAll predicate branches depth history ≠ true ↔
      ∃ path : nestedTensorPath branches depth,
        predicate (nestedTensorHistoryAt alpha branches depth history path) ≠ true := by
  constructor
  · intro hfailure
    by_contra hnoWitness
    apply hfailure
    apply (nestedTensorHistoryAll_eq_true_iff
      predicate branches depth history).2
    intro path
    by_contra hpath
    exact hnoWitness ⟨path, hpath⟩
  · rintro ⟨path, hpath⟩ hall
    exact hpath
      ((nestedTensorHistoryAll_eq_true_iff
        predicate branches depth history).1 hall path)

/-- One actual decoded pool routed successfully exactly when its visible
history contains the requested number of accepted decoded trials. -/
def decodedRetryPoolOutcomeEnough (attempts required : Nat)
    (outcome : Sigma fun _ : tensorPowerHistory DistillationOutcome attempts => PUnit) : Bool :=
  decide (required <=
    (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts outcome.1).card)

/-- Every next-stage pool on one routed logical path has enough accepted trials. -/
def decodedRetryPoolSuccessorStageRoutingGood
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (outcome : decodedRetryPoolSuccessorStageOutcome m w z q stage hstage) : Bool :=
  tensorPowerHistoryAll
    (decodedRetryPoolOutcomeEnough
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
    (logicalOutputCount m w) outcome.2

/-- Successful routing through a bounded natural stage of the physical chain. -/
def decodedRetryPoolProtocolSuccessfulRoutingAux
    (m w z q : Nat) : (stage : Nat) -> (hstage : stage < z) ->
      decodedRetryPoolProtocolOutcomeAux m w z q stage hstage -> Bool
  | 0, hzero, outcome =>
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hzero⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hzero⟩) outcome
  | stage + 1, hstage, outcome =>
      let previous : Fin z := ⟨stage, by omega⟩
      decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) outcome.1 &&
        nestedTensorHistoryAll
          (decodedRetryPoolSuccessorStageRoutingGood
            m w z q previous hstage)
          (logicalOutputCount m w) stage outcome.2

@[simp] theorem decodedRetryPoolProtocolSuccessfulRoutingAux_zero
    (m w z q : Nat) (hz : 0 < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q 0 hz) :
    decodedRetryPoolProtocolSuccessfulRoutingAux m w z q 0 hz outcome =
      decodedRetryPoolOutcomeEnough
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) outcome :=
  rfl

@[simp] theorem decodedRetryPoolProtocolSuccessfulRoutingAux_succ
    (m w z q stage : Nat) (hstage : stage + 1 < z)
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage) :
    decodedRetryPoolProtocolSuccessfulRoutingAux
        m w z q (stage + 1) hstage outcome =
      (decodedRetryPoolProtocolSuccessfulRoutingAux
          m w z q stage (by omega) outcome.1 &&
        nestedTensorHistoryAll
          (decodedRetryPoolSuccessorStageRoutingGood
            m w z q ⟨stage, by omega⟩ hstage)
          (logicalOutputCount m w) stage outcome.2) :=
  rfl

/-- The global successful-routing event of the complete positive-depth
physical protocol. -/
def decodedRetryPoolPhysicalProtocolSuccessfulRouting
    (m w z q : Nat) (hz : 0 < z)
    (outcome : decodedRetryPoolPhysicalProtocolOutcome m w z q hz) : Bool :=
  decodedRetryPoolProtocolSuccessfulRoutingAux
    m w z q (z - 1) (by omega) outcome

/-- The actual complete physical instrument with only its visible histories
coarsened to successful or rejected routing. -/
noncomputable def decodedRetryPoolPhysicalProtocolBinaryInstrument
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :=
  (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz).binaryCoarsen
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)

/-- Binary coarsening retains the exact complete physical Kraus family. -/
theorem decodedRetryPoolPhysicalProtocolBinaryInstrument_complete
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) :
    (decodedRetryPoolPhysicalProtocolBinaryInstrument
      h hdegree z q hz).kraus.Complete :=
  binaryCoarsen_complete
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz)

/-- The global physical success probability is the accepted Born mass of the
coarsened actual instrument. -/
noncomputable def decodedRetryPoolPhysicalProtocolSuccessMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) : Real :=
  (decodedRetryPoolPhysicalProtocolBinaryInstrument
    h hdegree z q hz).bornWeight .accepted rho

/-- The global success mass is exactly the finite sum of original physical
Born weights whose visible histories satisfy all routing requirements. -/
theorem decodedRetryPoolPhysicalProtocolSuccessMass_eq_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho =
      ∑ outcome ∈ Finset.univ.filter
          (fun outcome =>
            decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz outcome),
        (decodedRetryPoolPhysicalProtocolInstrument
          h hdegree z q hz).bornWeight outcome rho := by
  exact binaryCoarsen_bornWeight_accepted
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz) rho

theorem decodedRetryPoolPhysicalProtocolSuccessMass_nonneg
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    0 <= decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho :=
  (decodedRetryPoolPhysicalProtocolBinaryInstrument
    h hdegree z q hz).bornWeight_nonneg .accepted rho

theorem decodedRetryPoolPhysicalProtocolSuccessMass_le_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolPhysicalProtocolSuccessMass h hdegree z q hz rho <= 1 :=
  binaryCoarsen_accepted_le_one
    (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
    (decodedRetryPoolPhysicalProtocolSuccessfulRouting m w z q hz)
    (decodedRetryPoolPhysicalProtocolInstrument_complete h hdegree z q hz) rho

end HH18Parameterized
end Distillation
end QEC

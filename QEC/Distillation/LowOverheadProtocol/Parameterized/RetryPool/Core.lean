import QEC.Distillation.LowOverheadProtocol.Parameterized.DecodedInstrument
import QEC.Semantics.Instruments.TensorPower.BornMass
/-!
# Parameterized HH18 decoded retry pool

This internal API pools finitely many actual decoded HH18 blocks.  It retains
their finite observed histories, selects accepted decoded logical registers,
and uses an explicit physical replacement state only on shortage histories.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators

attribute [local instance 100] Fintype.ofFinite

local instance instDecodedRetryPoolClassicalDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A decoded trial contributes to selection exactly when its actual coarse
postselection outcome is accepted. -/
def decodedRetryPoolAccepts (outcome : DistillationOutcome) : Prop :=
  outcome = .accepted

instance instDecodedRetryPoolAcceptsDecidable : DecidablePred decodedRetryPoolAccepts := by
  intro outcome
  unfold decodedRetryPoolAccepts
  infer_instance

/-- The explicit all-zero logical-register vector used only for a finite
shortage replacement state. -/
noncomputable def decodedRetryPoolShortageVector (m w required : Nat) :
    QubitRegister (Fin required × LogicalSite m w) :=
  EuclideanSpace.basisFun (Bitstring (Fin required × LogicalSite m w)) Complex
    (fun _ => 0)

theorem decodedRetryPoolShortageVector_inner_self (m w required : Nat) :
    inner Complex (decodedRetryPoolShortageVector m w required)
      (decodedRetryPoolShortageVector m w required) = 1 := by
  simp [decodedRetryPoolShortageVector]

private theorem decodedRetryPoolShortageVector_normSq (m w required : Nat) :
    ‖decodedRetryPoolShortageVector m w required‖ ^ 2 = 1 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex),
    decodedRetryPoolShortageVector_inner_self]
  norm_num

/-- The physical density prepared only when a finite accepted-history
selection is unavailable. -/
noncomputable def decodedRetryPoolShortageState (m w required : Nat) :
    DensityOperator (QubitRegister (Fin required × LogicalSite m w)) :=
  DensityOperator.pureDensity (decodedRetryPoolShortageVector m w required)
    (decodedRetryPoolShortageVector_normSq m w required)

/-- The literal dependent raw index of the retry pool: an actual decoded raw
history followed by the selected or replacement channel's chosen Kraus index. -/
abbrev decodedRetryPoolRawIndex {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat) : Type :=
  Sigma fun firstIndex : tensorPowerHistory (decodedRawIndex h hdegree) attempts =>
    Fin ((tensorPowerHistoryConditionedChannel decodedRetryPoolAccepts attempts
      (((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex)
      required (LogicalSite m w)
      (decodedRetryPoolShortageState m w required)).chosenKrausCount)

/-- The actual finite decoded retry pool.  Its output is exactly the selected
logical register `QubitRegister (Fin required × LogicalSite m w)`. -/
noncomputable def decodedRetryPoolInstrument {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat) :
    FiniteInstrument (decodedRetryPoolRawIndex h hdegree attempts required)
      (Sigma fun _ : tensorPowerHistory DistillationOutcome attempts => PUnit)
      (tensorPowerCarrier (PhysicalRegister m w) attempts)
      (QubitRegister (Fin required × LogicalSite m w)) :=
  tensorPowerHistoryConditionedInstrument (decodedInstrument h hdegree)
    decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required)

/-- The pool's visible outcome retains the actual decoded observed history and
only appends the terminal unit observation of the total selection channel. -/
theorem decodedRetryPoolInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (firstIndex : tensorPowerHistory (decodedRawIndex h hdegree) attempts)
    (secondIndex : Fin ((tensorPowerHistoryConditionedChannel
      decodedRetryPoolAccepts attempts
      (((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex)
      required (LogicalSite m w)
      (decodedRetryPoolShortageState m w required)).chosenKrausCount)) :
    (decodedRetryPoolInstrument h hdegree attempts required).observe
      ⟨firstIndex, secondIndex⟩ =
        ⟨((decodedInstrument h hdegree).tensorPower attempts).observe firstIndex,
          PUnit.unit⟩ := by
  exact tensorPowerHistoryConditionedInstrument_observe
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required) firstIndex secondIndex

/-- Completeness of the actual retry-pool Kraus family. -/
theorem decodedRetryPoolInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat) :
    (decodedRetryPoolInstrument h hdegree attempts required).kraus.Complete :=
  tensorPowerHistoryConditionedInstrument_complete (decodedInstrument h hdegree)
    decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required)
    (decodedInstrument_complete h hdegree)

/-- The total selected-or-replacement stage preserves every actual decoded
observed-history Born mass. -/
theorem decodedRetryPoolInstrument_bornWeight_eq_tensorPower {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (history : tensorPowerHistory DistillationOutcome attempts)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
        ⟨history, PUnit.unit⟩ rho =
      ((decodedInstrument h hdegree).tensorPower attempts).bornWeight history rho := by
  exact tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required
    (decodedRetryPoolShortageState m w required) history rho

/-- The finite pool mass of observed histories with enough actual accepted
decoded trials. -/
noncomputable def decodedRetryPoolEnoughMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) : ℝ :=
  ∑ history ∈ Finset.univ.filter
      (fun history => required ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card),
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
      ⟨history, PUnit.unit⟩ rho

/-- The finite pool mass of observed histories short of the requested number
of actual accepted decoded trials. -/
noncomputable def decodedRetryPoolShortageMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) : ℝ :=
  ∑ history ∈ Finset.univ.filter
      (fun history =>
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts attempts history).card < required),
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
      ⟨history, PUnit.unit⟩ rho

/-- The enough-event mass is nonnegative because it is a finite sum of
physical Born weights. -/
theorem decodedRetryPoolEnoughMass_nonneg {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    0 ≤ decodedRetryPoolEnoughMass h hdegree attempts required rho := by
  unfold decodedRetryPoolEnoughMass
  exact Finset.sum_nonneg fun history _ =>
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight_nonneg
      ⟨history, PUnit.unit⟩ rho

/-- The shortage-event mass is nonnegative because it is a finite sum of
physical Born weights. -/
theorem decodedRetryPoolShortageMass_nonneg {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    0 ≤ decodedRetryPoolShortageMass h hdegree attempts required rho := by
  unfold decodedRetryPoolShortageMass
  exact Finset.sum_nonneg fun history _ =>
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight_nonneg
      ⟨history, PUnit.unit⟩ rho

/-- The pool's enough and shortage observed-history masses partition the
complete physical Born mass. -/
theorem decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    decodedRetryPoolEnoughMass h hdegree attempts required rho +
        decodedRetryPoolShortageMass h hdegree attempts required rho = 1 := by
  unfold decodedRetryPoolEnoughMass decodedRetryPoolShortageMass
  simp_rw [decodedRetryPoolInstrument_bornWeight_eq_tensorPower]
  exact tensorPowerEnoughMass_add_tensorPowerShortageMass
    (decodedInstrument h hdegree) decodedRetryPoolAccepts attempts required rho
    (decodedInstrument_complete h hdegree)

/-- The enough-event mass is bounded above by the complete physical Born
mass. -/
theorem decodedRetryPoolEnoughMass_le_one {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (rho : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) attempts)) :
    decodedRetryPoolEnoughMass h hdegree attempts required rho ≤ 1 := by
  have hpartition := decodedRetryPoolEnoughMass_add_decodedRetryPoolShortageMass
    h hdegree attempts required rho
  have hshortage := decodedRetryPoolShortageMass_nonneg
    h hdegree attempts required rho
  linarith

/-- On actual tensorized measured-resource blocks, every pooled observed
history has the recursively factored observed Born mass. -/
theorem decodedRetryPoolInstrument_bornWeight_tensorPowerProductInput {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (attempts required : Nat)
    (inputs : ResourceInput (physicalInputCount m w) QubitSpace)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome attempts) :
    (decodedRetryPoolInstrument h hdegree attempts required).bornWeight
        ⟨history, PUnit.unit⟩
          (tensorPowerProductInput (prepareMeasuredResources m w inputs) rhoUnit attempts) =
      tensorPowerBornProduct (decodedInstrument h hdegree)
        (prepareMeasuredResources m w inputs) attempts history := by
  rw [decodedRetryPoolInstrument_bornWeight_eq_tensorPower]
  exact bornWeight_tensorPower (decodedInstrument h hdegree)
    (prepareMeasuredResources m w inputs) rhoUnit attempts history

/-- The accepted observed history of one noisy physical block has exactly the
existing parameterized accepted Bernoulli mass. -/
theorem decodedRetryPoolInstrument_noisy_one_accepted_bornWeight_eq_acceptedBernoulliMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolInstrument h hdegree 1 1).bornWeight
        ⟨(.accepted, PUnit.unit), PUnit.unit⟩
          (tensorPowerProductInput
            (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit 1) =
      acceptedBernoulliMass w r m epsilon := by
  erw [decodedRetryPoolInstrument_bornWeight_eq_tensorPower]
  erw [bornWeight_tensorPower (decodedInstrument h hdegree)
    (prepareMeasuredResources m w (noisyResources m w epsilon)) rhoUnit 1
    (.accepted, PUnit.unit)]
  simp only [tensorPowerBornProduct]
  rw [decodedInstrument_bornWeight_noisyResources_accepted_eq_acceptedBernoulliMass]
  norm_num

end HH18Parameterized
end Distillation
end QEC

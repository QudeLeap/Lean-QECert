import QEC.Semantics.Instruments.TensorPower.Basis
import QEC.Semantics.Core.Subsystem
/-!
# Selected coordinate subsystems of finite tensor powers

This module turns an accepted finite-trial selector into its literal selected
coordinate subsystem.  It preserves the recursive tensor-power carrier until
the basis transport, then uses the concrete finite-subsystem partial trace.
It does not assign probabilities, replace a shortage branch, or interpret the
selected coordinates as a protocol output.
-/

universe u v

namespace QEC
namespace Semantics

noncomputable section

namespace FiniteInstrument

/-- Embed a requested selected slot and local port into the actual trial and
port coordinate selected by the accepted-history order embedding. -/
noncomputable def tensorPowerSelectedCoordinateEmbedding
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (Fin required × ι) ↪ (Fin attempts × ι) := by
  refine
    { toFun := fun coordinate =>
        (tensorPowerAcceptedSelector accepts attempts history required hrequired coordinate.1,
          coordinate.2)
      inj' := ?_ }
  rintro ⟨first, firstPort⟩ ⟨second, secondPort⟩ heq
  have htrials :
      tensorPowerAcceptedSelector accepts attempts history required hrequired first =
        tensorPowerAcceptedSelector accepts attempts history required hrequired second :=
    congrArg Prod.fst heq
  have hports : firstPort = secondPort :=
    congrArg Prod.snd heq
  have hslots : first = second :=
    (tensorPowerAcceptedSelector accepts attempts history required hrequired).injective htrials
  exact Prod.ext hslots hports

/-- The exact finite subsystem image of the requested selected slots and
local ports in the flattened trial/register coordinate type. -/
noncomputable def tensorPowerSelectedSubsystem
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    FiniteSubsystem (Fin attempts × ι) where
  selected :=
    (Finset.univ : Finset (Fin required × ι)).map
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι)

/-- Membership in the selected subsystem is exactly membership in the image
of the selected-slot coordinate embedding. -/
theorem mem_tensorPowerSelectedSubsystem_iff
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (coordinate : Fin attempts × ι) :
    coordinate ∈
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selected ↔
      ∃ selected : Fin required × ι,
        tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
          selected = coordinate := by
  change coordinate ∈ (Finset.univ : Finset (Fin required × ι)).map
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι) ↔ _
  constructor
  · intro hcoordinate
    rcases Finset.mem_map.mp hcoordinate with ⟨selected, -, hselected⟩
    exact ⟨selected, hselected⟩
  · rintro ⟨selected, hselected⟩
    exact Finset.mem_map.mpr ⟨selected, Finset.mem_univ _, hselected⟩

/-- Every requested selected slot/port has its concrete coordinate in the
selected finite subsystem. -/
theorem tensorPowerSelectedCoordinateEmbedding_mem
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Fin required × ι) :
    tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      selected ∈
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selected :=
  (mem_tensorPowerSelectedSubsystem_iff accepts attempts history required hrequired ι
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      selected)).mpr ⟨selected, rfl⟩

/-- The requested selected coordinates are explicitly equivalent to the
subtype of actual flattened coordinates in the finite subsystem image. -/
noncomputable def tensorPowerSelectedCoordinateEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    (Fin required × ι) ≃
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates := by
  apply Equiv.ofBijective
    (fun selected =>
      ⟨tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
          selected,
        tensorPowerSelectedCoordinateEmbedding_mem accepts attempts history required hrequired ι
          selected⟩)
  constructor
  · intro first second heq
    apply (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι).injective
    exact Subtype.ext_iff.mp heq
  · intro coordinate
    rcases (mem_tensorPowerSelectedSubsystem_iff accepts attempts history required hrequired ι
      coordinate.1).mp coordinate.2 with ⟨selected, hselected⟩
    refine ⟨selected, ?_⟩
    apply Subtype.ext
    exact hselected

/-- The selected-coordinate equivalence has the actual selector image as its
underlying flattened coordinate. -/
@[simp] theorem tensorPowerSelectedCoordinateEquiv_apply_val
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Fin required × ι) :
    ((tensorPowerSelectedCoordinateEquiv accepts attempts history required hrequired ι selected :
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates) :
      Fin attempts × ι) =
      tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι selected :=
  rfl

/-- The trial component of a selected coordinate is the compiled accepted
selector at its requested slot. -/
@[simp] theorem tensorPowerSelectedCoordinateEmbedding_fst
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (selected : Fin required × ι) :
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι selected).1 =
      tensorPowerAcceptedSelector accepts attempts history required hrequired selected.1 :=
  rfl

/-- Distinct requested selected slots map to distinct actual trial indices,
at every common local port. -/
theorem tensorPowerSelectedCoordinateEmbedding_trials_ne_of_ne
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {first second : Fin required} (hne : first ≠ second) (port : ι) :
    (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
      (first, port)).1 ≠
      (tensorPowerSelectedCoordinateEmbedding accepts attempts history required hrequired ι
        (second, port)).1 := by
  change tensorPowerAcceptedSelector accepts attempts history required hrequired first ≠
    tensorPowerAcceptedSelector accepts attempts history required hrequired second
  exact tensorPowerAcceptedSelector_ne_of_ne accepts attempts history required hrequired hne

/-- Reindex selected-subsystem bitstrings by the explicit selected-slot/
actual-coordinate equivalence. -/
noncomputable def tensorPowerSelectedBitstringEquiv
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates ≃
      Qubit.Bitstring (Fin required × ι) where
  toFun := fun bits selected =>
    bits (tensorPowerSelectedCoordinateEquiv accepts attempts history required hrequired ι selected)
  invFun := fun bits coordinate =>
    bits ((tensorPowerSelectedCoordinateEquiv accepts attempts history required hrequired ι).symm
      coordinate)
  left_inv := by
    intro bits
    funext coordinate
    simp
  right_inv := by
    intro bits
    funext selected
    simp

/-- The basis-preserving unitary reindexing from the actual selected-coordinate
register to the requested selected-slot register. -/
noncomputable def tensorPowerSelectedRegisterReindex
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    UnitaryTransport
      (Qubit.QubitRegister
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates)
      (Qubit.QubitRegister (Fin required × ι)) := by
  let sourceBasis :=
    EuclideanSpace.basisFun
      (Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates)
      Complex
  let targetBasis := EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
  let U := sourceBasis.equiv targetBasis
    (tensorPowerSelectedBitstringEquiv accepts attempts history required hrequired ι)
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The selected-register reindexing sends each actual selected-coordinate
computational basis vector to its requested selected-slot basis vector. -/
@[simp] theorem tensorPowerSelectedRegisterReindex_apply_basis
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (bits : Qubit.Bitstring
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates) :
    tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι
      (EuclideanSpace.basisFun (Qubit.Bitstring
        (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).SelectedCoordinates)
        Complex bits) =
      EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
        (tensorPowerSelectedBitstringEquiv accepts attempts history required hrequired ι bits) := by
  dsimp [tensorPowerSelectedRegisterReindex]
  rw [OrthonormalBasis.equiv_apply_basis]

/-- The actual CPTP selected-subsystem channel: flatten the recursive carrier,
partially trace to the selector image, then reindex its selected register. -/
noncomputable def tensorPowerSelectedPartialTraceChannel
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    QuantumChannel (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin required × ι)) :=
  QuantumChannel.comp
    (QuantumChannel.unitaryConj
      (tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι))
    (QuantumChannel.comp
      (tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selectedPartialTraceFromRegister
      (QuantumChannel.unitaryConj (tensorPowerQubitRegisterTransport ι attempts)))

/-- The selected-subsystem channel acts by the stated flatten, partial-trace,
and reindex composition on every operator. -/
@[simp] theorem tensorPowerSelectedPartialTraceChannel_apply
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)) :
    tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι A =
      (tensorPowerSelectedRegisterReindex accepts attempts history required hrequired ι).conjOperator
        ((tensorPowerSelectedSubsystem accepts attempts history required hrequired ι).selectedPartialTraceFromRegister
          ((tensorPowerQubitRegisterTransport ι attempts).conjOperator A)) :=
  rfl

end FiniteInstrument

end
end Semantics
end QEC

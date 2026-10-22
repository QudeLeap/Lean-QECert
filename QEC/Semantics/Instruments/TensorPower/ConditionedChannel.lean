import QEC.Semantics.Instruments.Selection.SelectedSubsystem
import QEC.Semantics.Channels.Instrument
import QEC.Semantics.Dynamics.ThermalEncoding
/-!
# Total history-conditioned tensor-power channels

This internal API turns each observed finite tensor-power history into a
total quantum channel.  Histories with enough accepted trials use the literal
selected-subsystem partial trace.  A shortage history uses a separately
supplied replacement density only to make the channel total.
-/

universe v w

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators ComplexOrder TensorProduct

noncomputable section

namespace FiniteInstrument

/-- The concrete commutation unitary used to discard the old input factor
after preparation on the right. -/
noncomputable def fixedDensityReplacementSwap (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    UnitaryTransport (CompositeSystem H K) (CompositeSystem K H) := by
  let U := TensorProduct.commIsometry Complex H K
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

/-- The replacement commutation unitary exchanges pure tensor factors. -/
@[simp] theorem fixedDensityReplacementSwap_apply_tmul (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) (k : K) :
    fixedDensityReplacementSwap H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl

/-- Physically replace an arbitrary finite input by `sigma`: prepare `sigma`
on a right factor, commute the tensor factors, and trace out the old input
factor. -/
noncomputable def fixedDensityReplacementChannel (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) : QuantumChannel H K :=
  QuantumChannel.comp (partialTraceRightRaw_cptp K H)
    (QuantumChannel.comp
      (QuantumChannel.unitaryConj (fixedDensityReplacementSwap H K))
      (ThermalEncoding.prepareRight H K sigma))

/-- On a rank-one input, the physical replacement channel retains only the
input trace coefficient and prepares the supplied density operator. -/
theorem fixedDensityReplacementChannel_apply_rankOne (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (h g : H) :
    fixedDensityReplacementChannel H K sigma
      (InnerProductSpace.rankOne Complex h g).toLinearMap =
        (inner Complex g h) • sigma.toOperator := by
  classical
  unfold fixedDensityReplacementChannel
  rw [QuantumChannel.comp_apply, QuantumChannel.comp_apply]
  rw [ThermalEncoding.prepareRight_apply_rankOne]
  simp only [map_sum]
  simp only [QuantumChannel.unitaryConj_apply, QuditSubsystem.conjOperator_rankOne,
    fixedDensityReplacementSwap_apply_tmul,
    partialTraceRightRaw_cptp_toLinearMap,
    QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  rw [← Finset.smul_sum]
  simpa only [ThermalEncoding.spectralEnsembleVector] using
    congrArg (fun A : Operator K => (inner Complex g h) • A)
      sigma.spectralDecomposition.symm

/-- The physical replacement channel sends every normalized density input to
the supplied normalized replacement density. -/
theorem fixedDensityReplacementChannel_mapDensity (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (rho : DensityOperator H) :
    (fixedDensityReplacementChannel H K sigma).mapDensity rho = sigma := by
  classical
  apply DensityOperator.ext_toOperator
  change fixedDensityReplacementChannel H K sigma rho.toOperator = sigma.toOperator
  have hrho : rho.toOperator =
      ∑ i : Fin (Module.finrank Complex H),
        (InnerProductSpace.rankOne Complex
          (ThermalEncoding.spectralEnsembleVector rho i)
          (ThermalEncoding.spectralEnsembleVector rho i)).toLinearMap := by
    simpa only [ThermalEncoding.spectralEnsembleVector] using rho.spectralDecomposition
  rw [hrho, map_sum]
  calc
    (∑ i : Fin (Module.finrank Complex H),
        fixedDensityReplacementChannel H K sigma
          (InnerProductSpace.rankOne Complex
            (ThermalEncoding.spectralEnsembleVector rho i)
            (ThermalEncoding.spectralEnsembleVector rho i)).toLinearMap) =
        ∑ i : Fin (Module.finrank Complex H),
          inner Complex (ThermalEncoding.spectralEnsembleVector rho i)
            (ThermalEncoding.spectralEnsembleVector rho i) • sigma.toOperator := by
          apply Finset.sum_congr rfl
          intro i _
          exact fixedDensityReplacementChannel_apply_rankOne H K sigma _ _
    _ = (∑ i : Fin (Module.finrank Complex H),
          inner Complex (ThermalEncoding.spectralEnsembleVector rho i)
            (ThermalEncoding.spectralEnsembleVector rho i)) • sigma.toOperator := by
          rw [Finset.sum_smul]
    _ = sigma.toOperator := by
          rw [ThermalEncoding.spectralEnsembleVector_sum_inner]
          simp

/-- Select the literal accepted subsystem when the observed history contains
enough accepted trials; otherwise use `shortageState` only as a totality
placeholder. -/
noncomputable def tensorPowerHistoryConditionedChannel
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    QuantumChannel (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin required × ι)) :=
  if hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card then
    tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι
  else
    fixedDensityReplacementChannel
      (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
      (Qubit.QubitRegister (Fin required × ι)) shortageState

/-- An enough-accepted history reduces definitionally to its literal selected
subsystem partial-trace channel. -/
theorem tensorPowerHistoryConditionedChannel_of_enough
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat)
    (hrequired : required ≤ (tensorPowerAcceptedIndices accepts attempts history).card)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required hrequired ι := by
  simp [tensorPowerHistoryConditionedChannel, hrequired]

/-- A shortage history reduces to the physical replacement channel, rather
than being interpreted as an accepted selected subsystem. -/
theorem tensorPowerHistoryConditionedChannel_of_shortage
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat)
    (hshort : (tensorPowerAcceptedIndices accepts attempts history).card < required)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState =
      fixedDensityReplacementChannel
        (tensorPowerCarrier (Qubit.QubitRegister ι) attempts)
        (Qubit.QubitRegister (Fin required × ι)) shortageState := by
  simp [tensorPowerHistoryConditionedChannel, Nat.not_le_of_lt hshort]

/-- The finite shortage predicate is exactly the absence of a full injective
selection of accepted trials. -/
theorem tensorPowerHistoryConditionedChannel_shortage_iff_no_full_selection
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (history : tensorPowerHistory α attempts) (required : Nat) :
    (tensorPowerAcceptedIndices accepts attempts history).card < required ↔
      ¬ ∃ selection : Fin required → Fin attempts,
        Function.Injective selection ∧
          ∀ slot, selection slot ∈ tensorPowerAcceptedIndices accepts attempts history :=
  tensorPowerAccepted_shortage_iff_no_full_selection accepts attempts history required

/-- Bind each actual observed tensor-power history to its total conditioned
channel.  The second raw index is a dependent sigma fibre over the first raw
history's observed outcome. -/
noncomputable def tensorPowerHistoryConditionedInstrument
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι))) :
    FiniteInstrument
      (Sigma fun firstIndex : tensorPowerHistory κ attempts =>
        Fin ((tensorPowerHistoryConditionedChannel accepts attempts
          ((I.tensorPower attempts).observe firstIndex) required ι shortageState).chosenKrausCount))
      (Sigma fun _ : tensorPowerHistory Ω attempts => PUnit)
      (tensorPowerCarrier H attempts)
      (Qubit.QubitRegister (Fin required × ι)) :=
  (I.tensorPower attempts).bindDependent
    (fun history =>
      QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))

/-- The total instrument's visible outcome records the actual first-stage
observed history and the unit observation of the selected second channel. -/
theorem tensorPowerHistoryConditionedInstrument_observe
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (firstIndex : tensorPowerHistory κ attempts)
    (secondIndex : Fin
      ((tensorPowerHistoryConditionedChannel accepts attempts
        ((I.tensorPower attempts).observe firstIndex) required ι shortageState).chosenKrausCount)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).observe
      ⟨firstIndex, secondIndex⟩ =
        ⟨(I.tensorPower attempts).observe firstIndex, PUnit.unit⟩ := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun history =>
        QuantumChannel.toFiniteInstrument
          (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))).observe
        ⟨firstIndex, secondIndex⟩ =
      ⟨(I.tensorPower attempts).observe firstIndex, PUnit.unit⟩
  exact FiniteInstrument.bindDependent_observe
    (I.tensorPower attempts)
    (fun history =>
      QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))
    firstIndex secondIndex

/-- Completeness of the total history-conditioned instrument follows from
the actual tensor-power completeness and the chosen finite Kraus family of
each conditioned channel. -/
theorem tensorPowerHistoryConditionedInstrument_complete
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (hI : I.kraus.Complete) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).kraus.Complete := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun history =>
        QuantumChannel.toFiniteInstrument
          (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))).kraus.Complete
  exact FiniteInstrument.bindDependent_complete
    (I.tensorPower attempts)
    (fun history =>
      QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))
    (I.tensorPower_complete hI attempts)
    (fun history =>
      QuantumChannel.toFiniteInstrument_complete
        (tensorPowerHistoryConditionedChannel accepts attempts history required ι shortageState))

/-- The complete total instrument has normalized observable Born mass for
every density input. -/
theorem tensorPowerHistoryConditionedInstrument_sum_bornWeight_eq_one
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (hI : I.kraus.Complete)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    ∑ outcome,
      (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).bornWeight
        outcome rho = 1 :=
  FiniteInstrument.sum_bornWeight_eq_one
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState)
    (tensorPowerHistoryConditionedInstrument_complete I accepts attempts required shortageState hI)
    rho

end FiniteInstrument

end
end Semantics
end QEC

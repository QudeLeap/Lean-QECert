import QEC.Semantics.Instruments.TensorPower.BranchOperator
/-!
# Branch operators of history-conditioned tensor powers

This layer connects the visible branch of the total selected-or-replacement
instrument to the actual tensor-power branch followed by its history-selected
physical channel.  Enough histories therefore use the literal selector; the
replacement branch remains confined to shortage histories.
-/

universe v w

namespace QEC
namespace Semantics

open Classical

noncomputable section

namespace FiniteInstrument

/-- The visible history branch of the total conditioned instrument is the
actual tensor-power branch sent through the channel chosen by that history. -/
theorem tensorPowerHistoryConditionedInstrument_branchOperator
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (A : Operator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩ A =
      tensorPowerHistoryConditionedChannel accepts attempts history required ι
        shortageState ((I.tensorPower attempts).branchOperator history A) := by
  change
    ((I.tensorPower attempts).bindDependent
      (fun observedHistory => QuantumChannel.toFiniteInstrument
        (tensorPowerHistoryConditionedChannel accepts attempts observedHistory
          required ι shortageState))).branchOperator
        ⟨history, PUnit.unit⟩ A = _
  rw [bindDependent_branchOperator_punit]
  exact QuantumChannel.toFiniteInstrument_inducedMap_apply
    (tensorPowerHistoryConditionedChannel accepts attempts history required ι
      shortageState) _

/-- On an enough-accepted visible history, the total instrument branch uses
the literal selected-subsystem channel and never the shortage replacement. -/
theorem tensorPowerHistoryConditionedInstrument_branchOperator_of_enough
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card)
    (A : Operator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩ A =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required
        hrequired ι ((I.tensorPower attempts).branchOperator history A) := by
  rw [tensorPowerHistoryConditionedInstrument_branchOperator]
  rw [tensorPowerHistoryConditionedChannel_of_enough]

/-- On a literal tensorized product input, an enough-history branch is the
actual selector applied to the recursively factored observed branch product. -/
theorem tensorPowerHistoryConditionedInstrument_branchOperator_productInput_of_enough
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
      [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (history : tensorPowerHistory Ω attempts)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts history).card) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required
        shortageState).branchOperator ⟨history, PUnit.unit⟩
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
      tensorPowerSelectedPartialTraceChannel accepts attempts history required
        hrequired ι
        (tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history) := by
  rw [tensorPowerHistoryConditionedInstrument_branchOperator_of_enough]
  rw [branchOperator_tensorPower_productInput]

end FiniteInstrument

end
end Semantics
end QEC

import QEC.Semantics.Instruments.TensorPower.BranchOperator
import QEC.Semantics.Instruments.Selection.SelectedSubsystemOperator
import QEC.Semantics.Instruments.Selection.SelectedTrialProduct
/-!
# Selected matrix entries of tensorized branch products

This layer combines the literal selected-subsystem matrix-entry formula with
the actual trial-wise branch-operator product.  It exposes the remaining
discarded-label sum without asserting independence or replacing any branch.
-/

universe u v

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

/-- A requested matrix entry of a selected tensorized branch is the sum of
the exact recursive branch-entry products over one discarded label. -/
theorem tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (branch : α → Operator (Qubit.QubitRegister ι))
    (unit : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          (tensorPowerBranchOperatorProduct branch unit attempts observedHistory)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        tensorPowerBranchOperatorMatrixEntryProduct
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
          branch unit attempts observedHistory
          ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
            required hrequired ι).symm (left, complement))
          ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts observedHistory
            required hrequired ι).symm (right, complement)) := by
  rw [tensorPowerSelectedPartialTraceChannel_matrixEntry]
  apply Finset.sum_congr rfl
  intro complement _
  rw [tensorPowerBranchOperatorProduct_matrixEntry]

/-- The same selected matrix entry, with every recursive branch entry exposed
as its actual finite product over trial indices. -/
theorem tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod
    {α : Type v} (accepts : α → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory α attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (branch : α → Operator (Qubit.QubitRegister ι))
    (unit : Operator (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          (tensorPowerBranchOperatorProduct branch unit attempts observedHistory)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex right)) =
      ∑ complement : Qubit.Bitstring
          (tensorPowerSelectedSubsystem accepts attempts observedHistory required
            hrequired ι).ComplementCoordinates,
        inner Complex
            (tensorPowerBasis
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) 0 PUnit.unit)
            (unit
              (tensorPowerBasis
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) 0 PUnit.unit)) *
          ∏ trial : Fin attempts,
            inner Complex
              (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
                (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
                  ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts
                    observedHistory required hrequired ι).symm (left, complement))
                  trial))
              (branch (tensorPowerHistoryAt α attempts observedHistory trial)
                (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
                  (tensorPowerHistoryAt (Qubit.Bitstring ι) attempts
                    ((tensorPowerSelectedHistoryBitstringEquiv accepts attempts
                      observedHistory required hrequired ι).symm (right, complement))
                    trial))) := by
  rw [tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry]
  apply Finset.sum_congr rfl
  intro complement _
  rw [tensorPowerBranchOperatorMatrixEntryProduct_eq_prod]

/-- The unique depth-zero matrix entry of any tensor-unit density is one. -/
theorem tensorPowerUnitDensity_matrixEntry_eq_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {β : Type v} [Fintype β]
    (basis : OrthonormalBasis β Complex H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    inner Complex (tensorPowerBasis basis 0 PUnit.unit)
        (rhoUnit.toOperator (tensorPowerBasis basis 0 PUnit.unit)) = 1 := by
  calc
    inner Complex (tensorPowerBasis basis 0 PUnit.unit)
        (rhoUnit.toOperator (tensorPowerBasis basis 0 PUnit.unit)) =
        ∑ index : PUnit,
          inner Complex (tensorPowerBasis basis 0 index)
            (rhoUnit.toOperator (tensorPowerBasis basis 0 index)) := by
      simp
    _ = LinearMap.trace Complex (tensorPowerCarrier H 0) rhoUnit.toOperator :=
      (LinearMap.trace_eq_sum_inner rhoUnit.toOperator
        (tensorPowerBasis basis 0)).symm
    _ = 1 := rhoUnit.trace_one

/-- On a literal tensor-product input, a selected branch matrix entry is the
product of the retained local branch entries and the Born weights of every
discarded actual trial.  This is a partial-trace identity, not an independence
assumption. -/
theorem tensorPowerSelectedPartialTraceChannel_productInputBranch_matrixEntry
    {κ Ω : Type v} [Fintype κ] [Fintype Ω]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts : Nat) (observedHistory : tensorPowerHistory Ω attempts)
    (required : Nat)
    (hrequired : required ≤
      (tensorPowerAcceptedIndices accepts attempts observedHistory).card)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (left right : Qubit.Bitstring (Fin required × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex left)
        (tensorPowerSelectedPartialTraceChannel accepts attempts observedHistory
          required hrequired ι
          ((I.tensorPower attempts).branchOperator observedHistory
            (tensorPowerProductInput rho rhoUnit attempts).toOperator)
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin required × ι)) Complex
            right)) =
      (∏ slot : Fin required,
        inner Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
            (fun port => left (slot, port)))
          (I.branchOperator
            (tensorPowerHistoryAt Ω attempts observedHistory
              (tensorPowerAcceptedSelector accepts attempts observedHistory
                required hrequired slot))
            rho.toOperator
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
              (fun port => right (slot, port))))) *
      ∏ trial : tensorPowerUnselectedTrial accepts attempts observedHistory
          required hrequired,
        (I.bornWeight
          (tensorPowerHistoryAt Ω attempts observedHistory trial.1) rho : Complex) := by
  rw [branchOperator_tensorPower_productInput]
  rw [tensorPowerSelectedPartialTraceChannel_branchProduct_matrixEntry_eq_sum_prod]
  rw [tensorPowerUnitDensity_matrixEntry_eq_one]
  simp only [one_mul]
  rw [tensorPower_sum_complement_prod_eq_selected_mul_unselected_sums accepts
    attempts observedHistory required hrequired ι
    (fun trial leftBits rightBits =>
      inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex leftBits)
        (I.branchOperator
          (tensorPowerHistoryAt Ω attempts observedHistory trial) rho.toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex rightBits)))
    left right]
  congr 1
  apply Finset.prod_congr rfl
  intro trial _
  exact branchOperator_matrixEntry_sum_eq_bornWeight
    (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex) I
    (tensorPowerHistoryAt Ω attempts observedHistory trial.1) rho

end FiniteInstrument

end
end Semantics
end QEC

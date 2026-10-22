import QEC.Semantics.Instruments.NestedTensor.MarginalBranchOperator
/-!
# Filtered operator-valued marginals of nested tensor-power instruments

This layer filters a recursively nested global history by a predicate at one
selected leaf.  Summing every sibling history and retaining that output leaf
gives exactly the sum of the selected local branches on the true unnormalized
input-leaf operator.  No branch is normalized and no sibling independence is
assumed.
-/

universe u v w

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/-- Filtering a nested global history by one leaf observation, then retaining
that output leaf, is the corresponding sum of local observed branches on the
true input-leaf operator. -/
theorem nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (branches depth : Nat) (A : Operator (nestedTensorCarrier H branches depth))
    (path : nestedTensorPath branches depth) :
    nestedTensorCoordinateOperator K branches depth path
        (∑ history : nestedTensorHistory Omega branches depth,
          if predicate
              (nestedTensorHistoryAt Omega branches depth history path) then
            (nestedTensorPower I branches depth).branchOperator history A
          else 0) =
      ∑ outcome : Omega,
        if predicate outcome then
          I.branchOperator outcome
            (nestedTensorCoordinateOperator H branches depth path A)
        else 0 := by
  have hregroup :
      (∑ history : nestedTensorHistory Omega branches depth,
          if predicate
              (nestedTensorHistoryAt Omega branches depth history path) then
            (nestedTensorPower I branches depth).branchOperator history A
          else 0) =
        ∑ outcome : Omega,
          if predicate outcome then
            ∑ history : nestedTensorHistory Omega branches depth,
              if nestedTensorHistoryAt Omega branches depth history path = outcome then
                (nestedTensorPower I branches depth).branchOperator history A
              else 0
          else 0 := by
    calc
      _ = ∑ history : nestedTensorHistory Omega branches depth,
          ∑ outcome : Omega,
            if predicate outcome ∧
                nestedTensorHistoryAt Omega branches depth history path = outcome then
              (nestedTensorPower I branches depth).branchOperator history A
            else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          rw [Fintype.sum_eq_single
            (nestedTensorHistoryAt Omega branches depth history path)]
          · simp
          · intro outcome hne
            simp [hne.symm]
      _ = ∑ outcome : Omega,
          ∑ history : nestedTensorHistory Omega branches depth,
            if predicate outcome ∧
                nestedTensorHistoryAt Omega branches depth history path = outcome then
              (nestedTensorPower I branches depth).branchOperator history A
            else 0 := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro outcome _
          by_cases houtcome : predicate outcome
          · simp [houtcome]
          · simp [houtcome]
  rw [hregroup, map_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases houtcome : predicate outcome
  · rw [if_pos houtcome, if_pos houtcome]
    exact nestedTensor_coordinateOperator_branchOperator_sum_eq
      I hI branches depth A path outcome
  · simp [houtcome]

end FiniteInstrument

end
end Semantics
end QEC

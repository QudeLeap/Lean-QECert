import QEC.Semantics.Instruments.TensorPower.MarginalBranchOperator
/-!
# Filtered operator-valued marginals of tensor-power instruments

This source-neutral layer sums all global histories whose observation at one
selected coordinate satisfies a finite predicate.  After tracing to that
output coordinate, the result is exactly the sum of the corresponding local
branch operators evaluated on the true unnormalized input marginal.  It does
not normalize a retained branch or condition on any sibling observation.
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

/-- Summing all global histories selected by a predicate on one coordinate,
then tracing to that output coordinate, is the corresponding sum of local
observed branches on the true input-coordinate operator. -/
theorem tensorPower_coordinateOperator_branchOperator_filter_sum_eq
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (attempts : Nat) (A : Operator (tensorPowerCarrier H attempts))
    (trial : Fin attempts) :
    tensorPowerCoordinateOperator attempts trial
        (∑ history : tensorPowerHistory Omega attempts,
          if predicate (tensorPowerHistoryAt Omega attempts history trial) then
            (I.tensorPower attempts).branchOperator history A
          else 0) =
      ∑ outcome : Omega,
        if predicate outcome then
          I.branchOperator outcome
            (tensorPowerCoordinateOperator attempts trial A)
        else 0 := by
  have hregroup :
      (∑ history : tensorPowerHistory Omega attempts,
          if predicate (tensorPowerHistoryAt Omega attempts history trial) then
            (I.tensorPower attempts).branchOperator history A
          else 0) =
        ∑ outcome : Omega,
          if predicate outcome then
            ∑ history : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts history trial = outcome then
                (I.tensorPower attempts).branchOperator history A
              else 0
          else 0 := by
    calc
      _ = ∑ history : tensorPowerHistory Omega attempts,
          ∑ outcome : Omega,
            if predicate outcome ∧
                tensorPowerHistoryAt Omega attempts history trial = outcome then
              (I.tensorPower attempts).branchOperator history A
            else 0 := by
          apply Finset.sum_congr rfl
          intro history _
          rw [Fintype.sum_eq_single
            (tensorPowerHistoryAt Omega attempts history trial)]
          · simp
          · intro outcome hne
            simp [hne.symm]
      _ = ∑ outcome : Omega,
          ∑ history : tensorPowerHistory Omega attempts,
            if predicate outcome ∧
                tensorPowerHistoryAt Omega attempts history trial = outcome then
              (I.tensorPower attempts).branchOperator history A
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
    exact tensorPower_coordinateOperator_branchOperator_sum_eq
      I hI attempts A trial outcome
  · simp [houtcome]

end FiniteInstrument

end
end Semantics
end QEC

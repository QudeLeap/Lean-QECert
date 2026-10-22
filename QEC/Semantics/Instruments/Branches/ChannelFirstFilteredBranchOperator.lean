import QEC.Semantics.Instruments.TensorPower.BranchOperator
/-!
# Filtered branch operators after a physical channel

This source-neutral helper regroups a finite sum after binding the unit-
observed instrument of a quantum channel to a finite observed instrument.
Filtering depends only on the second observation, so the sum is exactly the
same filtered branch sum evaluated on the channel's unnormalized output.
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
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- A finite predicate-filtered branch sum after a channel-first dependent
bind is the corresponding branch sum of the second instrument on the channel
output operator. -/
theorem toFiniteInstrument_bindDependent_branchOperator_filter_sum_eq
    (Phi : QuantumChannel H K) (J : FiniteInstrument kappa Omega K L)
    (predicate : Omega -> Prop) [DecidablePred predicate] (A : Operator H) :
    (∑ outcome : Sigma fun _ : PUnit => Omega,
      if predicate outcome.2 then
        (Phi.toFiniteInstrument.bindDependent (fun _ => J)).branchOperator
          outcome A
      else 0) =
      ∑ outcome : Omega,
        if predicate outcome then J.branchOperator outcome (Phi A) else 0 := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases houtcome : predicate outcome
  · rw [if_pos houtcome, if_pos houtcome,
      bindDependent_branchOperator_fst_punit,
      QuantumChannel.toFiniteInstrument_inducedMap_apply]
  · simp [houtcome]

end FiniteInstrument

end
end Semantics
end QEC

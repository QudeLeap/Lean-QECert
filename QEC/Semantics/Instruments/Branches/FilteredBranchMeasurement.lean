import QEC.Semantics.Instruments.Sequential.NestedFilteredMarginalBranchOperator
/-!
# Measurements of nested finite-instrument events

This source-neutral layer compares the measured mass of two finite observed
events when one predicate implies the other.  The comparison is made only
after an arbitrary physical channel and a genuine finite-instrument outcome;
it therefore applies to unnormalized postselected branch operators without
introducing a classical probability model or a normalization assumption.
-/

noncomputable section

namespace QEC
namespace Semantics
namespace FiniteInstrument

open Classical
open scoped BigOperators

universe u v w x y

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {mu : Type x} [Fintype mu]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

/-- A named filtered branch sum is the same finite sum written over the
filtered visible-outcome set. -/
theorem filteredBranchOperatorSum_eq_sum_filter
    (I : FiniteInstrument kappa Omega H K)
    (predicate : Omega -> Prop) [DecidablePred predicate]
    (A : Operator H) :
    filteredBranchOperatorSum I predicate A =
      ∑ outcome ∈ Finset.univ.filter predicate,
        I.branchOperator outcome A := by
  classical
  unfold filteredBranchOperatorSum
  rw [Finset.sum_filter]

/-- If one visible event implies another, every physical measurement of the
first unnormalized branch has at most the measured mass of the second. -/
theorem filteredBranchMeasuredTrace_mono
    (I : FiniteInstrument kappa Omega H K)
    (rho : DensityOperator H)
    (channel : QuantumChannel K L)
    (measurement : FiniteInstrument mu Xi L L)
    (measurementOutcome : Xi)
    (small large : Omega -> Prop)
    [DecidablePred small] [DecidablePred large]
    (himp : forall outcome, small outcome -> large outcome) :
    Complex.re (LinearMap.trace Complex L
      (measurement.branchOperator measurementOutcome
        (channel (filteredBranchOperatorSum I small rho.toOperator)))) <=
    Complex.re (LinearMap.trace Complex L
      (measurement.branchOperator measurementOutcome
        (channel (filteredBranchOperatorSum I large rho.toOperator)))) := by
  classical
  have hterm (outcome : Omega) :
      0 <= Complex.re (LinearMap.trace Complex L
        (measurement.branchOperator measurementOutcome
          (channel (I.branchOperator outcome rho.toOperator)))) := by
    exact (Complex.nonneg_iff.mp
      (measurement.branchOperator_positive measurementOutcome
        (channel.map_positive
          (I.branchOperator_positive outcome rho.positive))).trace_nonneg).1
  have hexpand (predicate : Omega -> Prop) [DecidablePred predicate] :
      Complex.re (LinearMap.trace Complex L
        (measurement.branchOperator measurementOutcome
          (channel (filteredBranchOperatorSum I predicate rho.toOperator)))) =
        ∑ outcome ∈ Finset.univ.filter predicate,
          Complex.re (LinearMap.trace Complex L
            (measurement.branchOperator measurementOutcome
              (channel (I.branchOperator outcome rho.toOperator)))) := by
    unfold filteredBranchOperatorSum
    rw [map_sum]
    rw [measurement.branchOperator_sum]
    rw [map_sum, Complex.re_sum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro outcome _
    by_cases houtcome : predicate outcome <;> simp [houtcome]
  rw [hexpand small, hexpand large]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro outcome houtcome
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at houtcome ⊢
    exact himp outcome houtcome
  · intro outcome _ _
    exact hterm outcome

end FiniteInstrument
end Semantics
end QEC

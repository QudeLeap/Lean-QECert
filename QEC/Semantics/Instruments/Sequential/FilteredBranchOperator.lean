import QEC.Semantics.Instruments.Sequential.Composition
/-!
# Filtered branch operators of sequential finite instruments

This source-neutral layer filters both observations of a sequential finite
instrument.  The composite event sum is the filtered second-stage branch map
applied to the filtered first-stage unnormalized operator.  No branch is
normalized and no probabilistic independence is asserted.
-/

universe u v w x y

namespace QEC
namespace Semantics

open Classical
open scoped BigOperators

noncomputable section

namespace FiniteInstrument

variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/-- Filtering both retained observations of a sequential bind may be
regrouped by first outcome, with the second-stage branch sum applied to the
first-stage unnormalized branch. -/
theorem bind_branchOperator_filter_sum_eq
    (I : FiniteInstrument kappa Omega H K)
    (J : Omega -> FiniteInstrument kappaTwo Xi K L)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Omega -> Xi -> Prop)
    [∀ firstOutcome, DecidablePred (secondPredicate firstOutcome)]
    (A : Operator H) :
    (∑ outcome : Sigma fun _ : Omega => Xi,
      if firstPredicate outcome.1 ∧
          secondPredicate outcome.1 outcome.2 then
        (I.bind (fun firstOutcome => J firstOutcome)).branchOperator outcome A
      else 0) =
      ∑ firstOutcome : Omega,
        if firstPredicate firstOutcome then
          ∑ secondOutcome : Xi,
            if secondPredicate firstOutcome secondOutcome then
              (J firstOutcome).branchOperator secondOutcome
                (I.branchOperator firstOutcome A)
            else 0
        else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro firstOutcome _
  by_cases hfirst : firstPredicate firstOutcome
  · rw [if_pos hfirst]
    apply Finset.sum_congr rfl
    intro secondOutcome _
    by_cases hsecond : secondPredicate firstOutcome secondOutcome
    · rw [if_pos hsecond, if_pos ⟨hfirst, hsecond⟩]
      exact bind_branchOperator I (fun firstOutcome => J firstOutcome)
        firstOutcome secondOutcome A
    · simp [hsecond]
  · simp [hfirst]

end FiniteInstrument

end
end Semantics
end QEC

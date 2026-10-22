import QEC.Semantics.Instruments.Core
/-!
# Linearity of finite-instrument branch operators

Every retained observed branch is a finite sum of Kraus conjugations and is
therefore complex-linear in its unnormalized input operator.  These explicit
lemmas let sequential physical proofs move finite sums and measured scalars
without reopening the Kraus definition.
-/

universe u v w x

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

/-- An observed branch sends the zero unnormalized input operator to zero. -/
@[simp] theorem branchOperator_zero (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) :
    I.branchOperator outcome 0 = 0 := by
  unfold branchOperator
  simp

/-- An observed branch preserves addition of unnormalized input operators. -/
theorem branchOperator_add (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) (A B : Operator H) :
    I.branchOperator outcome (A + B) =
      I.branchOperator outcome A + I.branchOperator outcome B := by
  unfold branchOperator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hindex : I.observe index = outcome
  · simp [hindex, LinearMap.add_comp, LinearMap.comp_add]
  · simp [hindex]

/-- An observed branch preserves complex scalar multiplication of an
unnormalized input operator. -/
theorem branchOperator_smul (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) (c : Complex) (A : Operator H) :
    I.branchOperator outcome (c • A) =
      c • I.branchOperator outcome A := by
  unfold branchOperator
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hindex : I.observe index = outcome
  · simp [hindex, LinearMap.smul_comp, LinearMap.comp_smul]
  · simp [hindex]

/-- An observed branch commutes with every finite input-operator sum. -/
theorem branchOperator_sum (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) {alpha : Type x} [Fintype alpha]
    (A : alpha -> Operator H) :
    I.branchOperator outcome (∑ index, A index) =
      ∑ index, I.branchOperator outcome (A index) := by
  classical
  induction (Finset.univ : Finset alpha) using Finset.induction_on with
  | empty => simp [branchOperator]
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, branchOperator_add, ih,
        Finset.sum_insert hindex]

end FiniteInstrument

end
end Semantics
end QEC

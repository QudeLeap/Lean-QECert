import Mathlib.Algebra.Module.BigOperators

universe u v w

/-!
# Finite-family centering algebra

This source-neutral lemma centers a finite weighted family at the distinguished
zero branch.  Its explicit `Finset` argument keeps callers from needing to
compare separately synthesized finite enumerations during instantiation.
-/

namespace QEC
namespace Distillation
namespace FiniteCentering

open scoped BigOperators

/-- Centering an accepted finite family at its zero branch leaves exactly the
accepted nonzero residual. -/
theorem finset_centered_sum_eq_nonzero_residual
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (indices : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι) (center : M)
    (hzero : branch zeroIndex = center) :
    (∑ i ∈ indices, if accepts i then weight i • branch i else 0) -
        (∑ i ∈ indices, if accepts i then weight i else 0) • center =
      ∑ i ∈ indices,
        if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0 := by
  rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : accepts i
  · by_cases hzeroIndex : i = zeroIndex
    · subst i
      simp [hi, hzero]
    · simpa [hi, hzeroIndex] using (smul_sub (weight i) (branch i) center).symm
  · simp [hi]

end FiniteCentering
end Distillation
end QEC

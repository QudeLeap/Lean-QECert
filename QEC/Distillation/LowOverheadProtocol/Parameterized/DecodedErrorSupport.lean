import QEC.Distillation.Core.FiniteDecodedTrace
/-!
# Parameterized HH18 decoded-error support

This support-only module packages generic explicit-support algebra needed by
the parameterized decoded-error bridge.  It has no HH18 carrier or protocol
instantiation and delegates finite centering and trace estimates to the
source-neutral `FiniteCentering` and `FiniteDecodedTrace` lemmas.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18Parameterized

open Semantics
open scoped BigOperators

universe u v w

/-- Cast a real explicit-support mass sum to the corresponding complex sum. -/
theorem complex_of_real_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] (support : Finset ι)
    (mass : ℝ) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected]
    (hmass : mass = support.sum (fun i =>
      if selected i then weight i else 0)) :
    (mass : Complex) = support.sum (fun i =>
      if selected i then (weight i : Complex) else 0) := by
  rw [hmass, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hselected : selected i <;> simp [hselected]

/-- Apply a linear operator map through one explicitly selected finite sum. -/
theorem linearMap_apply_selected_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (support : Finset ι) (linearMap : Operator H →ₗ[Complex] Operator K)
    (input : Operator H) (weight : ι → Complex) (selected : ι → Prop)
    [DecidablePred selected] (inputBranch : ι → Operator H)
    (outputBranch : ι → Operator K)
    (hinput : input = support.sum (fun i =>
      if selected i then weight i • inputBranch i else 0))
    (hpointwise : ∀ i, linearMap (inputBranch i) = outputBranch i) :
    linearMap input = support.sum (fun i =>
      if selected i then weight i • outputBranch i else 0) := by
  rw [hinput, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hselected : selected i
  · simp only [if_pos hselected]
    rw [map_smul, hpointwise i]
  · simp only [if_neg hselected, map_zero]

/-- Center one explicitly selected finite family at its distinguished zero
branch, delegating the algebra to `FiniteCentering`. -/
theorem centered_sum_of_explicit_support
    {ι : Type u} [DecidableEq ι] {R : Type v} [Semiring R] {M : Type w}
    [AddCommGroup M] [Module R M]
    (support : Finset ι) (weight : ι → R) (accepts : ι → Prop)
    [DecidablePred accepts] (branch : ι → M) (zeroIndex : ι)
    (center raw residual : M) (mass : R)
    (hraw : raw = support.sum (fun i =>
      if accepts i then weight i • branch i else 0))
    (hmass : mass = support.sum (fun i =>
      if accepts i then weight i else 0))
    (hresidual : residual = support.sum (fun i =>
      if accepts i ∧ i ≠ zeroIndex then weight i • (branch i - center) else 0))
    (hzero : branch zeroIndex = center) :
    raw - mass • center = residual := by
  rw [hraw, hmass, hresidual]
  exact FiniteCentering.finset_centered_sum_eq_nonzero_residual
    support weight accepts branch zeroIndex center hzero

/-- Bound the trace norm of an explicitly selected centered residual by twice
its selected real mass, delegating the pointwise finite estimate to
`FiniteDecodedTrace`. -/
theorem weighted_residual_traceNorm_of_explicit_support
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (support : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (residual : Operator H) (residualMass : ℝ)
    (hresidual : residual = support.sum (fun i =>
      if selected i then (weight i : Complex) • (branch i - center) else 0))
    (hmass : residualMass = support.sum (fun i =>
      if selected i then weight i else 0))
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm residual ≤ 2 * residualMass := by
  rw [hresidual, hmass]
  calc
    traceNorm (support.sum (fun i =>
        if selected i then (weight i : Complex) • (branch i - center) else 0)) ≤
        support.sum (fun i => if selected i then 2 * weight i else 0) := by
      simpa [mul_comm] using
        FiniteDecodedTrace.finset_weighted_residual_traceNorm_le_two_mul_mass
          support weight selected branch center hweight hbranch
    _ = 2 * support.sum (fun i => if selected i then weight i else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hselected : selected i <;> simp [hselected]

end HH18Parameterized
end Distillation
end QEC

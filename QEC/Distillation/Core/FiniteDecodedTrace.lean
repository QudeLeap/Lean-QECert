import QEC.Distillation.Core.FiniteCentering
import QEC.Semantics.Core.OperatorTraceNorm
/-!
# Source-neutral finite decoded trace estimates

These are explicit finite-family estimates.  They carry no protocol carrier,
success model, or target-state data; concrete layers must prove and supply all
of their hypotheses from their own physical construction.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace FiniteDecodedTrace

open Semantics
open scoped BigOperators

universe u v

/-- A finite nonnegative weighted family whose centered branches are each at
trace distance at most two has residual trace norm at most twice its selected
weight mass. -/
theorem finset_weighted_residual_traceNorm_le_two_mul_mass
    {ι : Type u} [DecidableEq ι] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (indices : Finset ι) (weight : ι → ℝ) (selected : ι → Prop)
    [DecidablePred selected] (branch : ι → Operator H) (center : Operator H)
    (hweight : ∀ i, 0 ≤ weight i)
    (hbranch : ∀ i, traceNorm (branch i - center) ≤ 2) :
    traceNorm (∑ i ∈ indices,
        if selected i then (weight i : Complex) • (branch i - center) else 0) ≤
      ∑ i ∈ indices, if selected i then 2 * weight i else 0 := by
  classical
  calc
    traceNorm (∑ i ∈ indices,
        if selected i then (weight i : Complex) • (branch i - center) else 0) ≤
      ∑ i ∈ indices, traceNorm
        (if selected i then (weight i : Complex) • (branch i - center) else 0) := by
          simpa using traceNorm_sum_le indices (fun i : ι =>
            if selected i then (weight i : Complex) • (branch i - center) else 0)
    _ ≤ ∑ i ∈ indices, if selected i then 2 * weight i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hselected : selected i
      · simp only [if_pos hselected, traceNorm_smul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight i)]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hbranch i) (hweight i)
      · simp only [if_neg hselected]
        exact le_of_eq (by rw [traceNorm_eq_zero_iff])

/-- Scaling a residual by the inverse of a positive real success mass preserves
its trace estimate with the same explicit normalization. -/
theorem normalized_residual_traceNorm_le
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (success residualMass : ℝ) (residual : Operator H)
    (hsuccess : 0 < success)
    (hresidual : traceNorm residual ≤ 2 * residualMass) :
    traceNorm ((success : Complex)⁻¹ • residual) ≤ 2 * (residualMass / success) := by
  rw [traceNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsuccess]
  calc
    success⁻¹ * traceNorm residual ≤ success⁻¹ * (2 * residualMass) :=
      mul_le_mul_of_nonneg_left hresidual (by positivity)
    _ = 2 * (residualMass / success) := by
      field_simp [ne_of_gt hsuccess]

end FiniteDecodedTrace
end Distillation
end QEC

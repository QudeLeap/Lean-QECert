import QEC.Distillation.TwoQubitOperations.Parity
/-!
# Two-qubit parity Born weights

Squared-norm outcome weights for the even and odd `Z ⊗ Z` projectors.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace TwoQubit

open scoped InnerProductSpace

def zzEvenWeight (psi : TwoQubitSpace) : ℝ :=
  ‖zzEvenProjector psi‖ ^ 2

def zzOddWeight (psi : TwoQubitSpace) : ℝ :=
  ‖zzOddProjector psi‖ ^ 2

theorem zzEvenWeight_eq_re_inner (psi : TwoQubitSpace) :
    zzEvenWeight psi =
      Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ := by
  unfold zzEvenWeight
  calc
    ‖zzEvenProjector psi‖ ^ 2 =
        Complex.re
          ⟪zzEvenProjector psi, zzEvenProjector psi⟫_ℂ :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) _
    _ = Complex.re
          ⟪psi, zzEvenProjector (zzEvenProjector psi)⟫_ℂ :=
      congrArg Complex.re
        (zzEvenProjector_isSymmetricProjection.isSymmetric
          psi (zzEvenProjector psi))
    _ = Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ := by
      rw [← Module.End.mul_apply, zzEvenProjector_idempotent]

theorem zzOddWeight_eq_re_inner (psi : TwoQubitSpace) :
    zzOddWeight psi =
      Complex.re ⟪psi, zzOddProjector psi⟫_ℂ := by
  unfold zzOddWeight
  calc
    ‖zzOddProjector psi‖ ^ 2 =
        Complex.re
          ⟪zzOddProjector psi, zzOddProjector psi⟫_ℂ :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) _
    _ = Complex.re
          ⟪psi, zzOddProjector (zzOddProjector psi)⟫_ℂ :=
      congrArg Complex.re
        (zzOddProjector_isSymmetricProjection.isSymmetric
          psi (zzOddProjector psi))
    _ = Complex.re ⟪psi, zzOddProjector psi⟫_ℂ := by
      rw [← Module.End.mul_apply, zzOddProjector_idempotent]

theorem zzEvenWeight_nonneg (psi : TwoQubitSpace) :
    0 ≤ zzEvenWeight psi :=
  sq_nonneg _

theorem zzOddWeight_nonneg (psi : TwoQubitSpace) :
    0 ≤ zzOddWeight psi :=
  sq_nonneg _

theorem zzWeights_sum (psi : TwoQubitSpace) :
    zzEvenWeight psi + zzOddWeight psi = ‖psi‖ ^ 2 := by
  rw [zzEvenWeight_eq_re_inner, zzOddWeight_eq_re_inner]
  calc
    Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ +
          Complex.re ⟪psi, zzOddProjector psi⟫_ℂ =
        Complex.re
          (⟪psi, zzEvenProjector psi⟫_ℂ +
            ⟪psi, zzOddProjector psi⟫_ℂ) := by
      rw [Complex.add_re]
    _ = Complex.re
          ⟪psi, zzEvenProjector psi + zzOddProjector psi⟫_ℂ := by
      rw [inner_add_right]
    _ = Complex.re
          ⟪psi, (zzEvenProjector + zzOddProjector) psi⟫_ℂ := rfl
    _ = Complex.re ⟪psi, psi⟫_ℂ := by
      rw [zzProjectors_complete]
      rfl
    _ = ‖psi‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) psi).symm

theorem zzWeights_sum_of_normSq_one
    (psi : TwoQubitSpace) (hpsi : ‖psi‖ ^ 2 = 1) :
    zzEvenWeight psi + zzOddWeight psi = 1 := by
  calc
    zzEvenWeight psi + zzOddWeight psi = ‖psi‖ ^ 2 :=
      zzWeights_sum psi
    _ = 1 := hpsi

theorem zzEvenWeight_eq_zero_iff (psi : TwoQubitSpace) :
    zzEvenWeight psi = 0 ↔ zzEvenProjector psi = 0 := by
  simp only [zzEvenWeight, sq_eq_zero_iff, norm_eq_zero]

theorem zzOddWeight_eq_zero_iff (psi : TwoQubitSpace) :
    zzOddWeight psi = 0 ↔ zzOddProjector psi = 0 := by
  simp only [zzOddWeight, sq_eq_zero_iff, norm_eq_zero]

end TwoQubit
end Distillation
end QEC

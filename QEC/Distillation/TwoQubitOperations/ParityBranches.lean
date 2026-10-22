import QEC.Distillation.TwoQubitOperations.ParityWeights
import QEC.Semantics.ErrorCorrection.CodeSupport
noncomputable section

namespace QEC
namespace Distillation
namespace TwoQubit

open Semantics

def zzEvenBranchState
    (psi : TwoQubitSpace) (_h : 0 < zzEvenWeight psi) :
    TwoQubitSpace :=
  (Real.sqrt (zzEvenWeight psi) : Complex)⁻¹ •
    zzEvenProjector psi

def zzOddBranchState
    (psi : TwoQubitSpace) (_h : 0 < zzOddWeight psi) :
    TwoQubitSpace :=
  (Real.sqrt (zzOddWeight psi) : Complex)⁻¹ •
    zzOddProjector psi

@[simp] theorem zzEvenBranchState_norm
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    ‖zzEvenBranchState psi h‖ = 1 := by
  have hprojector : zzEvenProjector psi ≠ 0 := by
    intro hzero
    exact h.ne' ((zzEvenWeight_eq_zero_iff psi).2 hzero)
  have hnorm : ‖zzEvenProjector psi‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hprojector
  have hsqrt :
      Real.sqrt (zzEvenWeight psi) = ‖zzEvenProjector psi‖ := by
    rw [zzEvenWeight, Real.sqrt_sq (norm_nonneg _)]
  unfold zzEvenBranchState
  rw [norm_smul, norm_inv, Complex.norm_real, hsqrt]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    inv_mul_cancel₀ hnorm

@[simp] theorem zzOddBranchState_norm
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    ‖zzOddBranchState psi h‖ = 1 := by
  have hprojector : zzOddProjector psi ≠ 0 := by
    intro hzero
    exact h.ne' ((zzOddWeight_eq_zero_iff psi).2 hzero)
  have hnorm : ‖zzOddProjector psi‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hprojector
  have hsqrt :
      Real.sqrt (zzOddWeight psi) = ‖zzOddProjector psi‖ := by
    rw [zzOddWeight, Real.sqrt_sq (norm_nonneg _)]
  unfold zzOddBranchState
  rw [norm_smul, norm_inv, Complex.norm_real, hsqrt]
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    inv_mul_cancel₀ hnorm

@[simp] theorem zzEvenProjector_branchState
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    zzEvenProjector (zzEvenBranchState psi h) =
      zzEvenBranchState psi h := by
  unfold zzEvenBranchState
  rw [LinearMap.map_smul]
  congr 1
  rw [← Module.End.mul_apply, zzEvenProjector_idempotent]

@[simp] theorem zzOddProjector_branchState
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    zzOddProjector (zzOddBranchState psi h) =
      zzOddBranchState psi h := by
  unfold zzOddBranchState
  rw [LinearMap.map_smul]
  congr 1
  rw [← Module.End.mul_apply, zzOddProjector_idempotent]

theorem zzEvenBranchState_rescale
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (Real.sqrt (zzEvenWeight psi) : Complex) •
        zzEvenBranchState psi h =
      zzEvenProjector psi := by
  have hsqrt_ne :
      (Real.sqrt (zzEvenWeight psi) : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 h))
  unfold zzEvenBranchState
  rw [smul_smul, mul_inv_cancel₀ hsqrt_ne, one_smul]

theorem zzOddBranchState_rescale
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (Real.sqrt (zzOddWeight psi) : Complex) •
        zzOddBranchState psi h =
      zzOddProjector psi := by
  have hsqrt_ne :
      (Real.sqrt (zzOddWeight psi) : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 h))
  unfold zzOddBranchState
  rw [smul_smul, mul_inv_cancel₀ hsqrt_ne, one_smul]

noncomputable def zzEvenBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    DensityOperator TwoQubitSpace :=
  DensityOperator.pureOfNonzero (zzEvenBranchState psi h) (by
    intro hzero
    have hnorm := zzEvenBranchState_norm psi h
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm)

noncomputable def zzOddBranchDensity
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    DensityOperator TwoQubitSpace :=
  DensityOperator.pureOfNonzero (zzOddBranchState psi h) (by
    intro hzero
    have hnorm := zzOddBranchState_norm psi h
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm)

@[simp] theorem zzEvenBranchDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (zzEvenBranchDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzEvenBranchState psi h)
        (zzEvenBranchState psi h)).toLinearMap := by
  rw [zzEvenBranchDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [inner_self_eq_norm_sq_to_K, zzEvenBranchState_norm]
  norm_num

@[simp] theorem zzOddBranchDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (zzOddBranchDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzOddBranchState psi h)
        (zzOddBranchState psi h)).toLinearMap := by
  rw [zzOddBranchDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [inner_self_eq_norm_sq_to_K, zzOddBranchState_norm]
  norm_num

end TwoQubit
end Distillation
end QEC

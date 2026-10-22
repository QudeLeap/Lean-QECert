import QEC.Distillation.Universality.OneQubitClifford
import QEC.Semantics.ErrorCorrection.CodeSupport
/-!
# One-qubit phase states

Exact amplitudes, normalized one-qubit phase states, and their pure density
operators. This module does not state gate-injection or distillation results.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitMagic

open Semantics Semantics.Qubit

/-- The unit complex amplitude `exp(i theta)`. -/
def phaseAmplitude (theta : Real) : Complex :=
  Complex.exp ((theta : Complex) * Complex.I)

@[simp] theorem phaseAmplitude_zero : phaseAmplitude 0 = 1 := by
  simp [phaseAmplitude]

theorem phaseAmplitude_add (theta phi : Real) :
    phaseAmplitude (theta + phi) =
      phaseAmplitude theta * phaseAmplitude phi := by
  unfold phaseAmplitude
  rw [show (((theta + phi : Real) : Complex) * Complex.I) =
      (theta : Complex) * Complex.I + (phi : Complex) * Complex.I by
    push_cast
    ring]
  exact Complex.exp_add _ _

/-- Integer multiples of one full turn have trivial phase. -/
theorem phaseAmplitude_two_pi_mul_int (k : Int) :
    phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by
  unfold phaseAmplitude
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  all_goals push_cast
  all_goals ring_nf

theorem phaseAmplitude_neg (theta : Real) :
    phaseAmplitude (-theta) = (phaseAmplitude theta)⁻¹ := by
  unfold phaseAmplitude
  rw [show (((-theta : Real) : Complex) * Complex.I) =
      -((theta : Complex) * Complex.I) by
    push_cast
    ring]
  exact Complex.exp_neg _

@[simp] theorem phaseAmplitude_norm (theta : Real) :
    ‖phaseAmplitude theta‖ = 1 := by
  simpa [phaseAmplitude] using Complex.norm_exp_ofReal_mul_I theta

@[simp] theorem phaseAmplitude_mul_conj (theta : Real) :
    phaseAmplitude theta * star (phaseAmplitude theta) = 1 := by
  rw [Complex.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, phaseAmplitude_norm]
  norm_num

theorem phaseAmplitude_neg_pi_div_four :
    phaseAmplitude (-Real.pi / 4) =
      (Real.sqrt 2 / 2 : Complex) -
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((-Real.pi / 4 : Real) : Complex) * Complex.I) =
        (Real.cos (-Real.pi / 4) : Complex) +
          (Real.sin (-Real.pi / 4) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (-Real.pi / 4)
    _ = (Real.sqrt 2 / 2 : Complex) -
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
      rw [show -Real.pi / 4 = -(Real.pi / 4) by ring,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
        Real.sin_pi_div_four]
      push_cast
      ring

theorem phaseAmplitude_neg_pi_div_six :
    phaseAmplitude (-Real.pi / 6) =
      (Real.sqrt 3 / 2 : Complex) - (2 : Complex)⁻¹ * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((-Real.pi / 6 : Real) : Complex) * Complex.I) =
        (Real.cos (-Real.pi / 6) : Complex) +
          (Real.sin (-Real.pi / 6) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (-Real.pi / 6)
    _ = (Real.sqrt 3 / 2 : Complex) - (2 : Complex)⁻¹ * Complex.I := by
      rw [show -Real.pi / 6 = -(Real.pi / 6) by ring,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six,
        Real.sin_pi_div_six]
      push_cast
      norm_num
      ring

/-- The normalized phase state `(1, exp(i theta)) / sqrt 2`. -/
def phaseState (theta : Real) : QubitSpace :=
  WithLp.toLp 2 fun b =>
    if b = 0 then (Real.sqrt 2 : Complex)⁻¹
    else (Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude theta

@[simp] theorem phaseState_apply_zero (theta : Real) :
    phaseState theta 0 = (Real.sqrt 2 : Complex)⁻¹ := by
  simp [phaseState]

@[simp] theorem phaseState_apply_one (theta : Real) :
    phaseState theta 1 =
      (Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude theta := by
  simp [phaseState]

theorem phaseState_inner_self (theta : Real) :
    inner Complex (phaseState theta) (phaseState theta) = 1 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, phaseState_apply_zero,
    phaseState_apply_one, RCLike.inner_apply]
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  calc
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ +
        (Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude theta *
          ((Real.sqrt 2 : Complex)⁻¹ * star (phaseAmplitude theta)) =
        (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ +
          ((Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹) *
            (phaseAmplitude theta * star (phaseAmplitude theta)) := by
      ring
    _ = 2 * ((Real.sqrt 2 : Complex)⁻¹ *
          (Real.sqrt 2 : Complex)⁻¹) := by
      rw [phaseAmplitude_mul_conj]
      ring
    _ = 1 := by
      field_simp [hsqrt_ne]
      rw [pow_two, hsqrt_sq]

@[simp] theorem phaseState_norm (theta : Real) :
    ‖phaseState theta‖ = 1 := by
  have hinner := phaseState_inner_self theta
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖phaseState theta‖ ^ 2 = 1 := by
    have hsq_complex :
        ((‖phaseState theta‖ ^ 2 : Real) : Complex) = 1 := by
      simpa using hinner
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg (phaseState theta)]

theorem phaseState_ne_zero (theta : Real) :
    phaseState theta ≠ 0 := by
  intro hzero
  have hnorm := phaseState_norm theta
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The pure density operator of the normalized phase state. -/
noncomputable def phaseStateDensity (theta : Real) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero
    (phaseState theta) (phaseState_ne_zero theta)

@[simp] theorem phaseStateDensity_toOperator (theta : Real) :
    (phaseStateDensity theta).toOperator =
      (InnerProductSpace.rankOne Complex
        (phaseState theta) (phaseState theta)).toLinearMap := by
  rw [phaseStateDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [phaseState_inner_self]
  simp

/-- The diagonal matrix with phase `exp(i theta)` on the one coordinate. -/
def phaseShiftMatrix (theta : Real) : Matrix (Fin 2) (Fin 2) Complex :=
  !![1, 0; 0, phaseAmplitude theta]

/-- The diagonal phase shift as an operator on the concrete qubit space. -/
def phaseShiftOperator (theta : Real) : Operator QubitSpace :=
  Matrix.toEuclideanLin (phaseShiftMatrix theta)

@[simp] theorem phaseShiftOperator_apply_zero (theta : Real) (psi : QubitSpace) :
    phaseShiftOperator theta psi 0 = psi 0 := by
  simp [phaseShiftOperator, phaseShiftMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem phaseShiftOperator_apply_one (theta : Real) (psi : QubitSpace) :
    phaseShiftOperator theta psi 1 = phaseAmplitude theta * psi 1 := by
  simp [phaseShiftOperator, phaseShiftMatrix, Matrix.mulVec, dotProduct]

theorem phaseShiftOperator_basis_zero (theta : Real) :
    phaseShiftOperator theta (EuclideanSpace.basisFun (Fin 2) Complex 0) =
      EuclideanSpace.basisFun (Fin 2) Complex 0 := by
  ext b
  fin_cases b <;> simp

theorem phaseShiftOperator_basis_one (theta : Real) :
    phaseShiftOperator theta (EuclideanSpace.basisFun (Fin 2) Complex 1) =
      phaseAmplitude theta • EuclideanSpace.basisFun (Fin 2) Complex 1 := by
  ext b
  fin_cases b <;> simp

@[simp] theorem phaseShiftOperator_zero :
    phaseShiftOperator 0 = (1 : Operator QubitSpace) := by
  ext psi b
  fin_cases b <;> simp

theorem phaseShiftOperator_add (theta phi : Real) :
    phaseShiftOperator theta * phaseShiftOperator phi =
      phaseShiftOperator (theta + phi) := by
  ext psi b
  fin_cases b <;>
    simp [Module.End.mul_apply, phaseAmplitude_add] <;> ring

@[simp] theorem phaseShiftOperator_neg_mul (theta : Real) :
    phaseShiftOperator (-theta) * phaseShiftOperator theta = 1 := by
  rw [phaseShiftOperator_add]
  simp

@[simp] theorem phaseShiftOperator_mul_neg (theta : Real) :
    phaseShiftOperator theta * phaseShiftOperator (-theta) = 1 := by
  rw [phaseShiftOperator_add]
  simp

theorem phaseShiftOperator_pi_div_two :
    phaseShiftOperator (Real.pi / 2) = phaseOperator := by
  ext psi b
  fin_cases b
  · change phaseShiftOperator (Real.pi / 2) psi 0 = phaseOperator psi 0
    simp
  · change phaseShiftOperator (Real.pi / 2) psi 1 = phaseOperator psi 1
    rw [phaseShiftOperator_apply_one, phaseOperator_apply_one]
    simp [phaseAmplitude, Complex.exp_pi_div_two_mul_I]

theorem phaseShiftOperator_phaseState (theta phi : Real) :
    phaseShiftOperator theta (phaseState phi) = phaseState (theta + phi) := by
  ext b
  fin_cases b
  · change phaseShiftOperator theta (phaseState phi) 0 =
      phaseState (theta + phi) 0
    simp
  · change phaseShiftOperator theta (phaseState phi) 1 =
      phaseState (theta + phi) 1
    rw [phaseShiftOperator_apply_one, phaseState_apply_one,
      phaseState_apply_one, phaseAmplitude_add]
    ring

theorem phaseShiftOperator_map_inner (theta : Real)
    (x y : QubitSpace) :
    inner Complex (phaseShiftOperator theta x)
      (phaseShiftOperator theta y) = inner Complex x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two, phaseShiftOperator_apply_zero,
    phaseShiftOperator_apply_one, RCLike.inner_apply, map_mul]
  calc
    y 0 * star (x 0) +
        phaseAmplitude theta * y 1 *
          (star (phaseAmplitude theta) * star (x 1)) =
      y 0 * star (x 0) +
        (phaseAmplitude theta * star (phaseAmplitude theta)) *
          (y 1 * star (x 1)) := by ring
    _ = y 0 * star (x 0) + y 1 * star (x 1) := by
      rw [phaseAmplitude_mul_conj]
      ring

/-- The phase shift with its negated-angle operator as explicit inverse. -/
def phaseShiftLinearEquiv (theta : Real) :
    QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk (phaseShiftOperator theta) (phaseShiftOperator (-theta))
    (fun psi => by
      change phaseShiftOperator (-theta) (phaseShiftOperator theta psi) = psi
      have h := LinearMap.congr_fun (phaseShiftOperator_neg_mul theta) psi
      simpa only [Module.End.mul_apply, Module.End.one_apply] using h)
    (fun psi => by
      change phaseShiftOperator theta (phaseShiftOperator (-theta) psi) = psi
      have h := LinearMap.congr_fun (phaseShiftOperator_mul_neg theta) psi
      simpa only [Module.End.mul_apply, Module.End.one_apply] using h)

@[simp] theorem phaseShiftLinearEquiv_apply (theta : Real) (psi : QubitSpace) :
    phaseShiftLinearEquiv theta psi = phaseShiftOperator theta psi :=
  rfl

@[simp] theorem phaseShiftLinearEquiv_symm_apply
    (theta : Real) (psi : QubitSpace) :
    (phaseShiftLinearEquiv theta).symm psi =
      phaseShiftOperator (-theta) psi :=
  rfl

/-- The diagonal phase shift packaged as a unitary transport. -/
def phaseShiftTransport (theta : Real) :
    UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseShiftLinearEquiv theta
  map_inner := phaseShiftOperator_map_inner theta

@[simp] theorem phaseShiftTransport_apply (theta : Real) (psi : QubitSpace) :
    phaseShiftTransport theta psi = phaseShiftOperator theta psi :=
  rfl

end OneQubitMagic
end Distillation
end QEC

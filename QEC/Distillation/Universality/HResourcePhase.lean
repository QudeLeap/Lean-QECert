import QEC.Distillation.Universality.OneQubitMagic
import QEC.Semantics.ErrorCorrection.QuditSubsystem
/-!
# Ideal H-resource phase preparation

This module realizes the finite one-qubit H-resource conversion from the
BK05 ideal-resource route.  It identifies the existing H magic-state density
with the source vector, then applies the concrete K phase followed by
Hadamard.  The vector calculation retains the source global phase; the final
density statement removes it only after proving that phase has unit norm.

No retry, injection client, or universality conclusion is stated
here.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitMagic

open Semantics Semantics.Qubit

/-- The source `|H>` vector with coordinates `cos(pi / 8), sin(pi / 8)`. -/
def sourceHState : QubitSpace :=
  WithLp.toLp 2 fun b =>
    if b = 0 then (Real.cos (Real.pi / 8) : Complex)
    else (Real.sin (Real.pi / 8) : Complex)

@[simp] theorem sourceHState_apply_zero :
    sourceHState 0 = (Real.cos (Real.pi / 8) : Complex) := by
  simp [sourceHState]

@[simp] theorem sourceHState_apply_one :
    sourceHState 1 = (Real.sin (Real.pi / 8) : Complex) := by
  simp [sourceHState]

theorem sourceHState_inner_self :
    inner Complex sourceHState sourceHState = 1 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, sourceHState_apply_zero, sourceHState_apply_one,
    RCLike.inner_apply, Complex.conj_ofReal]
  norm_cast
  simpa [pow_two] using Real.cos_sq_add_sin_sq (Real.pi / 8)

@[simp] theorem sourceHState_norm : ‖sourceHState‖ = 1 := by
  have hinner := sourceHState_inner_self
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖sourceHState‖ ^ 2 = 1 := by
    have hsq_complex : ((‖sourceHState‖ ^ 2 : Real) : Complex) = 1 := by
      simpa using hinner
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg sourceHState]

theorem sourceHState_ne_zero : sourceHState ≠ 0 := by
  intro hzero
  have hnorm := sourceHState_norm
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The pure density of the source H vector. -/
noncomputable def sourceHDensity : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero sourceHState sourceHState_ne_zero

@[simp] theorem sourceHDensity_toOperator :
    sourceHDensity.toOperator =
      (InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap := by
  rw [sourceHDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [sourceHState_inner_self]
  simp

private theorem cos_pi_div_eight_sq :
    Real.cos (Real.pi / 8) ^ 2 = 1 / 2 + Real.sqrt 2 / 4 := by
  rw [Real.cos_sq]
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  ring

private theorem sin_pi_div_eight_sq :
    Real.sin (Real.pi / 8) ^ 2 = 1 / 2 - Real.sqrt 2 / 4 := by
  rw [Real.sin_sq, cos_pi_div_eight_sq]
  ring

private theorem sin_pi_div_eight_mul_cos_pi_div_eight :
    Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) = Real.sqrt 2 / 4 := by
  calc
    Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) =
        Real.sin (2 * (Real.pi / 8)) / 2 := by
          rw [Real.sin_two_mul]
          ring
    _ = Real.sqrt 2 / 4 := by
      rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four]
      ring

private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem rankOne_apply_coordinate
    (u v x : QubitSpace) (b : Fin 2) :
    ((InnerProductSpace.rankOne Complex u v).toLinearMap x) b =
      (inner Complex v x) * u b := by
  change ((InnerProductSpace.rankOne Complex u v) x).ofLp b = _
  rw [InnerProductSpace.rankOne_apply]
  rfl

/-- The existing reference H magic-state density is the source pure H vector. -/
theorem hMagicState_eq_sourceHDensity : hMagicState = sourceHDensity := by
  apply densityOperator_ext_toOperator
  rw [sourceHDensity_toOperator]
  change blochProjector hBloch =
    (InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  have hsqrt_inv :
      ((1 / Real.sqrt 2 : Real) : Complex) = (Real.sqrt 2 : Complex) / 2 := by
    push_cast
    field_simp [hsqrt_ne]
    rw [pow_two, hsqrt_sq]
  have hcos_sq :
      (Real.cos (Real.pi / 8) : Complex) ^ 2 =
        (1 / 2 + Real.sqrt 2 / 4 : Real) := by
    rw [pow_two]
    exact_mod_cast (show
      Real.cos (Real.pi / 8) * Real.cos (Real.pi / 8) =
        1 / 2 + Real.sqrt 2 / 4 by
          simpa [pow_two] using cos_pi_div_eight_sq)
  have hsin_sq :
      (Real.sin (Real.pi / 8) : Complex) ^ 2 =
        (1 / 2 - Real.sqrt 2 / 4 : Real) := by
    rw [pow_two]
    exact_mod_cast (show
      Real.sin (Real.pi / 8) * Real.sin (Real.pi / 8) =
        1 / 2 - Real.sqrt 2 / 4 by
          simpa [pow_two] using sin_pi_div_eight_sq)
  have hsin_cos :
      (Real.sin (Real.pi / 8) : Complex) *
          (Real.cos (Real.pi / 8) : Complex) =
        (Real.sqrt 2 / 4 : Real) := by
    exact_mod_cast sin_pi_div_eight_mul_cos_pi_div_eight
  have hcos_sin :
      (Real.cos (Real.pi / 8) : Complex) *
          (Real.sin (Real.pi / 8) : Complex) =
        (Real.sqrt 2 / 4 : Real) := by
    rw [mul_comm]
    exact hsin_cos
  have hangle : Real.pi * (1 / 8 : Real) = Real.pi / 8 := by
    ring
  ext psi b
  fin_cases b
  · change blochProjector hBloch psi 0 =
      ((InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap psi) 0
    rw [rankOne_apply_coordinate]
    change (2 : Complex)⁻¹ * (psi 0 + (blochOperator hBloch psi) 0) = _
    simp only [blochOperator_apply_zero, hBloch, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply]
    change _ =
      (psi 0 * star (sourceHState 0) + psi 1 * star (sourceHState 1)) * sourceHState 0
    rw [sourceHState_apply_zero, sourceHState_apply_one]
    rw [Complex.star_def]
    simp only [Complex.conj_ofReal]
    ring_nf
    have hcross :
        psi 1 * (Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex) =
          psi 1 * (Real.sqrt 2 / 4 : Real) := by
      calc
        _ = psi 1 * ((Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex)) := by ring
        _ = _ := by rw [hcos_sin]
    rw [hangle, hcos_sq, hcross]
    field_simp [hsqrt_ne]
    rw [hsqrt_inv]
    push_cast
    ring
  · change blochProjector hBloch psi 1 =
      ((InnerProductSpace.rankOne Complex sourceHState sourceHState).toLinearMap psi) 1
    rw [rankOne_apply_coordinate]
    change (2 : Complex)⁻¹ * (psi 1 + (blochOperator hBloch psi) 1) = _
    simp only [blochOperator_apply_one, hBloch, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply]
    change _ =
      (psi 0 * star (sourceHState 0) + psi 1 * star (sourceHState 1)) * sourceHState 1
    rw [sourceHState_apply_zero, sourceHState_apply_one]
    rw [Complex.star_def]
    simp only [Complex.conj_ofReal]
    ring_nf
    have hcross :
        psi 0 * (Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex) =
          psi 0 * (Real.sqrt 2 / 4 : Real) := by
      calc
        _ = psi 0 * ((Real.cos (Real.pi / 8) : Complex) *
            (Real.sin (Real.pi / 8) : Complex)) := by ring
        _ = _ := by rw [hcos_sin]
    rw [hangle, hsin_sq, hcross]
    field_simp [hsqrt_ne]
    rw [hsqrt_inv]
    push_cast
    ring

theorem phaseAmplitude_pi_div_eight :
    phaseAmplitude (Real.pi / 8) =
      (Real.cos (Real.pi / 8) : Complex) +
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
  unfold phaseAmplitude
  exact Complex.exp_ofReal_mul_I (Real.pi / 8)

theorem phaseAmplitude_neg_pi_div_eight :
    phaseAmplitude (-Real.pi / 8) =
      (Real.cos (Real.pi / 8) : Complex) -
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((-Real.pi / 8 : Real) : Complex) * Complex.I) =
        (Real.cos (-Real.pi / 8) : Complex) +
          (Real.sin (-Real.pi / 8) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (-Real.pi / 8)
    _ = (Real.cos (Real.pi / 8) : Complex) -
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
      rw [show -Real.pi / 8 = -(Real.pi / 8) by ring,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring

/-- The source H-route Clifford composition: first K, then Hadamard. -/
noncomputable def hResourceTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseTransport.toLinearEquiv.trans hadamardTransport.toLinearEquiv
  map_inner := by
    intro x y
    exact (hadamardTransport.map_inner (phaseTransport x) (phaseTransport y)).trans
      (phaseTransport.map_inner x y)

@[simp] theorem hResourceTransport_apply (psi : QubitSpace) :
    hResourceTransport psi = hadamardOperator (phaseOperator psi) :=
  rfl

/-- BK05's vector-level H/K calculation, retaining its explicit global phase. -/
theorem hResourceTransport_sourceHState :
    hResourceTransport sourceHState =
      phaseAmplitude (Real.pi / 8) • phaseState (-Real.pi / 4) := by
  have hproduct :
      phaseAmplitude (Real.pi / 8) * phaseAmplitude (-Real.pi / 4) =
        (Real.cos (Real.pi / 8) : Complex) -
          (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
    rw [← phaseAmplitude_add]
    rw [show Real.pi / 8 + -Real.pi / 4 = -Real.pi / 8 by ring]
    exact phaseAmplitude_neg_pi_div_eight
  ext b
  fin_cases b
  · change hadamardOperator (phaseOperator sourceHState) 0 =
      phaseAmplitude (Real.pi / 8) * phaseState (-Real.pi / 4) 0
    rw [hadamardOperator_apply_zero, phaseOperator_apply_zero,
      phaseOperator_apply_one, sourceHState_apply_zero, sourceHState_apply_one,
      phaseState_apply_zero, phaseAmplitude_pi_div_eight]
    ring
  · change hadamardOperator (phaseOperator sourceHState) 1 =
      phaseAmplitude (Real.pi / 8) * phaseState (-Real.pi / 4) 1
    rw [hadamardOperator_apply_one, phaseOperator_apply_zero,
      phaseOperator_apply_one, sourceHState_apply_zero, sourceHState_apply_one,
      phaseState_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.cos (Real.pi / 8) : Complex) -
            Complex.I * (Real.sin (Real.pi / 8) : Complex)) =
          (Real.sqrt 2 : Complex)⁻¹ *
            (phaseAmplitude (Real.pi / 8) * phaseAmplitude (-Real.pi / 4)) := by
              rw [hproduct]
              ring
      _ = phaseAmplitude (Real.pi / 8) *
          ((Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude (-Real.pi / 4)) := by
            ring

private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace)
    (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x b
  rw [rankOne_apply_coordinate, rankOne_apply_coordinate]
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi b) =
        (z * star z) * inner Complex psi x * psi b := by ring
    _ = inner Complex psi x * psi b := by rw [hz]; ring

/-- The H/K Clifford composition sends the existing H density to `A_{-pi/4}`. -/
theorem hResourceTransport_hMagicState :
    hResourceTransport.conjDensity hMagicState =
      phaseStateDensity (-Real.pi / 4) := by
  rw [hMagicState_eq_sourceHDensity]
  apply densityOperator_ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, sourceHDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne, hResourceTransport_sourceHState,
    phaseStateDensity_toOperator]
  exact rankOne_global_phase (phaseAmplitude (Real.pi / 8))
    (phaseState (-Real.pi / 4)) (phaseAmplitude_mul_conj (Real.pi / 8))

end OneQubitMagic
end Distillation
end QEC

import QEC.Distillation.Universality.OneQubitMagic
import QEC.Distillation.Core.MagicStateProtocol
import QEC.Distillation.TwoQubitOperations.Core
/-!
# Ideal T-resource phase preparation

The source-exact BK05 ideal `T`-resource preprocessing route.  Two copies of
the concrete T state are projected onto the honest `ZZ`-even branch, passed
through the existing XOR/discard primitive, and then acted on by Hadamard.
The resulting state is the `-pi/6` phase state up to global phase.

This module is internal.  It does not invoke the phase-injection retry API or
state density/universality conclusions.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitMagic

open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct

/-- The source parameter `cos (2 beta) = 1 / sqrt 3` for the ideal T state. -/
def sourceTParameter : Real := (Real.sqrt 3)⁻¹

/-- The nonnegative zero-coordinate amplitude of the source T state. -/
def sourceTCos : Real := Real.sqrt ((1 + sourceTParameter) / 2)

/-- The nonnegative one-coordinate magnitude of the source T state. -/
def sourceTSin : Real := sourceTParameter / (Real.sqrt 2 * sourceTCos)

private theorem sqrt_three_pos : 0 < Real.sqrt 3 :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 :=
  sqrt_three_pos.ne'

theorem sourceTParameter_nonneg : 0 ≤ sourceTParameter := by
  unfold sourceTParameter
  exact inv_nonneg.mpr (le_of_lt sqrt_three_pos)

theorem sourceTParameter_sq : sourceTParameter ^ 2 = 1 / 3 := by
  unfold sourceTParameter
  have hsquare : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_three_ne_zero]
  nlinarith

private theorem sourceTParameter_mul_sqrt_three :
    sourceTParameter * Real.sqrt 3 = 1 := by
  unfold sourceTParameter
  field_simp [sqrt_three_ne_zero]

private theorem sourceTParameter_complex_eq_inv_sqrt_three :
    (sourceTParameter : Complex) = (Real.sqrt 3 : Complex)⁻¹ := by
  have hsqrt_three_ne : (Real.sqrt 3 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_three_ne_zero
  have hparameter :
      (sourceTParameter : Complex) * (Real.sqrt 3 : Complex) = 1 := by
    exact_mod_cast sourceTParameter_mul_sqrt_three
  calc
    (sourceTParameter : Complex) =
        (sourceTParameter : Complex) * 1 := by ring
    _ = (sourceTParameter : Complex) *
        ((Real.sqrt 3 : Complex) * (Real.sqrt 3 : Complex)⁻¹) := by
      rw [mul_inv_cancel₀ hsqrt_three_ne, mul_one]
    _ = ((sourceTParameter : Complex) * (Real.sqrt 3 : Complex)) *
        (Real.sqrt 3 : Complex)⁻¹ := by ring
    _ = (Real.sqrt 3 : Complex)⁻¹ := by
      rw [hparameter, one_mul]

theorem sourceTCos_sq : sourceTCos ^ 2 = (1 + sourceTParameter) / 2 := by
  unfold sourceTCos
  rw [Real.sq_sqrt]
  nlinarith [sourceTParameter_nonneg]

theorem sourceTCos_pos : 0 < sourceTCos := by
  unfold sourceTCos
  apply Real.sqrt_pos.2
  nlinarith [sourceTParameter_nonneg]

private theorem sourceTCos_ne_zero : sourceTCos ≠ 0 :=
  sourceTCos_pos.ne'

theorem sourceTSin_mul_sourceTCos :
    sourceTSin * sourceTCos = sourceTParameter / Real.sqrt 2 := by
  unfold sourceTSin
  field_simp [sourceTCos_ne_zero, sqrt_two_pos.ne']

theorem sourceTSin_sq : sourceTSin ^ 2 = (1 - sourceTParameter) / 2 := by
  have hcos := sourceTCos_sq
  have hparameter := sourceTParameter_sq
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [sqrt_two_mul_self]
  unfold sourceTSin
  field_simp [sourceTCos_ne_zero, sqrt_two_pos.ne']
  rw [hsqrt, hcos]
  nlinarith

theorem sourceTSin_nonneg : 0 ≤ sourceTSin := by
  unfold sourceTSin
  apply div_nonneg sourceTParameter_nonneg
  exact mul_nonneg (le_of_lt sqrt_two_pos) (le_of_lt sourceTCos_pos)

theorem sourceTCos_sq_add_sourceTSin_sq :
    sourceTCos ^ 2 + sourceTSin ^ 2 = 1 := by
  rw [sourceTCos_sq, sourceTSin_sq]
  ring

/-- The phase `exp(i pi/4)` in the concrete amplitude convention. -/
theorem phaseAmplitude_pi_div_four :
    phaseAmplitude (Real.pi / 4) =
      (Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((Real.pi / 4 : Real) : Complex) * Complex.I) =
        (Real.cos (Real.pi / 4) : Complex) +
          (Real.sin (Real.pi / 4) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (Real.pi / 4)
    _ = (Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
      rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
      push_cast
      ring

/-- The source BK05 T vector with phase `exp(i pi/4)` on its one coordinate. -/
def sourceTState : QubitSpace :=
  WithLp.toLp 2 fun b =>
    if b = 0 then (sourceTCos : Complex)
    else phaseAmplitude (Real.pi / 4) * (sourceTSin : Complex)

@[simp] theorem sourceTState_apply_zero :
    sourceTState 0 = (sourceTCos : Complex) := by
  simp [sourceTState]

@[simp] theorem sourceTState_apply_one :
    sourceTState 1 =
      phaseAmplitude (Real.pi / 4) * (sourceTSin : Complex) := by
  simp [sourceTState]

theorem sourceTState_inner_self :
    inner Complex sourceTState sourceTState = 1 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, sourceTState_apply_zero, sourceTState_apply_one,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have hsum := sourceTCos_sq_add_sourceTSin_sq
  calc
    (sourceTCos : Complex) * sourceTCos +
        phaseAmplitude (Real.pi / 4) * sourceTSin *
          (star (phaseAmplitude (Real.pi / 4)) * sourceTSin) =
        ((sourceTCos ^ 2 + sourceTSin ^ 2 : Real) : Complex) := by
      calc
        (sourceTCos : Complex) * sourceTCos +
            phaseAmplitude (Real.pi / 4) * sourceTSin *
              (star (phaseAmplitude (Real.pi / 4)) * sourceTSin) =
            (sourceTCos : Complex) * sourceTCos +
              (phaseAmplitude (Real.pi / 4) *
                star (phaseAmplitude (Real.pi / 4))) *
                  (sourceTSin : Complex) * sourceTSin := by ring
        _ = ((sourceTCos ^ 2 + sourceTSin ^ 2 : Real) : Complex) := by
          rw [phaseAmplitude_mul_conj]
          push_cast
          ring
    _ = 1 := by norm_cast

@[simp] theorem sourceTState_norm : ‖sourceTState‖ = 1 := by
  have hinner := sourceTState_inner_self
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖sourceTState‖ ^ 2 = 1 := by
    have hsq_complex : ((‖sourceTState‖ ^ 2 : Real) : Complex) = 1 := by
      simpa using hinner
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg sourceTState]

theorem sourceTState_ne_zero : sourceTState ≠ 0 := by
  intro hzero
  have hnorm := sourceTState_norm
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

noncomputable def sourceTDensity : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero sourceTState sourceTState_ne_zero

@[simp] theorem sourceTDensity_toOperator :
    sourceTDensity.toOperator =
      (InnerProductSpace.rankOne Complex sourceTState sourceTState).toLinearMap := by
  rw [sourceTDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [sourceTState_inner_self]
  simp

private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem sourceTCos_sq_complex :
    (sourceTCos : Complex) * sourceTCos =
      ((1 + sourceTParameter) / 2 : Real) := by
  have h : sourceTCos * sourceTCos = (1 + sourceTParameter) / 2 := by
    simpa [pow_two] using sourceTCos_sq
  exact_mod_cast h

private theorem sourceTSin_sq_complex :
    (sourceTSin : Complex) * sourceTSin =
      ((1 - sourceTParameter) / 2 : Real) := by
  have h : sourceTSin * sourceTSin = (1 - sourceTParameter) / 2 := by
    simpa [pow_two] using sourceTSin_sq
  exact_mod_cast h

private theorem sourceTSin_mul_sourceTCos_complex :
    (sourceTSin : Complex) * sourceTCos =
      (sourceTParameter / Real.sqrt 2 : Real) := by
  exact_mod_cast sourceTSin_mul_sourceTCos

/-- The source amplitude equation `cos (2 beta) = 1 / sqrt 3`. -/
theorem sourceTState_angle_equation :
    sourceTCos ^ 2 - sourceTSin ^ 2 = sourceTParameter := by
  rw [sourceTCos_sq, sourceTSin_sq]
  ring

/-- Two independently prepared source T states in the project register order. -/
noncomputable def sourceTTwoQubitState : TwoQubitSpace :=
  tensorRegisterTransport (sourceTState ⊗ₜ[Complex] sourceTState)

/-- The honest `ZZ`-even Born weight of the source two-copy state. -/
noncomputable def sourceTEvenWeight : Real := zzEvenWeight sourceTTwoQubitState
private theorem tensorRegisterTransport_apply_tmul_coordinate
    (x y : QubitSpace) (bits : Bitstring (Fin 2)) :
    tensorRegisterTransport (x ⊗ₜ[Complex] y) bits =
      x (bits 0) * y (bits 1) := by
  have hinner := tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (x ⊗ₜ[Complex] y)
  change inner Complex
      (tensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
      (tensorRegisterTransport (x ⊗ₜ[Complex] y)) =
    inner Complex
      (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
        EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
      (x ⊗ₜ[Complex] y) at hinner
  rw [tensorRegisterTransport_apply_basis] at hinner
  have hp : pairBitstring (bits 0, bits 1) = bits := by
    simpa only [splitBitstring] using pair_splitBitstring bits
  rw [hp, EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner] at hinner
  exact hinner

private theorem zzEvenProjector_sourceTTwoQubitState_apply
    (a b : Fin 2) :
    zzEvenProjector sourceTTwoQubitState (pairBitstring (a, b)) =
      if a = b then sourceTState a * sourceTState b else 0 := by
  unfold zzEvenProjector
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]
  simp only [WithLp.ofLp_smul, WithLp.ofLp_add]
  change (2 : Complex)⁻¹ *
      (sourceTTwoQubitState.ofLp (pairBitstring (a, b)) +
        (zzOperator sourceTTwoQubitState).ofLp (pairBitstring (a, b))) = _
  have hzz : (zzOperator sourceTTwoQubitState).ofLp (pairBitstring (a, b)) =
      zPhase a * zPhase b * sourceTTwoQubitState.ofLp (pairBitstring (a, b)) := by
    simpa only [pairBitstring_zero, pairBitstring_one] using
      zzOperator_apply sourceTTwoQubitState (pairBitstring (a, b))
  rw [hzz]
  unfold sourceTTwoQubitState
  rw [tensorRegisterTransport_apply_tmul_coordinate]
  by_cases h : a = b
  · subst b
    fin_cases a <;> simp [zPhase] <;> ring
  · fin_cases a <;> fin_cases b <;> simp_all [zPhase]

private theorem sourceTEvenProjection_inner :
    inner Complex (zzEvenProjector sourceTTwoQubitState)
      (zzEvenProjector sourceTTwoQubitState) = (2 / 3 : Complex) := by
  rw [PiLp.inner_apply]
  rw [← Equiv.sum_comp bitstringPairEquiv
    (fun bits => inner Complex ((zzEvenProjector sourceTTwoQubitState).ofLp bits)
      ((zzEvenProjector sourceTTwoQubitState).ofLp bits))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have h00 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (0, 0)) = (sourceTCos : Complex) * sourceTCos := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 0 0
  have h01 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (0, 1)) = 0 := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 0 1
  have h10 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (1, 0)) = 0 := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 1 0
  have h11 : (zzEvenProjector sourceTTwoQubitState).ofLp
      (bitstringPairEquiv (1, 1)) =
        (phaseAmplitude (Real.pi / 4) * sourceTSin) *
          (phaseAmplitude (Real.pi / 4) * sourceTSin) := by
    simpa [bitstringPairEquiv] using zzEvenProjector_sourceTTwoQubitState_apply 1 1
  rw [h00, h01, h10, h11]
  simp only [RCLike.inner_apply, map_zero, zero_mul, add_zero]
  have hfourth : sourceTCos ^ 4 + sourceTSin ^ 4 = 2 / 3 := by
    rw [show sourceTCos ^ 4 = (sourceTCos ^ 2) ^ 2 by ring,
      show sourceTSin ^ 4 = (sourceTSin ^ 2) ^ 2 by ring]
    rw [sourceTCos_sq, sourceTSin_sq]
    ring_nf
    rw [sourceTParameter_sq]
    norm_num
  have hphase : phaseAmplitude (Real.pi / 4) *
      star (phaseAmplitude (Real.pi / 4)) = 1 :=
    phaseAmplitude_mul_conj (Real.pi / 4)
  simp only [map_mul, Complex.conj_ofReal]
  ring_nf
  have hangle : Real.pi * (1 / 4 : Real) = Real.pi / 4 := by ring
  rw [hangle]
  change (sourceTCos : Complex) ^ 4 +
      phaseAmplitude (Real.pi / 4) ^ 2 * (sourceTSin : Complex) ^ 4 *
        star (phaseAmplitude (Real.pi / 4)) ^ 2 = _
  have hphaseSq : phaseAmplitude (Real.pi / 4) ^ 2 *
      star (phaseAmplitude (Real.pi / 4)) ^ 2 = 1 := by
    rw [← mul_pow, hphase]
    norm_num
  calc
    _ = (sourceTCos : Complex) ^ 4 +
        (phaseAmplitude (Real.pi / 4) ^ 2 *
          star (phaseAmplitude (Real.pi / 4)) ^ 2) * sourceTSin ^ 4 := by ring
    _ = ((sourceTCos ^ 4 + sourceTSin ^ 4 : Real) : Complex) := by
      rw [hphaseSq]
      norm_num
    _ = 2 / 3 := by
      calc
        _ = ((2 / 3 : Real) : Complex) := congrArg (fun x : Real => (x : Complex)) hfourth
        _ = 2 / 3 := by norm_num
/-- BK05's honest `ZZ`-even acceptance probability is exactly `2/3`. -/
theorem sourceTEvenWeight_eq_two_thirds : sourceTEvenWeight = 2 / 3 := by
  unfold sourceTEvenWeight zzEvenWeight
  have hinner := sourceTEvenProjection_inner
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hnormC : ((‖zzEvenProjector sourceTTwoQubitState‖ ^ 2 : Real) : Complex) =
      2 / 3 := by
    calc
      _ = (‖zzEvenProjector sourceTTwoQubitState‖ : Complex) ^ 2 :=
        Complex.ofReal_pow _ _
      _ = 2 / 3 := hinner
  have hnormC' : ((‖zzEvenProjector sourceTTwoQubitState‖ ^ 2 : Real) : Complex) =
      ((2 / 3 : Real) : Complex) := by
    calc
      _ = 2 / 3 := hnormC
      _ = ((2 / 3 : Real) : Complex) := by norm_num
  exact_mod_cast hnormC'

private theorem sourceTState_scaled_cross :
    sourceTCos * sourceTSin * Real.sqrt 2 = sourceTParameter := by
  rw [show sourceTCos * sourceTSin = sourceTSin * sourceTCos by ring,
    sourceTSin_mul_sourceTCos]
  field_simp [sqrt_two_pos.ne']

private theorem sourceTState_upper_cross :
    (sourceTCos : Complex) *
        (star (phaseAmplitude (Real.pi / 4)) * sourceTSin) =
      (sourceTParameter / 2 : Real) -
        (sourceTParameter / 2 : Real) * Complex.I := by
  have hphase : star (phaseAmplitude (Real.pi / 4)) =
      (Real.sqrt 2 / 2 : Complex) -
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
    rw [phaseAmplitude_pi_div_four]
    push_cast
    simp
    ring
  have hscaled : (sourceTCos : Complex) * sourceTSin * Real.sqrt 2 =
      sourceTParameter := by
    exact_mod_cast sourceTState_scaled_cross
  rw [hphase]
  calc
    (sourceTCos : Complex) *
        (((Real.sqrt 2 / 2 : Complex) -
          (Real.sqrt 2 / 2 : Complex) * Complex.I) * sourceTSin) =
        ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 -
          ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 *
            Complex.I := by
      push_cast
      ring
    _ = (sourceTParameter / 2 : Real) -
          (sourceTParameter / 2 : Real) * Complex.I := by
      rw [hscaled]
      norm_num

private theorem sourceTState_lower_cross :
    phaseAmplitude (Real.pi / 4) * sourceTSin * sourceTCos =
      (sourceTParameter / 2 : Real) +
        (sourceTParameter / 2 : Real) * Complex.I := by
  have hscaled : (sourceTCos : Complex) * sourceTSin * Real.sqrt 2 =
      sourceTParameter := by
    exact_mod_cast sourceTState_scaled_cross
  rw [phaseAmplitude_pi_div_four]
  calc
    ((Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I) *
          sourceTSin * sourceTCos =
        ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 +
          ((sourceTCos : Complex) * sourceTSin * Real.sqrt 2) / 2 *
            Complex.I := by
      push_cast
      ring
    _ = (sourceTParameter / 2 : Real) +
          (sourceTParameter / 2 : Real) * Complex.I := by
      rw [hscaled]
      norm_num

/--
The concrete BK05 source vector realizes the repository's canonical pure
`tMagicState`, not merely a state with the same norm.
-/
theorem sourceTDensity_eq_tMagicState : sourceTDensity = tMagicState := by
  apply densityOperator_ext_toOperator
  rw [sourceTDensity_toOperator]
  change
    (InnerProductSpace.rankOne Complex sourceTState sourceTState).toLinearMap =
      blochProjector tBloch
  ext psi b
  fin_cases b
  · change
      ((InnerProductSpace.rankOne Complex sourceTState sourceTState) psi) 0 =
        (blochProjector tBloch psi) 0
    rw [InnerProductSpace.rankOne_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, sourceTState_apply_zero, sourceTState_apply_one,
      RCLike.inner_apply, map_mul, Complex.conj_ofReal, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = ((sourceTCos : Complex) * sourceTCos) * psi 0 +
          ((sourceTCos : Complex) *
            (star (phaseAmplitude (Real.pi / 4)) * sourceTSin)) * psi 1 := by
        have hstar :
            (starRingEnd Complex) (phaseAmplitude (Real.pi / 4)) =
              star (phaseAmplitude (Real.pi / 4)) := rfl
        rw [hstar]
        ring
      _ = _ := by
        rw [sourceTCos_sq_complex, sourceTState_upper_cross]
        simp only [blochProjector, LinearMap.smul_apply, LinearMap.add_apply,
          Module.End.one_apply, blochOperator_apply_zero, tBloch,
          PiLp.smul_apply, PiLp.add_apply]
        push_cast
        rw [sourceTParameter_complex_eq_inv_sqrt_three]
        ring
  · change
      ((InnerProductSpace.rankOne Complex sourceTState sourceTState) psi) 1 =
        (blochProjector tBloch psi) 1
    rw [InnerProductSpace.rankOne_apply, PiLp.inner_apply]
    simp only [Fin.sum_univ_two, sourceTState_apply_zero, sourceTState_apply_one,
      RCLike.inner_apply, map_mul, Complex.conj_ofReal, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = (phaseAmplitude (Real.pi / 4) * sourceTSin * sourceTCos) * psi 0 +
          (phaseAmplitude (Real.pi / 4) * star (phaseAmplitude (Real.pi / 4))) *
            ((sourceTSin : Complex) * sourceTSin) * psi 1 := by
        have hstar :
            (starRingEnd Complex) (phaseAmplitude (Real.pi / 4)) =
              star (phaseAmplitude (Real.pi / 4)) := rfl
        rw [hstar]
        ring
      _ = _ := by
        rw [sourceTState_lower_cross, phaseAmplitude_mul_conj,
          sourceTSin_sq_complex]
        simp only [blochProjector, LinearMap.smul_apply, LinearMap.add_apply,
          Module.End.one_apply, blochOperator_apply_one, tBloch,
          PiLp.smul_apply, PiLp.add_apply]
        push_cast
        rw [sourceTParameter_complex_eq_inv_sqrt_three]
        ring

private theorem sourceTEvenWeight_pos : 0 < sourceTEvenWeight := by
  rw [sourceTEvenWeight_eq_two_thirds]
  norm_num

theorem sourceTTwoQubitState_norm : ‖sourceTTwoQubitState‖ = 1 := by
  unfold sourceTTwoQubitState
  change ‖tensorRegisterTransport.toLinearIsometryEquiv
      (sourceTState ⊗ₜ[Complex] sourceTState)‖ = 1
  rw [tensorRegisterTransport.toLinearIsometryEquiv.norm_map,
    TensorProduct.norm_tmul, sourceTState_norm]
  norm_num

/-- The rejected `ZZ`-odd branch has the complementary Born weight. -/
theorem sourceTOddWeight_eq_one_third :
    zzOddWeight sourceTTwoQubitState = 1 / 3 := by
  have hsum := zzWeights_sum_of_normSq_one sourceTTwoQubitState (by
    rw [sourceTTwoQubitState_norm]
    norm_num)
  change sourceTEvenWeight + zzOddWeight sourceTTwoQubitState = 1 at hsum
  rw [sourceTEvenWeight_eq_two_thirds] at hsum
  linarith

private theorem sourceTOddWeight_pos : 0 < zzOddWeight sourceTTwoQubitState := by
  rw [sourceTOddWeight_eq_one_third]
  norm_num

/-- The actual normalized `ZZ`-even conditional state. -/
noncomputable def sourceTEvenBranch : DensityOperator TwoQubitSpace :=
  zzEvenBranchDensity sourceTTwoQubitState sourceTEvenWeight_pos

/-- The actual normalized `ZZ`-odd conditional state that is discarded. -/
noncomputable def sourceTOddBranch : DensityOperator TwoQubitSpace :=
  zzOddBranchDensity sourceTTwoQubitState sourceTOddWeight_pos

/-- The concrete first-qubit state after accepted-branch XOR and discard. -/
noncomputable def sourceTEvenFirstQubit : QubitSpace :=
  zzEvenBranchFirstQubit sourceTTwoQubitState sourceTEvenWeight_pos

private theorem sourceTEvenFirstQubit_apply_zero :
    sourceTEvenFirstQubit 0 =
      (Real.sqrt sourceTEvenWeight : Complex)⁻¹ *
        (sourceTCos : Complex) * sourceTCos := by
  simp [sourceTEvenFirstQubit, zzEvenBranchFirstQubit, zzEvenBranchState,
    sourceTEvenWeight, zzEvenProjector_sourceTTwoQubitState_apply] <;> ring

private theorem phaseAmplitude_pi_div_four_sq :
    phaseAmplitude (Real.pi / 4) * phaseAmplitude (Real.pi / 4) = Complex.I := by
  rw [phaseAmplitude_pi_div_four]
  have hsqrt : (Real.sqrt 2 : Complex) * Real.sqrt 2 = 2 := by
    exact_mod_cast sqrt_two_mul_self
  rw [show (Real.sqrt 2 / 2 : Complex) = Real.sqrt 2 * (2 : Complex)⁻¹ by ring]
  ring_nf
  rw [Complex.I_sq]
  field_simp
  rw [pow_two, hsqrt]
  ring

private theorem sourceTEvenFirstQubit_apply_one :
    sourceTEvenFirstQubit 1 =
      (Real.sqrt sourceTEvenWeight : Complex)⁻¹ * Complex.I *
        (sourceTSin : Complex) * sourceTSin := by
  simp only [sourceTEvenFirstQubit, zzEvenBranchFirstQubit, zzEvenBranchState]
  change (Real.sqrt sourceTEvenWeight : Complex)⁻¹ *
      zzEvenProjector sourceTTwoQubitState
        (pairBitstring (1, controlledXBit 1 0)) = _
  have hprojected : zzEvenProjector sourceTTwoQubitState
      (pairBitstring (1, 1)) =
      (phaseAmplitude (Real.pi / 4) * sourceTSin) *
        (phaseAmplitude (Real.pi / 4) * sourceTSin) := by
    simpa only [sourceTState_apply_one, if_pos rfl, if_true] using
      (zzEvenProjector_sourceTTwoQubitState_apply 1 1)
  rw [controlledXBit_one, flipBit_zero]
  rw [hprojected]
  calc
    _ = (Real.sqrt sourceTEvenWeight : Complex)⁻¹ *
        (phaseAmplitude (Real.pi / 4) * phaseAmplitude (Real.pi / 4)) *
          sourceTSin * sourceTSin := by ring
    _ = _ := by rw [phaseAmplitude_pi_div_four_sq]


private theorem sourceTEvenFirstQubit_phase_ratio :
    (hadamardOperator sourceTEvenFirstQubit) 1 =
      phaseAmplitude (-Real.pi / 6) *
        (hadamardOperator sourceTEvenFirstQubit) 0 := by
  rw [hadamardOperator_apply_one, hadamardOperator_apply_zero,
    sourceTEvenFirstQubit_apply_zero, sourceTEvenFirstQubit_apply_one,
    phaseAmplitude_neg_pi_div_six]
  have hweight_ne : (Real.sqrt sourceTEvenWeight : Complex) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 sourceTEvenWeight_pos).ne'
  have hsqrt_two_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  field_simp [hweight_ne, hsqrt_two_ne, sqrt_three_ne_zero]
  push_cast
  ring_nf
  have hcos : (sourceTCos : Complex) ^ 2 =
      ((1 + sourceTParameter) / 2 : Real) := by
    simpa [pow_two] using sourceTCos_sq_complex
  have hsin : (sourceTSin : Complex) ^ 2 =
      ((1 - sourceTParameter) / 2 : Real) := by
    simpa [pow_two] using sourceTSin_sq_complex
  rw [hcos, hsin]
  ring_nf
  norm_num [sourceTParameter]
  have hsqrt_three_ne : (Real.sqrt 3 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_three_ne_zero
  field_simp [hsqrt_three_ne]
  have hsqrt_three_sq : (Real.sqrt 3 : Complex) ^ 2 = 3 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3))
  ring_nf
  rw [hsqrt_three_sq]
  ring

/-- The explicit global phase extracted from the zero coordinate of the output. -/
noncomputable def sourceTGlobalPhase : Complex :=
  (Real.sqrt 2 : Complex) * (hadamardOperator sourceTEvenFirstQubit) 0

/--
After XOR, discard, and Hadamard, the accepted source state is exactly
`A_{-pi/6}` up to the displayed global phase.
-/
theorem sourceTEvenOutput_global_phase :
    hadamardOperator sourceTEvenFirstQubit =
      sourceTGlobalPhase • phaseState (-Real.pi / 6) := by
  ext b
  fin_cases b
  · change (hadamardOperator sourceTEvenFirstQubit) 0 =
      sourceTGlobalPhase * phaseState (-Real.pi / 6) 0
    rw [phaseState_apply_zero, sourceTGlobalPhase]
    have hsqrt_two_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
      exact_mod_cast sqrt_two_pos.ne'
    field_simp [hsqrt_two_ne]
  · change (hadamardOperator sourceTEvenFirstQubit) 1 =
      sourceTGlobalPhase * phaseState (-Real.pi / 6) 1
    rw [phaseState_apply_one, sourceTGlobalPhase,
      sourceTEvenFirstQubit_phase_ratio]
    have hsqrt_two_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
      exact_mod_cast sqrt_two_pos.ne'
    field_simp [hsqrt_two_ne]

theorem sourceTEvenOutput_norm : ‖hadamardOperator sourceTEvenFirstQubit‖ = 1 := by
  change ‖hadamardTransport.toLinearIsometryEquiv sourceTEvenFirstQubit‖ = 1
  rw [hadamardTransport.toLinearIsometryEquiv.norm_map]
  exact zzEvenBranchFirstQubit_norm sourceTTwoQubitState sourceTEvenWeight_pos

/-- The displayed global phase has unit norm, so it is physically inessential. -/
theorem sourceTGlobalPhase_norm : ‖sourceTGlobalPhase‖ = 1 := by
  have hnorm := congrArg norm sourceTEvenOutput_global_phase
  rw [norm_smul, phaseState_norm] at hnorm
  simpa [sourceTEvenOutput_norm] using hnorm.symm

/-- The accepted branch passed through the existing XOR/discard channel. -/
theorem sourceTEvenBranch_xor_discard :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity sourceTEvenBranch =
      zzEvenBranchFirstDensity sourceTTwoQubitState sourceTEvenWeight_pos := by
  exact secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
    sourceTTwoQubitState sourceTEvenWeight_pos

/-- The next action after a source attempt; rejection consumes no accepted output. -/
inductive SourceTOutcomeAction
  | emitAccepted
  | retryWithFreshPair
deriving DecidableEq

/-- Source-faithful classical handling of the two `ZZ` outcomes. -/
def sourceTOutcomeAction : DistillationOutcome → SourceTOutcomeAction
  | .accepted => .emitAccepted
  | .rejected => .retryWithFreshPair

/--
One source attempt records only the two fresh resources it consumes, its two
normalized conditional branches, and their Born weights. It deliberately does
not encode an eventual retry count or a cyclic phase-retry theorem.
-/
structure SourceTAttempt where
  resourceCount : Nat
  acceptedWeight : Real
  rejectedWeight : Real
  acceptedBranch : DensityOperator TwoQubitSpace
  rejectedBranch : DensityOperator TwoQubitSpace
  weights_sum : acceptedWeight + rejectedWeight = 1

/-- The BK05 two-resource `T` attempt with explicit normalized branches. -/
noncomputable def sourceTAttempt : SourceTAttempt where
  resourceCount := 2
  acceptedWeight := sourceTEvenWeight
  rejectedWeight := zzOddWeight sourceTTwoQubitState
  acceptedBranch := sourceTEvenBranch
  rejectedBranch := sourceTOddBranch
  weights_sum := by
    rw [sourceTEvenWeight_eq_two_thirds, sourceTOddWeight_eq_one_third]
    norm_num

theorem sourceTAttempt_resource_count : sourceTAttempt.resourceCount = 2 := rfl

theorem sourceTAttempt_accepted_weight : sourceTAttempt.acceptedWeight = 2 / 3 :=
  sourceTEvenWeight_eq_two_thirds

theorem sourceTAttempt_rejected_weight : sourceTAttempt.rejectedWeight = 1 / 3 :=
  sourceTOddWeight_eq_one_third

theorem sourceTAttempt_accepted_branch_normalized :
    LinearMap.trace Complex TwoQubitSpace sourceTAttempt.acceptedBranch.toOperator = 1 :=
  sourceTAttempt.acceptedBranch.trace_one

theorem sourceTAttempt_rejected_branch_normalized :
    LinearMap.trace Complex TwoQubitSpace sourceTAttempt.rejectedBranch.toOperator = 1 :=
  sourceTAttempt.rejectedBranch.trace_one

/-- A rejected attempt restarts with a fresh two-resource attempt. -/
theorem sourceTRejected_retries_with_fresh_pair :
    sourceTOutcomeAction .rejected = .retryWithFreshPair := rfl

/-- Acceptance emits the separately proved `-pi/6` output rather than retrying. -/
theorem sourceTAccepted_emits_output :
    sourceTOutcomeAction .accepted = .emitAccepted := rfl
end OneQubitMagic
end Distillation
end QEC

import QEC.Distillation.LowOverheadProtocol.Core.NoisyInput
import QEC.Distillation.Injection.PhaseInjection
/-!
# HH18 one-qubit phase-injection covariance

This route-local bridge consumes the exact one-qubit phase resources from
`HH18NoisyInput` through the existing `PhaseInjection` circuit.  A Pauli-`Z`
resource error shifts the phase-state angle by `pi`.  The visible favorable
outcome needs no correction, while the adverse outcome is corrected by the
Clifford `S†` phase shift.  The resulting ideal and errored vector actions
retain the source-level global scalar already exposed by `oneShotAttempt`.

This module stops at the one-qubit circuit boundary.  It introduces no
multi-qubit protocol, measurement coarse-graining, decoding, or accounting.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace HH18PhaseInjection

open Semantics Semantics.Qubit

/-- The physical phase angle injected by an ideal HH18 `T†` resource. -/
def tInvIdealAngle : Real :=
  -Real.pi / 4

/-- The canonical angle of the Pauli-`Z`-errored HH18 phase resource. -/
def tInvErrorAngle : Real :=
  tInvIdealAngle + Real.pi

private theorem phaseAmplitude_pi :
    OneQubitMagic.phaseAmplitude Real.pi = -1 := by
  unfold OneQubitMagic.phaseAmplitude
  calc
    Complex.exp (((Real.pi : Real) : Complex) * Complex.I) =
        (Real.cos Real.pi : Complex) +
          (Real.sin Real.pi : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I Real.pi
    _ = -1 := by
      rw [Real.cos_pi, Real.sin_pi]
      norm_num

private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- A physical Pauli-`Z` error on a phase state is exactly a `pi` angle shift. -/
theorem pauliZ_phaseState_eq_phaseState_add_pi (theta : Real) :
    pauliZ (OneQubitMagic.phaseState theta) =
      OneQubitMagic.phaseState (theta + Real.pi) := by
  ext bit
  fin_cases bit
  · simp
  · change (pauliZ (OneQubitMagic.phaseState theta)) 1 =
      (OneQubitMagic.phaseState (theta + Real.pi)) 1
    rw [pauliZ_apply, OneQubitMagic.phaseState_apply_one,
      OneQubitMagic.phaseState_apply_one]
    simp only [zPhase_one]
    rw [OneQubitMagic.phaseAmplitude_add, phaseAmplitude_pi]
    ring

/-- The selected nonzero HH18 error branch is the canonical shifted phase state. -/
theorem tInvErrorResourceState_eq_phaseState :
    HH18NoisyInput.tInvResourceErrorState 1 =
      OneQubitMagic.phaseState tInvErrorAngle := by
  simpa [HH18NoisyInput.tInvResourceErrorState,
    HH18NoisyInput.idealTInvResourceState, tInvErrorAngle, tInvIdealAngle]
    using pauliZ_phaseState_eq_phaseState_add_pi (-Real.pi / 4)

/-- The selected nonzero HH18 error density is the canonical shifted phase density. -/
theorem tInvErrorResourceDensity_eq_phaseStateDensity :
    HH18NoisyInput.tInvResourceErrorDensity 1 =
      OneQubitMagic.phaseStateDensity tInvErrorAngle := by
  apply densityOperator_ext_toOperator
  rw [HH18NoisyInput.tInvResourceErrorDensity,
    DensityOperator.pureOfNonzero_toOperator,
    tInvErrorResourceState_eq_phaseState,
    OneQubitMagic.phaseStateDensity_toOperator]
  rw [OneQubitMagic.phaseState_inner_self]
  simp

/-- The ideal injection use consumes the exact zero-error HH18 resource density. -/
@[simp] theorem idealTInvResourceUse_resource :
    (PhaseInjection.phaseStateResourceUse tInvIdealAngle).resource =
      HH18NoisyInput.tInvResourceErrorDensity 0 := by
  change OneQubitMagic.phaseStateDensity tInvIdealAngle =
    HH18NoisyInput.tInvResourceErrorDensity 0
  rw [HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity]
  rfl

/-- The errored injection use consumes the exact selected HH18 error density. -/
@[simp] theorem erroredTInvResourceUse_resource :
    (PhaseInjection.phaseStateResourceUse tInvErrorAngle).resource =
      HH18NoisyInput.tInvResourceErrorDensity 1 := by
  change OneQubitMagic.phaseStateDensity tInvErrorAngle =
    HH18NoisyInput.tInvResourceErrorDensity 1
  exact tInvErrorResourceDensity_eq_phaseStateDensity.symm

/-- Running the ideal resource use produces the literal phase-injection input. -/
theorem idealTInvResourceUse_run (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (PhaseInjection.phaseStateResourceUse tInvIdealAngle).run
        (PhaseInjection.sourceInputDensity psi hpsi) =
      PhaseInjection.injectionInputDensity psi tInvIdealAngle hpsi := by
  exact PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
    psi tInvIdealAngle hpsi

/-- Running the errored resource use produces the literal shifted-angle input. -/
theorem erroredTInvResourceUse_run (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (PhaseInjection.phaseStateResourceUse tInvErrorAngle).run
        (PhaseInjection.sourceInputDensity psi hpsi) =
      PhaseInjection.injectionInputDensity psi tInvErrorAngle hpsi := by
  exact PhaseInjection.phaseStateResourceUse_run_eq_injectionInputDensity
    psi tInvErrorAngle hpsi

/-- Outcome-conditioned Clifford correction: identity on the favorable branch,
and `S†` on the adverse branch. -/
def tInvOutcomeCorrection : Bool -> Operator QubitSpace
  | true => 1
  | false => OneQubitMagic.phaseShiftOperator (-Real.pi / 2)

@[simp] theorem tInvOutcomeCorrection_favorable :
    tInvOutcomeCorrection true = 1 :=
  rfl

@[simp] theorem tInvOutcomeCorrection_adverse :
    tInvOutcomeCorrection false =
      OneQubitMagic.phaseShiftOperator (-Real.pi / 2) :=
  rfl

private theorem phaseShiftOperator_add_pi (theta : Real) :
    OneQubitMagic.phaseShiftOperator (theta + Real.pi) =
      pauliZ * OneQubitMagic.phaseShiftOperator theta := by
  ext psi bit
  fin_cases bit
  · simp [Module.End.mul_apply]
  · change (OneQubitMagic.phaseShiftOperator (theta + Real.pi) psi) 1 =
      (pauliZ * OneQubitMagic.phaseShiftOperator theta) psi 1
    rw [OneQubitMagic.phaseShiftOperator_apply_one,
      Module.End.mul_apply, pauliZ_apply,
      OneQubitMagic.phaseShiftOperator_apply_one]
    simp only [zPhase_one]
    rw [OneQubitMagic.phaseAmplitude_add, phaseAmplitude_pi]
    ring

private theorem phaseShiftOperator_add_two_pi_mul_int
    (theta : Real) (k : Int) :
    OneQubitMagic.phaseShiftOperator
        (theta + (2 * Real.pi) * (k : Real)) =
      OneQubitMagic.phaseShiftOperator theta := by
  ext psi bit
  fin_cases bit
  · simp
  · change (OneQubitMagic.phaseShiftOperator
        (theta + (2 * Real.pi) * (k : Real)) psi) 1 =
      (OneQubitMagic.phaseShiftOperator theta psi) 1
    rw [OneQubitMagic.phaseShiftOperator_apply_one,
      OneQubitMagic.phaseShiftOperator_apply_one]
    rw [OneQubitMagic.phaseAmplitude_add,
      OneQubitMagic.phaseAmplitude_two_pi_mul_int]
    ring

private theorem tInvError_phaseShiftOperator :
    OneQubitMagic.phaseShiftOperator tInvErrorAngle =
      pauliZ * OneQubitMagic.phaseShiftOperator tInvIdealAngle := by
  simpa [tInvErrorAngle] using phaseShiftOperator_add_pi tInvIdealAngle

private theorem tInvOutcomeCorrection_adverse_comp_ideal :
    tInvOutcomeCorrection false *
        OneQubitMagic.phaseShiftOperator (-tInvIdealAngle) =
      OneQubitMagic.phaseShiftOperator tInvIdealAngle := by
  rw [tInvOutcomeCorrection_adverse, OneQubitMagic.phaseShiftOperator_add]
  congr 1
  unfold tInvIdealAngle
  ring

private theorem tInvOutcomeCorrection_adverse_comp_error :
    tInvOutcomeCorrection false *
        OneQubitMagic.phaseShiftOperator (-tInvErrorAngle) =
      pauliZ * OneQubitMagic.phaseShiftOperator tInvIdealAngle := by
  rw [tInvOutcomeCorrection_adverse, OneQubitMagic.phaseShiftOperator_add]
  calc
    OneQubitMagic.phaseShiftOperator (-Real.pi / 2 + -tInvErrorAngle) =
        OneQubitMagic.phaseShiftOperator
          (tInvErrorAngle + (2 * Real.pi) * ((-1 : Int) : Real)) := by
      congr 1
      simp [tInvErrorAngle, tInvIdealAngle]
      ring
    _ = OneQubitMagic.phaseShiftOperator tInvErrorAngle :=
      phaseShiftOperator_add_two_pi_mul_int tInvErrorAngle (-1)
    _ = pauliZ * OneQubitMagic.phaseShiftOperator tInvIdealAngle :=
      tInvError_phaseShiftOperator

/-- The visible one-shot ideal-resource branch followed by its correction. -/
noncomputable def correctedIdealTInvAttempt (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  tInvOutcomeCorrection coin
    (PhaseInjection.oneShotAttempt psi tInvIdealAngle hpsi coin)

/-- The visible one-shot errored-resource branch followed by the same correction. -/
noncomputable def correctedErroredTInvAttempt (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  tInvOutcomeCorrection coin
    (PhaseInjection.oneShotAttempt psi tInvErrorAngle hpsi coin)

/-- Both corrected ideal branches implement physical `T†`, retaining only the
existing explicit source-vector global scalar. -/
theorem correctedIdealTInvAttempt_action (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    correctedIdealTInvAttempt psi hpsi coin =
      PhaseInjection.oneShotAttemptGlobalPhase tInvIdealAngle coin •
        OneQubitMagic.phaseShiftOperator tInvIdealAngle psi := by
  unfold correctedIdealTInvAttempt
  rw [PhaseInjection.oneShotAttempt_action]
  cases coin
  · rw [map_smul]
    simp only [PhaseInjection.oneShotAttemptAngle,
      PhaseInjection.observedRetryOutcome, PhaseInjection.sourceOutcomeAngle]
    have happ := LinearMap.congr_fun
      tInvOutcomeCorrection_adverse_comp_ideal psi
    exact congrArg
      (fun state : QubitSpace =>
        PhaseInjection.oneShotAttemptGlobalPhase tInvIdealAngle false • state)
      (by simpa [Module.End.mul_apply] using happ)
  · simp [tInvOutcomeCorrection, PhaseInjection.oneShotAttemptAngle,
      PhaseInjection.observedRetryOutcome, PhaseInjection.sourceOutcomeAngle]

/-- Both corrected errored branches implement a physical data `Z` after the
same ideal `T†` action, retaining only the existing branch scalar. -/
theorem correctedErroredTInvAttempt_action (psi : QubitSpace)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    correctedErroredTInvAttempt psi hpsi coin =
      PhaseInjection.oneShotAttemptGlobalPhase tInvErrorAngle coin •
        pauliZ (OneQubitMagic.phaseShiftOperator tInvIdealAngle psi) := by
  unfold correctedErroredTInvAttempt
  rw [PhaseInjection.oneShotAttempt_action]
  cases coin
  · rw [map_smul]
    simp only [PhaseInjection.oneShotAttemptAngle,
      PhaseInjection.observedRetryOutcome, PhaseInjection.sourceOutcomeAngle]
    have happ := LinearMap.congr_fun
      tInvOutcomeCorrection_adverse_comp_error psi
    exact congrArg
      (fun state : QubitSpace =>
        PhaseInjection.oneShotAttemptGlobalPhase tInvErrorAngle false • state)
      (by simpa [Module.End.mul_apply] using happ)
  · simp only [PhaseInjection.oneShotAttemptAngle,
      PhaseInjection.observedRetryOutcome, PhaseInjection.sourceOutcomeAngle]
    rw [tInvOutcomeCorrection_favorable, Module.End.one_apply]
    have happ := LinearMap.congr_fun tInvError_phaseShiftOperator psi
    exact congrArg
      (fun state : QubitSpace =>
        PhaseInjection.oneShotAttemptGlobalPhase tInvErrorAngle true • state)
      (by simpa [Module.End.mul_apply] using happ)

end HH18PhaseInjection
end Distillation
end QEC

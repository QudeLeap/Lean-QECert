import QEC.Distillation.Universality.AdaptiveIdealClifford
import QEC.Distillation.Universality.OneQubitPhase
import QEC.Distillation.Injection.PhaseRetry
/-!
# Exact phase-state injection

This module records the concrete BK05 one-shot ingredients: an unknown input
is tensored with the supplied phase state, the actual signed \`Z ⊗ Z\`
stabilizer measurement selects an even or odd branch, and the existing XOR
and honest-discard channel removes the measured ancillary qubit. The retry
interface deliberately records only the observed outcome labels and the
finite cyclic walk already proved in \`PhaseRetry\`; it does not install a
success probability, target gate, or resource count as data.

The source support is BK05 \`final.tex:541-579\`, under the registered
\`bk-phase-state-injection\` claim.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace PhaseInjection

open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct

/-- The literal two-qubit input \`ψ ⊗ A_θ\` of the BK05 circuit. -/
noncomputable def injectionInput (psi : QubitSpace) (theta : Real) :
    TwoQubit.TwoQubitSpace :=
  TwoQubit.tensorRegisterTransport
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)

/-- The binary \`Z ⊗ Z\` check, with both \`Z\` support coordinates active. -/
def zzCheck : Binary (Fin 2) :=
  cssZCheck (fun _ : Fin 2 => (1 : ZMod 2))

/-- The single \`Z ⊗ Z\` check commutes with itself, as required by the joint API. -/
theorem zzCheck_commutes : Commutes zzCheck zzCheck :=
  cssZCheck_commutes_cssZCheck _ _

/-- The actual one-check joint measurement used by the one-shot circuit. -/
def zzMeasurement : AdaptiveIdealClifford.JointMeasurement (Fin 2) (Fin 1) where
  checks := fun _ => zzCheck
  commute := by
    intro _ _
    exact zzCheck_commutes

/-- The visible one-check syndrome selecting the \`+1\` parity branch. -/
def positiveSyndrome : JointSyndrome (Fin 1) :=
  fun _ => StabilizerOutcome.positive

/-- The visible one-check syndrome selecting the \`-1\` parity branch. -/
def negativeSyndrome : JointSyndrome (Fin 1) :=
  fun _ => StabilizerOutcome.negative

/-- The literal spectral projector selected by a visible one-shot outcome. -/
def oneShotProjector (outcome : StabilizerOutcome) :
    Operator TwoQubit.TwoQubitSpace :=
  stabilizerProjector zzCheck outcome

/-- The signed-Hermitian semantics of the binary check is the repository ZZ operator. -/
theorem zzCheck_hermitianOperator :
    toHermitianQubitOperator zzCheck = TwoQubit.zzOperator := by
  ext psi bits
  simp [mul_assoc, zzCheck, toHermitianQubitOperator, hermitianPhaseScalar,
    binaryOverlapCount, binaryOverlapSupport, toQubitOperator,
    binaryPhaseScalar, xSupport, zSupport, binarySupport, zSupportPhase,
    TwoQubit.zzOperator, Module.End.mul_apply, Fin.prod_univ_two]

/-- The \`+1\` one-shot projector is the existing even ZZ projector. -/
@[simp] theorem oneShotProjector_positive :
    oneShotProjector StabilizerOutcome.positive = TwoQubit.zzEvenProjector := by
  simp [oneShotProjector, stabilizerProjector, zzCheck_hermitianOperator,
    TwoQubit.zzEvenProjector, StabilizerOutcome.sign]

/-- The \`-1\` one-shot projector is the existing odd ZZ projector. -/
@[simp] theorem oneShotProjector_negative :
    oneShotProjector StabilizerOutcome.negative = TwoQubit.zzOddProjector := by
  simp [oneShotProjector, stabilizerProjector, zzCheck_hermitianOperator,
    TwoQubit.zzOddProjector, StabilizerOutcome.sign] ; module

/-- A one-check joint projector reduces to its selected literal spectral projector. -/
theorem jointProjector_eq_oneShotProjector (outcome : StabilizerOutcome) :
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
        (fun _ => outcome) = oneShotProjector outcome := by
  classical
  simp [zzMeasurement, oneShotProjector, jointStabilizerProjector,
    jointStabilizerFactor]

/-- The actual positive joint-syndrome projector is the existing even projector. -/
theorem jointProjector_positive :
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute positiveSyndrome =
      TwoQubit.zzEvenProjector := by
  calc
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute positiveSyndrome =
        oneShotProjector StabilizerOutcome.positive := by
          exact jointProjector_eq_oneShotProjector StabilizerOutcome.positive
    _ = TwoQubit.zzEvenProjector := oneShotProjector_positive

/-- The actual negative joint-syndrome projector is the existing odd projector. -/
theorem jointProjector_negative :
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute negativeSyndrome =
      TwoQubit.zzOddProjector := by
  calc
    jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute negativeSyndrome =
        oneShotProjector StabilizerOutcome.negative := by
          exact jointProjector_eq_oneShotProjector StabilizerOutcome.negative
    _ = TwoQubit.zzOddProjector := oneShotProjector_negative

/-- The unnormalised branch produced by the actual selected parity projector. -/
def oneShotRawBranch (psi : QubitSpace) (theta : Real)
    (outcome : StabilizerOutcome) : TwoQubit.TwoQubitSpace :=
  oneShotProjector outcome (injectionInput psi theta)

/-- The Born weight computed from the actual unnormalised one-shot branch. -/
def oneShotWeight (psi : QubitSpace) (theta : Real)
    (outcome : StabilizerOutcome) : Real :=
  ‖oneShotRawBranch psi theta outcome‖ ^ 2

/-- The positive raw branch is the existing even-parity branch. -/
theorem oneShotRawBranch_positive (psi : QubitSpace) (theta : Real) :
    oneShotRawBranch psi theta StabilizerOutcome.positive =
      TwoQubit.zzEvenProjector (injectionInput psi theta) := by
  unfold oneShotRawBranch
  rw [oneShotProjector_positive]

/-- The negative raw branch is the existing odd-parity branch. -/
theorem oneShotRawBranch_negative (psi : QubitSpace) (theta : Real) :
    oneShotRawBranch psi theta StabilizerOutcome.negative =
      TwoQubit.zzOddProjector (injectionInput psi theta) := by
  unfold oneShotRawBranch
  rw [oneShotProjector_negative]

/-- The positive one-shot weight is the existing even ZZ Born weight. -/
theorem oneShotWeight_positive (psi : QubitSpace) (theta : Real) :
    oneShotWeight psi theta StabilizerOutcome.positive =
      TwoQubit.zzEvenWeight (injectionInput psi theta) := by
  unfold oneShotWeight
  rw [oneShotRawBranch_positive]
  rfl

/-- The negative one-shot weight is the existing odd ZZ Born weight. -/
theorem oneShotWeight_negative (psi : QubitSpace) (theta : Real) :
    oneShotWeight psi theta StabilizerOutcome.negative =
      TwoQubit.zzOddWeight (injectionInput psi theta) := by
  unfold oneShotWeight
  rw [oneShotRawBranch_negative]
  rfl

/-- The concrete XOR followed by the honest discard of the second qubit. -/
noncomputable def oneShotPostprocess :
    QuantumChannel TwoQubit.TwoQubitSpace QubitSpace :=
  QuantumChannel.comp TwoQubit.secondQubitDiscard
    (QuantumChannel.unitaryConj TwoQubit.xorTransport)

/-- The existing even branch density is processed by the literal XOR/discard channel. -/
theorem oneShotPostprocess_evenBranch
    (psi : TwoQubit.TwoQubitSpace) (h : 0 < TwoQubit.zzEvenWeight psi) :
    oneShotPostprocess.mapDensity (TwoQubit.zzEvenBranchDensity psi h) =
      TwoQubit.zzEvenBranchFirstDensity psi h := by
  simpa [oneShotPostprocess] using
    TwoQubit.secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity psi h

/-- The existing odd branch density is processed by the literal XOR/discard channel. -/
theorem oneShotPostprocess_oddBranch
    (psi : TwoQubit.TwoQubitSpace) (h : 0 < TwoQubit.zzOddWeight psi) :
    oneShotPostprocess.mapDensity (TwoQubit.zzOddBranchDensity psi h) =
      TwoQubit.zzOddBranchFirstDensity psi h := by
  simpa [oneShotPostprocess] using
    TwoQubit.secondQubitDiscard_mapDensity_xor_zzOddBranchDensity psi h

/-- The first-qubit state obtained by the positive branch after XOR and discard. -/
def positiveBranchOutput (psi : QubitSpace) (theta : Real)
    (h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta)) : QubitSpace :=
  TwoQubit.zzEvenBranchFirstQubit (injectionInput psi theta) h

/-- The first-qubit state obtained by the negative branch after XOR and discard. -/
def negativeBranchOutput (psi : QubitSpace) (theta : Real)
    (h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta)) : QubitSpace :=
  TwoQubit.zzOddBranchFirstQubit (injectionInput psi theta) h

/-- The source-level angle selected by an observed parity sign. -/
def sourceOutcomeAngle (theta : Real) : StabilizerOutcome → Real
  | .positive => theta
  | .negative => -theta

/--
The global scalar retained by the source's vector representative of one branch.
It is not circuit data: the observable branch density removes this scalar.
-/
def sourceOutcomeGlobalPhase (theta : Real) : StabilizerOutcome → Complex
  | .positive => 1
  | .negative => OneQubitMagic.phaseAmplitude theta

@[simp] theorem sourceOutcomeAngle_positive (theta : Real) :
    sourceOutcomeAngle theta StabilizerOutcome.positive = theta :=
  rfl

@[simp] theorem sourceOutcomeAngle_negative (theta : Real) :
    sourceOutcomeAngle theta StabilizerOutcome.negative = -theta :=
  rfl

@[simp] theorem sourceOutcomeGlobalPhase_positive (theta : Real) :
    sourceOutcomeGlobalPhase theta StabilizerOutcome.positive = 1 :=
  rfl

@[simp] theorem sourceOutcomeGlobalPhase_negative (theta : Real) :
    sourceOutcomeGlobalPhase theta StabilizerOutcome.negative =
      OneQubitMagic.phaseAmplitude theta :=
  rfl

private theorem injectionInput_apply_coordinate
    (psi : QubitSpace) (theta : Real) (bits : Bitstring (Fin 2)) :
    injectionInput psi theta bits =
      psi (bits 0) * OneQubitMagic.phaseState theta (bits 1) := by
  have hinner := TwoQubit.tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)
  change
    inner Complex
        (TwoQubit.tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
        (TwoQubit.tensorRegisterTransport
          (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)) =
      inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
        (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta) at hinner
  rw [TwoQubit.tensorRegisterTransport_apply_basis] at hinner
  have hp : TwoQubit.pairBitstring (bits 0, bits 1) = bits := by
    simpa only [TwoQubit.splitBitstring] using
      TwoQubit.pair_splitBitstring bits
  rw [hp] at hinner
  rw [EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner

private theorem xorTransport_apply_coordinate
    (state : TwoQubit.TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.xorTransport state bits = state (TwoQubit.xorBitstring bits) := by
  have hinner := TwoQubit.xorTransport.map_inner
    (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
      (TwoQubit.xorBitstring bits)) state
  change
    inner Complex
        (TwoQubit.xorTransport
          (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
            (TwoQubit.xorBitstring bits)))
        (TwoQubit.xorTransport state) =
      inner Complex
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
          (TwoQubit.xorBitstring bits)) state at hinner
  rw [TwoQubit.xorTransport_apply_basis,
    TwoQubit.xorBitstring_involutive] at hinner
  rw [EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner

private theorem tensorRegisterTransport_apply_tmul_coordinate
    (x y : QubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.tensorRegisterTransport (x ⊗ₜ[Complex] y) bits =
      x (bits 0) * y (bits 1) := by
  have hinner := TwoQubit.tensorRegisterTransport.map_inner
    (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
      EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
    (x ⊗ₜ[Complex] y)
  change
    inner Complex
        (TwoQubit.tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex (bits 1)))
        (TwoQubit.tensorRegisterTransport (x ⊗ₜ[Complex] y)) =
      inner Complex
        (EuclideanSpace.basisFun (Fin 2) Complex (bits 0) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex (bits 1))
        (x ⊗ₜ[Complex] y) at hinner
  rw [TwoQubit.tensorRegisterTransport_apply_basis] at hinner
  have hp : TwoQubit.pairBitstring (bits 0, bits 1) = bits := by
    simpa only [TwoQubit.splitBitstring] using
      TwoQubit.pair_splitBitstring bits
  rw [hp] at hinner
  rw [EuclideanSpace.basisFun_inner, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_inner,
    EuclideanSpace.basisFun_inner] at hinner
  exact hinner

private theorem zzEvenProjector_apply_coordinate
    (state : TwoQubit.TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.zzEvenProjector state bits =
      if bits 0 = bits 1 then state bits else 0 := by
  unfold TwoQubit.zzEvenProjector
  change (2 : Complex)⁻¹ * (state bits + TwoQubit.zzOperator state bits) = _
  rw [TwoQubit.zzOperator_apply]
  by_cases hbits : bits 0 = bits 1
  · simp only [if_pos hbits]
    rw [hbits, zPhase_sq]
    calc
      (2 : Complex)⁻¹ * (state bits + 1 * state bits) =
          ((2 : Complex)⁻¹ * 2) * state bits := by ring
      _ = state bits := by norm_num
  · simp only [if_neg hbits]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at hbits ⊢
      generalize hsecond : bits 1 = secondBit at hbits ⊢
      fin_cases firstBit <;> fin_cases secondBit <;>
        simp_all [zPhase]
    rw [hphase]
    ring

private theorem zzOddProjector_apply_coordinate
    (state : TwoQubit.TwoQubitSpace) (bits : Bitstring (Fin 2)) :
    TwoQubit.zzOddProjector state bits =
      if bits 0 = bits 1 then 0 else state bits := by
  unfold TwoQubit.zzOddProjector
  change (2 : Complex)⁻¹ * (state bits - TwoQubit.zzOperator state bits) = _
  rw [TwoQubit.zzOperator_apply]
  by_cases hbits : bits 0 = bits 1
  · simp only [if_pos hbits]
    rw [hbits, zPhase_sq]
    ring
  · simp only [if_neg hbits]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at hbits ⊢
      generalize hsecond : bits 1 = secondBit at hbits ⊢
      fin_cases firstBit <;> fin_cases secondBit <;>
        simp_all [zPhase]
    rw [hphase]
    calc
      (2 : Complex)⁻¹ * (state bits - (-1) * state bits) =
          ((2 : Complex)⁻¹ * 2) * state bits := by ring
      _ = state bits := by norm_num

private theorem phaseAmplitude_mul_neg_angle (theta : Real) :
    OneQubitMagic.phaseAmplitude theta * OneQubitMagic.phaseAmplitude (-theta) = 1 := by
  rw [← OneQubitMagic.phaseAmplitude_add]
  simp

private theorem zzEvenProjector_injectionInput
    (psi : QubitSpace) (theta : Real) :
    TwoQubit.zzEvenProjector (injectionInput psi theta) =
      (Real.sqrt 2 : Complex)⁻¹ •
        TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 0)) := by
  ext bits
  rw [zzEvenProjector_apply_coordinate, injectionInput_apply_coordinate]
  simp only [PiLp.smul_apply]
  rw [xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  generalize hfirst : bits 0 = firstBit
  generalize hsecond : bits 1 = secondBit
  fin_cases firstBit <;> fin_cases secondBit <;>
    simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit] <;> ring

private theorem zzOddProjector_injectionInput
    (psi : QubitSpace) (theta : Real) :
    TwoQubit.zzOddProjector (injectionInput psi theta) =
      (Real.sqrt 2 : Complex)⁻¹ •
        TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            ((OneQubitMagic.phaseAmplitude theta •
              OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 1)) := by
  ext bits
  rw [zzOddProjector_apply_coordinate, injectionInput_apply_coordinate]
  simp only [PiLp.smul_apply]
  rw [xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  generalize hfirst : bits 0 = firstBit
  generalize hsecond : bits 1 = secondBit
  fin_cases firstBit <;> fin_cases secondBit
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
    ring
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]
    rw [← mul_assoc (OneQubitMagic.phaseAmplitude theta)
      (OneQubitMagic.phaseAmplitude (-theta)) (psi 1),
      phaseAmplitude_mul_neg_angle, one_mul]
    ring
  · simp_all [TwoQubit.xorBitstring, TwoQubit.controlledXBit]

private theorem phaseShiftOperator_norm (theta : Real) (psi : QubitSpace) :
    ‖OneQubitMagic.phaseShiftOperator theta psi‖ = ‖psi‖ := by
  change ‖OneQubitMagic.phaseShiftTransport theta psi‖ = ‖psi‖
  exact (OneQubitMagic.phaseShiftTransport theta).toLinearIsometryEquiv.norm_map psi

private theorem zzEvenProjector_injectionInput_norm
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    ‖TwoQubit.zzEvenProjector (injectionInput psi theta)‖ = (Real.sqrt 2)⁻¹ := by
  rw [zzEvenProjector_injectionInput, norm_smul]
  have hxor :
      ‖TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 0))‖ =
        ‖TwoQubit.tensorRegisterTransport
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)‖ := by
    change
      ‖TwoQubit.xorTransport.toLinearIsometryEquiv
          (TwoQubit.tensorRegisterTransport
            (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 0))‖ = _
    exact TwoQubit.xorTransport.toLinearIsometryEquiv.norm_map _
  have htransport :
      ‖TwoQubit.tensorRegisterTransport
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)‖ =
        ‖OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex 0‖ := by
    change
      ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)‖ = _
    exact TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map _
  rw [hxor, htransport]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg OneQubitMagic.sqrt_two_pos.le, phaseShiftOperator_norm, hpsi]

private theorem zzOddProjector_injectionInput_norm
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    ‖TwoQubit.zzOddProjector (injectionInput psi theta)‖ = (Real.sqrt 2)⁻¹ := by
  rw [zzOddProjector_injectionInput, norm_smul]
  have hxor :
      ‖TwoQubit.xorTransport
          (TwoQubit.tensorRegisterTransport
            ((OneQubitMagic.phaseAmplitude theta •
              OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 1))‖ =
        ‖TwoQubit.tensorRegisterTransport
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)‖ := by
    change
      ‖TwoQubit.xorTransport.toLinearIsometryEquiv
          (TwoQubit.tensorRegisterTransport
            ((OneQubitMagic.phaseAmplitude theta •
              OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
              EuclideanSpace.basisFun (Fin 2) Complex 1))‖ = _
    exact TwoQubit.xorTransport.toLinearIsometryEquiv.norm_map _
  have htransport :
      ‖TwoQubit.tensorRegisterTransport
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)‖ =
        ‖(OneQubitMagic.phaseAmplitude theta •
          OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex 1‖ := by
    change
      ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)‖ = _
    exact TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map _
  rw [hxor, htransport]
  have htarget :
      ‖OneQubitMagic.phaseAmplitude theta •
        OneQubitMagic.phaseShiftOperator (-theta) psi‖ = 1 := by
    rw [norm_smul, OneQubitMagic.phaseAmplitude_norm,
      phaseShiftOperator_norm, hpsi]
    norm_num
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg OneQubitMagic.sqrt_two_pos.le, htarget]

private theorem injectionInput_zzEvenWeight
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    TwoQubit.zzEvenWeight (injectionInput psi theta) = (1 / 2 : Real) := by
  unfold TwoQubit.zzEvenWeight
  rw [zzEvenProjector_injectionInput_norm psi theta hpsi]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := OneQubitMagic.sqrt_two_pos.ne'
  field_simp [hsqrt_ne]
  nlinarith [OneQubitMagic.sqrt_two_mul_self]

private theorem injectionInput_zzOddWeight
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    TwoQubit.zzOddWeight (injectionInput psi theta) = (1 / 2 : Real) := by
  unfold TwoQubit.zzOddWeight
  rw [zzOddProjector_injectionInput_norm psi theta hpsi]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := OneQubitMagic.sqrt_two_pos.ne'
  field_simp [hsqrt_ne]
  nlinarith [OneQubitMagic.sqrt_two_mul_self]

private theorem sqrt_half_mul_sqrt_two :
    Real.sqrt (1 / 2 : Real) * Real.sqrt 2 = 1 := by
  rw [← Real.sqrt_mul (by norm_num : 0 ≤ (1 / 2 : Real))]
  norm_num

private theorem inv_sqrt_half_mul_inv_sqrt_two :
    (Real.sqrt (1 / 2 : Real) : Complex)⁻¹ *
      (Real.sqrt 2 : Complex)⁻¹ = 1 := by
  have hcast :
      (Real.sqrt (1 / 2 : Real) : Complex) *
        (Real.sqrt 2 : Complex) = 1 := by
    exact_mod_cast sqrt_half_mul_sqrt_two
  calc
    (Real.sqrt (1 / 2 : Real) : Complex)⁻¹ *
        (Real.sqrt 2 : Complex)⁻¹ =
      ((Real.sqrt 2 : Complex) *
        (Real.sqrt (1 / 2 : Real) : Complex))⁻¹ :=
      (mul_inv_rev (Real.sqrt 2 : Complex)
        (Real.sqrt (1 / 2 : Real) : Complex)).symm
    _ = ((Real.sqrt (1 / 2 : Real) : Complex) *
        (Real.sqrt 2 : Complex))⁻¹ := by
      rw [mul_comm (Real.sqrt 2 : Complex)
        (Real.sqrt (1 / 2 : Real) : Complex)]
    _ = 1 := by rw [hcast, inv_one]

private theorem zzEvenBranchState_injectionInput
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta)) :
    TwoQubit.zzEvenBranchState (injectionInput psi theta) h =
      TwoQubit.xorTransport
        (TwoQubit.tensorRegisterTransport
          (OneQubitMagic.phaseShiftOperator theta psi ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 0)) := by
  unfold TwoQubit.zzEvenBranchState
  rw [zzEvenProjector_injectionInput,
    injectionInput_zzEvenWeight psi theta hpsi, smul_smul,
    inv_sqrt_half_mul_inv_sqrt_two, one_smul]

private theorem zzOddBranchState_injectionInput
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta)) :
    TwoQubit.zzOddBranchState (injectionInput psi theta) h =
      TwoQubit.xorTransport
        (TwoQubit.tensorRegisterTransport
          ((OneQubitMagic.phaseAmplitude theta •
            OneQubitMagic.phaseShiftOperator (-theta) psi) ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex 1)) := by
  unfold TwoQubit.zzOddBranchState
  rw [zzOddProjector_injectionInput,
    injectionInput_zzOddWeight psi theta hpsi, smul_smul,
    inv_sqrt_half_mul_inv_sqrt_two, one_smul]

private theorem positiveBranchOutput_eq_phaseShift
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta)) :
    positiveBranchOutput psi theta h = OneQubitMagic.phaseShiftOperator theta psi := by
  ext a
  change
    TwoQubit.zzEvenBranchState (injectionInput psi theta) h
        (TwoQubit.pairBitstring (a, TwoQubit.controlledXBit a 0)) =
      OneQubitMagic.phaseShiftOperator theta psi a
  rw [zzEvenBranchState_injectionInput psi theta hpsi h,
    xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  fin_cases a <;> simp [TwoQubit.xorBitstring, TwoQubit.controlledXBit]

private theorem negativeBranchOutput_eq_phaseShift
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1)
    (h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta)) :
    negativeBranchOutput psi theta h =
      OneQubitMagic.phaseAmplitude theta •
        OneQubitMagic.phaseShiftOperator (-theta) psi := by
  ext a
  change
    TwoQubit.zzOddBranchState (injectionInput psi theta) h
        (TwoQubit.pairBitstring (a, TwoQubit.controlledXBit a 1)) =
      (OneQubitMagic.phaseAmplitude theta •
        OneQubitMagic.phaseShiftOperator (-theta) psi) a
  rw [zzOddBranchState_injectionInput psi theta hpsi h,
    xorTransport_apply_coordinate,
    tensorRegisterTransport_apply_tmul_coordinate]
  fin_cases a <;>
    simp [TwoQubit.xorBitstring, TwoQubit.controlledXBit]

/--
The exact one-shot statement, phrased only in terms of states and weights
computed above. It records the two source-required \`1 / 2\` weights and makes
the negative branch's global phase explicit rather than treating it as a
different physical output.
-/
def OneShotCorrect (psi : QubitSpace) (theta : Real) : Prop :=
  ‖psi‖ = 1 →
    oneShotWeight psi theta StabilizerOutcome.positive = (1 / 2 : Real) ∧
      oneShotWeight psi theta StabilizerOutcome.negative = (1 / 2 : Real) ∧
      (∀ h : 0 < TwoQubit.zzEvenWeight (injectionInput psi theta),
        positiveBranchOutput psi theta h =
          sourceOutcomeGlobalPhase theta StabilizerOutcome.positive •
            OneQubitMagic.phaseShiftOperator
              (sourceOutcomeAngle theta StabilizerOutcome.positive) psi) ∧
      ∀ h : 0 < TwoQubit.zzOddWeight (injectionInput psi theta),
        negativeBranchOutput psi theta h =
          sourceOutcomeGlobalPhase theta StabilizerOutcome.negative •
            OneQubitMagic.phaseShiftOperator
              (sourceOutcomeAngle theta StabilizerOutcome.negative) psi

/-- The actual ZZ measurement and XOR/discard branch states satisfy BK05's one-shot equation. -/
theorem oneShotCorrect (psi : QubitSpace) (theta : Real) : OneShotCorrect psi theta := by
  intro hpsi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [oneShotWeight_positive, injectionInput_zzEvenWeight psi theta hpsi]
  · rw [oneShotWeight_negative, injectionInput_zzOddWeight psi theta hpsi]
  · intro h
    simpa [sourceOutcomeGlobalPhase, sourceOutcomeAngle] using
      positiveBranchOutput_eq_phaseShift psi theta hpsi h
  · intro h
    simpa [sourceOutcomeGlobalPhase, sourceOutcomeAngle] using
      negativeBranchOutput_eq_phaseShift psi theta hpsi h

/--
An actual consumption of the supplied phase-state density. The consumer is
the concrete tensor-register transport, so its ledger debit is tied to the
resource passed to the circuit rather than to a numerical claim.
-/
noncomputable def phaseStateResourceUse (theta : Real) :
    AdaptiveIdealClifford.ResourceUse
      (H := QubitSpace) (K := TwoQubit.TwoQubitSpace) (R := QubitSpace) Real where
  token := theta
  resource := OneQubitMagic.phaseStateDensity theta
  consumer := QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport

/-- One attempt's resource ledger is the singleton debit generated by its use. -/
@[simp] theorem phaseStateResourceUse_ledger (theta : Real) :
    (phaseStateResourceUse theta).ledger = {theta} :=
  rfl


private theorem densityOperator_ext_toOperator {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H} (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem injectionInput_norm (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) : ‖injectionInput psi theta‖ = 1 := by
  change ‖TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv
    (psi ⊗ₜ[Complex] OneQubitMagic.phaseState theta)‖ = 1
  rw [TwoQubit.tensorRegisterTransport.toLinearIsometryEquiv.norm_map,
    TensorProduct.norm_tmul, hpsi, OneQubitMagic.phaseState_norm]
  norm_num

/-- The normalized density of the current unknown data qubit. -/
noncomputable def sourceInputDensity (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero psi (by
    intro hz
    rw [hz, norm_zero] at hpsi
    norm_num at hpsi)

/-- The pure density of the literal circuit input `ψ ⊗ A_θ`. -/
noncomputable def injectionInputDensity (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) : DensityOperator TwoQubit.TwoQubitSpace :=
  DensityOperator.pureOfNonzero (injectionInput psi theta) (by
    intro hz
    have hnorm := injectionInput_norm psi theta hpsi
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm)

private theorem sourceInputDensity_toOperator (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (sourceInputDensity psi hpsi).toOperator =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  rw [sourceInputDensity, DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, hpsi]
  norm_num

private theorem injectionInputDensity_toOperator (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) :
    (injectionInputDensity psi theta hpsi).toOperator =
      (InnerProductSpace.rankOne Complex (injectionInput psi theta)
        (injectionInput psi theta)).toLinearMap := by
  rw [injectionInputDensity, DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, injectionInput_norm psi theta hpsi]
  norm_num

/-- Executing the resource-use term gives exactly the density of the literal circuit input. -/
theorem phaseStateResourceUse_run_eq_injectionInputDensity
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) :
    (phaseStateResourceUse theta).run (sourceInputDensity psi hpsi) =
      injectionInputDensity psi theta hpsi := by
  apply densityOperator_ext_toOperator
  rw [AdaptiveIdealClifford.ResourceUse.run_toOperator]
  change (QuantumChannel.unitaryConj TwoQubit.tensorRegisterTransport)
    (DensityOperator.tensorDensity (sourceInputDensity psi hpsi)
      (OneQubitMagic.phaseStateDensity theta)).toOperator = _
  rw [QuantumChannel.unitaryConj_apply,
    DensityOperator.tensorDensity_toOperator,
    sourceInputDensity_toOperator,
    OneQubitMagic.phaseStateDensity_toOperator,
    DensityOperator.tensorMap_rankOne,
    QuditSubsystem.conjOperator_rankOne,
    injectionInputDensity_toOperator]
  rfl

/-- The observed retry label associated with one fair Boolean outcome. -/
def observedRetryOutcome (coin : Bool) : StabilizerOutcome :=
  if coin then StabilizerOutcome.positive else StabilizerOutcome.negative

/-- The corresponding actual one-check syndrome, rather than an assumed sign. -/
def observedRetrySyndrome (coin : Bool) : JointSyndrome (Fin 1) :=
  fun _ => observedRetryOutcome coin

/-- The signed cyclic exponent contributed by a visible parity outcome. -/
def outcomeIncrement {q : Nat} : StabilizerOutcome → ZMod q
  | .positive => 1
  | .negative => -1

/-- The observed parity label has exactly the increment used by \`PhaseRetry\`. -/
theorem outcomeIncrement_observedRetryOutcome {q : Nat} (coin : Bool) :
    outcomeIncrement (q := q) (observedRetryOutcome coin) =
      PhaseRetry.signedIncrement (q := q) coin := by
  cases coin <;> rfl

/-- The visible syndrome trace produced by a finite retry history. -/
def observedRetryHistory (coins : List Bool) : List (JointSyndrome (Fin 1)) :=
  coins.map observedRetrySyndrome

/-- The order-eight target-miss probability supplied by the finite retry theorem. -/
def retryEightMissProbability (blocks : Nat) (start target : ZMod 8) : Real :=
  PhaseRetry.targetMissProbability 8 blocks start target

/-- The order-twelve target-miss probability supplied by the finite retry theorem. -/
def retryTwelveMissProbability (blocks : Nat) (start target : ZMod 12) : Real :=
  PhaseRetry.targetMissProbability 12 blocks start target

/-- The exact finite exponential tail for the \`-π / 4\` phase cycle. -/
theorem retryEightMissProbability_exponential_bound
    (start target : ZMod 8) (blocks : Nat) :
    retryEightMissProbability blocks start target ≤ (255 / 256 : Real) ^ blocks :=
  PhaseRetry.targetMissProbability_eight_exponential_bound start target blocks

/-- The exact finite exponential tail for the \`-π / 6\` phase cycle. -/
theorem retryTwelveMissProbability_exponential_bound
    (start target : ZMod 12) (blocks : Nat) :
    retryTwelveMissProbability blocks start target ≤ (4095 / 4096 : Real) ^ blocks :=
  PhaseRetry.targetMissProbability_twelve_exponential_bound start target blocks

/-- The order-eight finite retry family reaches every requested cyclic target asymptotically. -/
theorem retryEightTargetHit_probability_one (start target : ZMod 8) :
    Filter.Tendsto (fun blocks =>
      PhaseRetry.targetHitProbability 8 blocks start target) Filter.atTop (nhds 1) :=
  PhaseRetry.finiteCyclicRetry_eight_target_hit_probability_one start target

/-- The order-twelve finite retry family reaches every requested cyclic target asymptotically. -/
theorem retryTwelveTargetHit_probability_one (start target : ZMod 12) :
    Filter.Tendsto (fun blocks =>
      PhaseRetry.targetHitProbability 12 blocks start target) Filter.atTop (nhds 1) :=
  PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one start target

/-- The Boolean encoding of the two visible one-shot stabilizer outcomes. -/
def outcomeCoin : StabilizerOutcome → Bool
  | .positive => true
  | .negative => false

/-- The actual joint-instrument weight of the visible retry syndrome. -/
noncomputable def oneShotProjectedWeight (psi : QubitSpace) (theta : Real)
    (coin : Bool) : Real :=
  ‖jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
    (observedRetrySyndrome coin) (injectionInput psi theta)‖ ^ 2

/-- Each actual joint-measurement outcome is a fair Boolean retry increment. -/
theorem oneShotProjectedWeight_fair (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotProjectedWeight psi theta coin = (1 / 2 : Real) := by
  cases coin
  · change ‖jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
      negativeSyndrome (injectionInput psi theta)‖ ^ 2 = (1 / 2 : Real)
    rw [jointProjector_negative]
    simpa [oneShotWeight, oneShotRawBranch] using (oneShotCorrect psi theta hpsi).2.1
  · change ‖jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
      positiveSyndrome (injectionInput psi theta)‖ ^ 2 = (1 / 2 : Real)
    rw [jointProjector_positive]
    simpa [oneShotWeight, oneShotRawBranch] using (oneShotCorrect psi theta hpsi).1


/-- The literal joint-instrument branch on the density produced by the resource use. -/
noncomputable def oneShotInstrumentBranch (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    AdaptiveIdealClifford.RawOutcomeBranch TwoQubit.TwoQubitSpace :=
  zzMeasurement.branch (observedRetrySyndrome coin)
    ((phaseStateResourceUse theta).run (sourceInputDensity psi hpsi))

/-- The actual joint-instrument Born weight of the visible retry syndrome. -/
noncomputable def oneShotMeasurementWeight (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : Real :=
  (oneShotInstrumentBranch psi theta hpsi coin).weight

private theorem oneShotInstrumentBranch_operator_eq_rankOne
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    (zzMeasurement.instrument.branchOperator (observedRetrySyndrome coin)
      (injectionInputDensity psi theta hpsi).toOperator) =
      (InnerProductSpace.rankOne Complex
        (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
          (observedRetrySyndrome coin) (injectionInput psi theta))
        (jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
          (observedRetrySyndrome coin) (injectionInput psi theta))).toLinearMap := by
  change (jointStabilizerInstrument zzMeasurement.checks zzMeasurement.commute).branchOperator _ _ = _
  rw [jointStabilizerInstrument_branchOperator]
  rw [injectionInputDensity_toOperator]
  let P := jointStabilizerProjector zzMeasurement.checks zzMeasurement.commute
    (observedRetrySyndrome coin)
  have hne : injectionInput psi theta ≠ 0 := by
    intro hz
    have hnorm := injectionInput_norm psi theta hpsi
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  have hcomp := DensityOperator.comp_pureOfNonzero_adjoint P
    (injectionInput psi theta) hne
  rw [DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K, injectionInput_norm psi theta hpsi] at hcomp
  norm_num at hcomp
  rw [jointStabilizerProjector_adjoint] at hcomp
  simpa [P, Module.End.mul_eq_comp, LinearMap.comp_assoc] using hcomp

/-- The instrument Born weight is the squared norm of its literal projector branch. -/
theorem oneShotMeasurementWeight_eq_projector_norm_sq
    (psi : QubitSpace) (theta : Real) (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotMeasurementWeight psi theta hpsi coin =
      oneShotProjectedWeight psi theta coin := by
  unfold oneShotMeasurementWeight oneShotInstrumentBranch
  rw [phaseStateResourceUse_run_eq_injectionInputDensity]
  rw [AdaptiveIdealClifford.JointMeasurement.branch_weight]
  unfold FiniteInstrument.bornWeight
  rw [oneShotInstrumentBranch_operator_eq_rankOne]
  rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Each actual joint-measurement outcome is a fair Boolean retry increment. -/
theorem oneShotMeasurementWeight_fair (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotMeasurementWeight psi theta hpsi coin = (1 / 2 : Real) := by
  rw [oneShotMeasurementWeight_eq_projector_norm_sq]
  exact oneShotProjectedWeight_fair psi theta hpsi coin
/-- The concrete postselected state produced by the one-shot circuit. -/
noncomputable def oneShotAttempt (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) : QubitSpace :=
  if coin then
    positiveBranchOutput psi theta
      (by rw [← oneShotWeight_positive, (oneShotCorrect psi theta hpsi).1]; norm_num)
  else
    negativeBranchOutput psi theta
      (by rw [← oneShotWeight_negative, (oneShotCorrect psi theta hpsi).2.1]; norm_num)

/-- The signed phase angle selected by a concrete observed measurement branch. -/
noncomputable def oneShotAttemptAngle (theta : Real) (coin : Bool) : Real :=
  sourceOutcomeAngle theta (observedRetryOutcome coin)

/-- The source-vector global scalar selected by a concrete observed branch. -/
noncomputable def oneShotAttemptGlobalPhase (theta : Real) (coin : Bool) : Complex :=
  sourceOutcomeGlobalPhase theta (observedRetryOutcome coin)

/-- The actual one-shot output is the selected signed phase action. -/
theorem oneShotAttempt_action (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    oneShotAttempt psi theta hpsi coin = oneShotAttemptGlobalPhase theta coin •
      OneQubitMagic.phaseShiftOperator (oneShotAttemptAngle theta coin) psi := by
  cases coin <;>
    simp [oneShotAttempt, oneShotAttemptAngle, oneShotAttemptGlobalPhase,
      observedRetryOutcome, oneShotCorrect psi theta hpsi]

private theorem oneShotAttemptGlobalPhase_norm (theta : Real) (coin : Bool) :
    ‖oneShotAttemptGlobalPhase theta coin‖ = 1 := by
  cases coin <;> simp [oneShotAttemptGlobalPhase, observedRetryOutcome,
    sourceOutcomeGlobalPhase, OneQubitMagic.phaseAmplitude_norm]

/-- Every concrete postselected one-shot output is again normalized. -/
theorem oneShotAttempt_norm (psi : QubitSpace) (theta : Real)
    (hpsi : ‖psi‖ = 1) (coin : Bool) :
    ‖oneShotAttempt psi theta hpsi coin‖ = 1 := by
  rw [oneShotAttempt_action, norm_smul, oneShotAttemptGlobalPhase_norm, one_mul]
  calc
    ‖OneQubitMagic.phaseShiftOperator (oneShotAttemptAngle theta coin) psi‖ = ‖psi‖ := by
      change ‖OneQubitMagic.phaseShiftTransport (oneShotAttemptAngle theta coin) psi‖ = ‖psi‖
      exact (OneQubitMagic.phaseShiftTransport
        (oneShotAttemptAngle theta coin)).toLinearIsometryEquiv.norm_map psi
    _ = 1 := hpsi

/-- Repeated injection recursively reuses the literal one-shot measurement and branch output. -/
noncomputable def repeatedPhaseInjection (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 → QubitSpace
  | [], psi, _ => psi
  | coin :: coins, psi, hpsi =>
      repeatedPhaseInjection theta coins (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)


/-- A single recursive attempt trace carrying both circuit output and consumed-resource ledger. -/
noncomputable def repeatedPhaseInjectionTrace (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 →
      QubitSpace × AdaptiveIdealClifford.ResourceLedger Real
  | [], psi, _ => (psi, AdaptiveIdealClifford.ResourceLedger.empty Real)
  | coin :: coins, psi, hpsi =>
      let tail := repeatedPhaseInjectionTrace theta coins
        (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
      (tail.1, (phaseStateResourceUse theta).ledger + tail.2)

/-- The state component of the resource trace is the existing recursive circuit execution. -/
theorem repeatedPhaseInjectionTrace_output (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionTrace theta coins psi hpsi).1 =
      repeatedPhaseInjection theta coins psi hpsi := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      rw [repeatedPhaseInjectionTrace, repeatedPhaseInjection]
      exact ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
/-- The product of actual conditional Born weights of a concrete retry history. -/
noncomputable def repeatedPhaseInjectionHistoryWeight (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 → Real
  | [], _, _ => 1
  | coin :: coins, psi, hpsi =>
      oneShotMeasurementWeight psi theta hpsi coin *
        repeatedPhaseInjectionHistoryWeight theta coins
          (oneShotAttempt psi theta hpsi coin)
          (oneShotAttempt_norm psi theta hpsi coin)

/-- The concrete fresh-resource measurement trace is uniformly fair. -/
theorem repeatedPhaseInjectionHistoryWeight_uniform (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    repeatedPhaseInjectionHistoryWeight theta coins psi hpsi =
      (1 / 2 : Real) ^ coins.length := by
  induction coins generalizing psi with
  | nil => simp [repeatedPhaseInjectionHistoryWeight]
  | cons coin coins ih =>
      rw [repeatedPhaseInjectionHistoryWeight,
        oneShotMeasurementWeight_fair psi theta hpsi coin]
      rw [ih (oneShotAttempt psi theta hpsi coin) (oneShotAttempt_norm psi theta hpsi coin)]
      simpa only [List.length_cons, pow_succ] using
        (mul_comm (1 / 2 : Real) ((1 / 2 : Real) ^ coins.length))

/-- The cumulative ledger carried by the same recursive execution as the circuit output. -/
noncomputable def repeatedPhaseInjectionLedger (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    AdaptiveIdealClifford.ResourceLedger Real :=
  (repeatedPhaseInjectionTrace theta coins psi hpsi).2

/-- The ledger projection is definitionally the resource component of the concrete trace. -/
theorem repeatedPhaseInjectionTrace_ledger (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionTrace theta coins psi hpsi).2 =
      repeatedPhaseInjectionLedger theta coins psi hpsi :=
  rfl

/-- Each concrete retry trace debits precisely one supplied phase state per attempt. -/
theorem repeatedPhaseInjectionLedger_eq_replicate (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    repeatedPhaseInjectionLedger theta coins psi hpsi =
      Multiset.replicate coins.length theta := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      change {theta} + repeatedPhaseInjectionLedger theta coins
        (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin) =
          Multiset.replicate (coins.length + 1) theta
      rw [ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin), Multiset.replicate_succ]
      rfl


/-- The accumulated signed source angle selected by a visible retry history. -/
noncomputable def phaseInjectionHistoryAngle (theta : Real) : List Bool → Real
  | [] => 0
  | coin :: coins => oneShotAttemptAngle theta coin + phaseInjectionHistoryAngle theta coins

/-- The accumulated global scalar of a visible retry history. -/
noncomputable def phaseInjectionHistoryGlobalPhase (theta : Real) : List Bool → Complex
  | [] => 1
  | coin :: coins =>
      oneShotAttemptGlobalPhase theta coin * phaseInjectionHistoryGlobalPhase theta coins

/-- A repeated concrete circuit implements the signed history angle, up to its explicit global phase. -/
theorem repeatedPhaseInjection_action (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    repeatedPhaseInjection theta coins psi hpsi =
      phaseInjectionHistoryGlobalPhase theta coins •
        OneQubitMagic.phaseShiftOperator (phaseInjectionHistoryAngle theta coins) psi := by
  induction coins generalizing psi with
  | nil => simp [repeatedPhaseInjection, phaseInjectionHistoryAngle,
      phaseInjectionHistoryGlobalPhase]
  | cons coin coins ih =>
      rw [repeatedPhaseInjection]
      rw [ih (oneShotAttempt psi theta hpsi coin) (oneShotAttempt_norm psi theta hpsi coin)]
      rw [oneShotAttempt_action]
      simp only [LinearMap.map_smul, smul_smul]
      rw [← Module.End.mul_apply, OneQubitMagic.phaseShiftOperator_add]
      simp [phaseInjectionHistoryAngle, phaseInjectionHistoryGlobalPhase, add_comm, mul_comm]

/-- The signed integer exponent read from an actual Boolean outcome history. -/
def phaseInjectionHistoryExponent : List Bool → Int
  | [] => 0
  | true :: coins => 1 + phaseInjectionHistoryExponent coins
  | false :: coins => -1 + phaseInjectionHistoryExponent coins

/-- The cyclic retry endpoint is exactly the history exponent modulo the cycle order. -/
theorem phaseInjectionHistory_endpoint (q : Nat) (start : ZMod q) (coins : List Bool) :
    PhaseRetry.endpoint start coins =
      start + (phaseInjectionHistoryExponent coins : ZMod q) := by
  induction coins generalizing start with
  | nil => simp [PhaseRetry.endpoint, phaseInjectionHistoryExponent]
  | cons coin coins ih =>
      cases coin <;>
        simp [PhaseRetry.endpoint, PhaseRetry.signedIncrement,
          phaseInjectionHistoryExponent, ih, add_assoc]

/-- The concrete signed angle is the phase-cycle unit times the integer retry exponent. -/
theorem phaseInjectionHistoryAngle_eq (theta : Real) (coins : List Bool) :
    phaseInjectionHistoryAngle theta coins =
      theta * (phaseInjectionHistoryExponent coins : Real) := by
  induction coins with
  | nil => simp [phaseInjectionHistoryAngle, phaseInjectionHistoryExponent]
  | cons coin coins ih =>
      cases coin <;>
        simp [phaseInjectionHistoryAngle, phaseInjectionHistoryExponent,
          oneShotAttemptAngle, observedRetryOutcome, sourceOutcomeAngle, ih] <;> ring

private theorem phaseAmplitude_neg_two_pi_mul_int (k : Int) :
    OneQubitMagic.phaseAmplitude ((-2 * Real.pi) * (k : Real)) = 1 := by
  unfold OneQubitMagic.phaseAmplitude
  convert Complex.exp_int_mul_two_pi_mul_I (-k) using 1
  all_goals push_cast
  all_goals ring_nf

private theorem phaseShiftOperator_neg_two_pi_mul_int (k : Int) :
    OneQubitMagic.phaseShiftOperator ((-2 * Real.pi) * (k : Real)) =
      (1 : Operator QubitSpace) := by
  ext psi b
  fin_cases b
  · change (OneQubitMagic.phaseShiftOperator ((-2 * Real.pi) * (k : Real)) psi) 0 = psi 0
    rw [OneQubitMagic.phaseShiftOperator_apply_zero]
  · change (OneQubitMagic.phaseShiftOperator ((-2 * Real.pi) * (k : Real)) psi) 1 = psi 1
    rw [OneQubitMagic.phaseShiftOperator_apply_one, phaseAmplitude_neg_two_pi_mul_int]
    ring

/-- The physical phase increment assigned to one step of a `q`-cycle retry. -/
noncomputable def phaseCycleAngle (q : Nat) : Real := (-2 * Real.pi) / q

/-- The target phase action represented by a cyclic residue. -/
noncomputable def phaseCycleTargetAction (q : Nat) (target : ZMod q) :
    Operator QubitSpace :=
  OneQubitMagic.phaseShiftOperator (phaseCycleAngle q * target.val)

/-- A residue hit gives the target phase action, with the `2π` ambiguity discharged in the operator. -/
theorem phaseCycleTargetAction_of_endpoint {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    OneQubitMagic.phaseShiftOperator (phaseInjectionHistoryAngle (phaseCycleAngle q) coins) =
      phaseCycleTargetAction q target := by
  have hcast : (phaseInjectionHistoryExponent coins : ZMod q) = target := by
    rw [phaseInjectionHistory_endpoint] at hendpoint
    simpa using hendpoint
  have hzero : ((phaseInjectionHistoryExponent coins - target.val : Int) : ZMod q) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, hcast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (phaseInjectionHistoryExponent coins - target.val) q).mp hzero
  rw [phaseInjectionHistoryAngle_eq]
  have hrealInt : phaseInjectionHistoryExponent coins = target.val + q * k := by
    linarith
  have hreal : (phaseInjectionHistoryExponent coins : Real) = target.val + q * k := by
    exact_mod_cast hrealInt
  rw [hreal]
  change OneQubitMagic.phaseShiftOperator (((-2 * Real.pi) / q) *
    (target.val + q * k)) = _
  have hq : (q : Real) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  rw [show ((-2 * Real.pi) / (q : Real)) *
      ((target.val : Real) + (q : Real) * (k : Real)) =
        ((-2 * Real.pi) / (q : Real)) * target.val +
          (-2 * Real.pi) * (k : Real) by
        field_simp [hq]
        ring]
  rw [← OneQubitMagic.phaseShiftOperator_add,
    phaseShiftOperator_neg_two_pi_mul_int]
  simp [phaseCycleTargetAction, phaseCycleAngle]

/-- A concrete retry endpoint realizes the corresponding target phase action. -/
theorem repeatedPhaseInjection_target_of_endpoint {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    repeatedPhaseInjection (phaseCycleAngle q) coins psi hpsi =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) coins •
        phaseCycleTargetAction q target psi := by
  rw [repeatedPhaseInjection_action,
    phaseCycleTargetAction_of_endpoint coins target hendpoint]

/-- The output component of a resource-carrying trace realizes a residue hit as a target action. -/
theorem repeatedPhaseInjectionTrace_target_of_endpoint {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod q) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle q) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) coins •
        phaseCycleTargetAction q target psi := by
  rw [repeatedPhaseInjectionTrace_output]
  exact repeatedPhaseInjection_target_of_endpoint coins target psi hpsi hendpoint

private theorem visitsTarget_exists_prefix {q : Nat} {start target : ZMod q}
    {coins : List Bool} (hvisit : PhaseRetry.visitsTarget start target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      PhaseRetry.endpoint start initial = target := by
  induction coins generalizing start with
  | nil =>
      refine ⟨[], [], by rfl, ?_⟩
      unfold PhaseRetry.visitsTarget at hvisit
      change target ∈ [start] at hvisit
      rw [List.mem_singleton] at hvisit
      simpa [PhaseRetry.endpoint] using hvisit.symm
  | cons coin coins ih =>
      unfold PhaseRetry.visitsTarget at hvisit
      change target ∈ start :: PhaseRetry.positions
        (start + PhaseRetry.signedIncrement coin) coins at hvisit
      simp only [List.mem_cons] at hvisit
      rcases hvisit with hstart | hrest
      · refine ⟨[], coin :: coins, by rfl, ?_⟩
        simpa [PhaseRetry.endpoint] using hstart.symm
      · obtain ⟨initial, suffix, hsplit, hendpoint⟩ :=
          ih (start := start + PhaseRetry.signedIncrement coin) hrest
        refine ⟨coin :: initial, suffix, ?_, ?_⟩
        · simp [hsplit]
        · simpa [PhaseRetry.endpoint] using hendpoint

/-- An actual cyclic target visit exposes a concrete resource-trace prefix with that target action. -/
theorem phaseInjectionTrace_visitsTarget_action {q : Nat} [NeZero q]
    (coins : List Bool) (target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.visitsTarget (0 : ZMod q) target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      (repeatedPhaseInjectionTrace (phaseCycleAngle q) initial psi hpsi).1 =
        phaseInjectionHistoryGlobalPhase (phaseCycleAngle q) initial •
          phaseCycleTargetAction q target psi := by
  obtain ⟨initial, suffix, hsplit, hendpoint⟩ := visitsTarget_exists_prefix hvisit
  refine ⟨initial, suffix, hsplit, ?_⟩
  exact repeatedPhaseInjectionTrace_target_of_endpoint initial target psi hpsi hendpoint

/-- The order-eight retry increment is the `-π / 4` phase-cycle increment. -/
theorem phaseCycleAngle_eight : phaseCycleAngle 8 = -Real.pi / 4 := by
  norm_num [phaseCycleAngle]
  ring

/-- The order-twelve retry increment is the `-π / 6` phase-cycle increment. -/
theorem phaseCycleAngle_twelve : phaseCycleAngle 12 = -Real.pi / 6 := by
  norm_num [phaseCycleAngle]
  ring

/-- The target action on the order-eight (`-π / 4`) phase cycle. -/
noncomputable def phaseEightTargetAction (target : ZMod 8) : Operator QubitSpace :=
  phaseCycleTargetAction 8 target

/-- The target action on the order-twelve (`-π / 6`) phase cycle. -/
noncomputable def phaseTwelveTargetAction (target : ZMod 12) : Operator QubitSpace :=
  phaseCycleTargetAction 12 target

theorem phaseEightTargetAction_eq (target : ZMod 8) :
    phaseEightTargetAction target =
      OneQubitMagic.phaseShiftOperator ((-Real.pi / 4) * target.val) := by
  rw [phaseEightTargetAction, phaseCycleTargetAction, phaseCycleAngle_eight]

theorem phaseTwelveTargetAction_eq (target : ZMod 12) :
    phaseTwelveTargetAction target =
      OneQubitMagic.phaseShiftOperator ((-Real.pi / 6) * target.val) := by
  rw [phaseTwelveTargetAction, phaseCycleTargetAction, phaseCycleAngle_twelve]

/-- An order-eight endpoint hit realizes its `-π / 4` target action in the concrete trace. -/
theorem repeatedPhaseInjectionTrace_eight_target_of_endpoint
    (coins : List Bool) (target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod 8) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle 8) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle 8) coins •
        phaseEightTargetAction target psi := by
  simpa [phaseEightTargetAction] using
    repeatedPhaseInjectionTrace_target_of_endpoint coins target psi hpsi hendpoint

/-- An order-twelve endpoint hit realizes its `-π / 6` target action in the concrete trace. -/
theorem repeatedPhaseInjectionTrace_twelve_target_of_endpoint
    (coins : List Bool) (target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hendpoint : PhaseRetry.endpoint (0 : ZMod 12) coins = target) :
    (repeatedPhaseInjectionTrace (phaseCycleAngle 12) coins psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle 12) coins •
        phaseTwelveTargetAction target psi := by
  simpa [phaseTwelveTargetAction] using
    repeatedPhaseInjectionTrace_target_of_endpoint coins target psi hpsi hendpoint

/-- An order-eight target visit exposes a concrete `-π / 4` trace prefix with its target action. -/
theorem phaseInjectionTrace_eight_visitsTarget_action
    (coins : List Bool) (target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.visitsTarget (0 : ZMod 8) target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      (repeatedPhaseInjectionTrace (phaseCycleAngle 8) initial psi hpsi).1 =
        phaseInjectionHistoryGlobalPhase (phaseCycleAngle 8) initial •
          phaseEightTargetAction target psi := by
  obtain ⟨initial, suffix, hsplit, haction⟩ :=
    phaseInjectionTrace_visitsTarget_action coins target psi hpsi hvisit
  exact ⟨initial, suffix, hsplit, by simpa [phaseEightTargetAction] using haction⟩

/-- An order-twelve target visit exposes a concrete `-π / 6` trace prefix with its target action. -/
theorem phaseInjectionTrace_twelve_visitsTarget_action
    (coins : List Bool) (target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.visitsTarget (0 : ZMod 12) target coins) :
    ∃ initial suffix, coins = initial ++ suffix ∧
      (repeatedPhaseInjectionTrace (phaseCycleAngle 12) initial psi hpsi).1 =
        phaseInjectionHistoryGlobalPhase (phaseCycleAngle 12) initial •
          phaseTwelveTargetAction target psi := by
  obtain ⟨initial, suffix, hsplit, haction⟩ :=
    phaseInjectionTrace_visitsTarget_action coins target psi hpsi hvisit
  exact ⟨initial, suffix, hsplit, by simpa [phaseTwelveTargetAction] using haction⟩

/-- One recursive physical history carries output, the concrete resource ledger, and Born mass. -/
noncomputable def repeatedPhaseInjectionPhysicalTrace (theta : Real) :
    (coins : List Bool) → (psi : QubitSpace) → ‖psi‖ = 1 →
      QubitSpace × (AdaptiveIdealClifford.ResourceLedger Real × Real)
  | [], psi, _ => (psi, (AdaptiveIdealClifford.ResourceLedger.empty Real, 1))
  | coin :: coins, psi, hpsi =>
      let tail := repeatedPhaseInjectionPhysicalTrace theta coins
        (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)
      (tail.1, ((phaseStateResourceUse theta).ledger + tail.2.1,
        (oneShotInstrumentBranch psi theta hpsi coin).weight * tail.2.2))

/-- The physical trace output is the concrete retry output. -/
theorem repeatedPhaseInjectionPhysicalTrace_output (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).1 =
      repeatedPhaseInjection theta coins psi hpsi := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      rw [repeatedPhaseInjectionPhysicalTrace, repeatedPhaseInjection]
      exact ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)

/-- The physical trace ledger is the resource ledger of the same retry execution. -/
theorem repeatedPhaseInjectionPhysicalTrace_ledger (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).2.1 =
      repeatedPhaseInjectionLedger theta coins psi hpsi := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      change {theta} +
        (repeatedPhaseInjectionPhysicalTrace theta coins
          (oneShotAttempt psi theta hpsi coin)
          (oneShotAttempt_norm psi theta hpsi coin)).2.1 = _
      rw [ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)]
      rfl

/-- The physical trace mass is the product of the actual instrument Born weights. -/
theorem repeatedPhaseInjectionPhysicalTrace_mass (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    (repeatedPhaseInjectionPhysicalTrace theta coins psi hpsi).2.2 =
      repeatedPhaseInjectionHistoryWeight theta coins psi hpsi := by
  induction coins generalizing psi with
  | nil => rfl
  | cons coin coins ih =>
      change (oneShotInstrumentBranch psi theta hpsi coin).weight *
        (repeatedPhaseInjectionPhysicalTrace theta coins
          (oneShotAttempt psi theta hpsi coin)
          (oneShotAttempt_norm psi theta hpsi coin)).2.2 = _
      rw [ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)]
      rfl

/-- The ordered Boolean outcomes represented by a finite cyclic retry block trace. -/
def retryTraceCoins {q : Nat} :
    (blocks : Nat) → PhaseRetry.BlockTrace q blocks → List Bool
  | 0, _ => []
  | blocks + 1, trace =>
      PhaseRetry.blockCoins (trace 0) ++ retryTraceCoins blocks (fun index => trace index.succ)

/-- Stop a visible retry history immediately on the first target residue. -/
def stoppingHistory {q : Nat} (start target : ZMod q) : List Bool → List Bool
  | [] => []
  | coin :: coins =>
      if start = target then [] else
        coin :: stoppingHistory (start + PhaseRetry.signedIncrement coin) target coins

/-- The finite stopping protocol evaluated on its concrete physical outcome trace. -/
noncomputable def phaseInjectionStoppingTrace {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    QubitSpace × (AdaptiveIdealClifford.ResourceLedger Real × Real) :=
  repeatedPhaseInjectionPhysicalTrace (phaseCycleAngle q)
    (stoppingHistory start target (retryTraceCoins blocks trace)) psi hpsi

/-- The stopped protocol ledger is a projection of its physical one-shot execution trace. -/
noncomputable def phaseInjectionStoppingLedger {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    AdaptiveIdealClifford.ResourceLedger Real :=
  (phaseInjectionStoppingTrace start target trace psi hpsi).2.1

/-- The stopped protocol Born mass is a projection of the same physical trace. -/
noncomputable def phaseInjectionStoppingMass {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : Real :=
  (phaseInjectionStoppingTrace start target trace psi hpsi).2.2

theorem retryTraceCoins_length {q blocks : Nat} (trace : PhaseRetry.BlockTrace q blocks) :
    (retryTraceCoins blocks trace).length = q * blocks := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
      simp only [retryTraceCoins, List.length_append, ih,
        PhaseRetry.blockCoins, List.length_ofFn, Nat.mul_succ]
      exact Nat.add_comm _ _
theorem stoppingHistory_length_le {q : Nat} (start target : ZMod q) (coins : List Bool) :
    (stoppingHistory start target coins).length ≤ coins.length := by
  induction coins generalizing start with
  | nil => simp [stoppingHistory]
  | cons coin coins ih =>
      by_cases htarget : start = target
      · simp [stoppingHistory, htarget]
      · simp [stoppingHistory, htarget,
          ih (start + PhaseRetry.signedIncrement coin)]

/-- A stopped physical protocol consumes at most one phase-state token per available retry step. -/
theorem phaseInjectionStoppingLedger_bound {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ∃ attempts ≤ q * blocks,
      phaseInjectionStoppingLedger start target trace psi hpsi =
        Multiset.replicate attempts (phaseCycleAngle q) := by
  refine ⟨(stoppingHistory start target (retryTraceCoins blocks trace)).length, ?_, ?_⟩
  · calc
      (stoppingHistory start target (retryTraceCoins blocks trace)).length ≤
          (retryTraceCoins blocks trace).length :=
        stoppingHistory_length_le start target (retryTraceCoins blocks trace)
      _ = q * blocks := retryTraceCoins_length trace
  · unfold phaseInjectionStoppingLedger phaseInjectionStoppingTrace
    rw [repeatedPhaseInjectionPhysicalTrace_ledger,
      repeatedPhaseInjectionLedger_eq_replicate]


private theorem retryEndpoint_append {q : Nat} (start : ZMod q)
    (left right : List Bool) :
    PhaseRetry.endpoint start (left ++ right) =
      PhaseRetry.endpoint (PhaseRetry.endpoint start left) right := by
  induction left generalizing start with
  | nil => simp [PhaseRetry.endpoint]
  | cons coin left ih => simp [PhaseRetry.endpoint, ih]

private theorem retryPositions_append {q : Nat} (start : ZMod q)
    (left right : List Bool) :
    PhaseRetry.positions start (left ++ right) =
      PhaseRetry.positions start left ++
        (PhaseRetry.positions (PhaseRetry.endpoint start left) right).tail := by
  induction left generalizing start with
  | nil =>
      cases right with
      | nil => simp [PhaseRetry.positions, PhaseRetry.endpoint]
      | cons coin right => simp [PhaseRetry.positions, PhaseRetry.endpoint]
  | cons coin left ih =>
      simp [PhaseRetry.positions, PhaseRetry.endpoint, ih]

private theorem retryEndpoint_mem_positions {q : Nat} (start : ZMod q)
    (coins : List Bool) :
    PhaseRetry.endpoint start coins ∈ PhaseRetry.positions start coins := by
  induction coins generalizing start with
  | nil => simp [PhaseRetry.endpoint, PhaseRetry.positions]
  | cons coin coins ih =>
      simp [PhaseRetry.endpoint, PhaseRetry.positions, ih]

private theorem retryMemPositions_tail_iff {q : Nat} (start target : ZMod q)
    (coins : List Bool) :
    target ∈ PhaseRetry.positions start coins ↔
      target = start ∨ target ∈ (PhaseRetry.positions start coins).tail := by
  cases coins with
  | nil => simp [PhaseRetry.positions]
  | cons coin coins => simp [PhaseRetry.positions]

private theorem retryVisitsTarget_append_iff {q : Nat} (start target : ZMod q)
    (left right : List Bool) :
    PhaseRetry.visitsTarget start target (left ++ right) ↔
      PhaseRetry.visitsTarget start target left ∨
        PhaseRetry.visitsTarget (PhaseRetry.endpoint start left) target right := by
  unfold PhaseRetry.visitsTarget
  rw [retryPositions_append, List.mem_append]
  constructor
  · rintro (hleft | htail)
    · exact Or.inl hleft
    · right
      exact (retryMemPositions_tail_iff (PhaseRetry.endpoint start left) target right).mpr
        (Or.inr htail)
  · rintro (hleft | hright)
    · exact Or.inl hleft
    · rw [retryMemPositions_tail_iff] at hright
      rcases hright with hendpoint | htail
      · subst target
        exact Or.inl (retryEndpoint_mem_positions start left)
      · exact Or.inr htail


theorem retryTraceVisitsTarget_iff {q blocks : Nat} (start target : ZMod q)
    (trace : PhaseRetry.BlockTrace q blocks) :
    PhaseRetry.traceVisitsTarget start target blocks trace ↔
      PhaseRetry.visitsTarget start target (retryTraceCoins blocks trace) := by
  induction blocks generalizing start with
  | zero =>
      simpa [PhaseRetry.traceVisitsTarget, retryTraceCoins,
        PhaseRetry.visitsTarget, PhaseRetry.positions] using (eq_comm : start = target ↔ target = start)
  | succ blocks ih =>
      change
        (PhaseRetry.visitsTarget start target (PhaseRetry.blockCoins (trace 0)) ∨
          PhaseRetry.traceVisitsTarget
            (PhaseRetry.blockEndpoint start (trace 0)) target blocks
            (fun index => trace index.succ)) ↔
          PhaseRetry.visitsTarget start target
            (PhaseRetry.blockCoins (trace 0) ++
              retryTraceCoins blocks (fun index => trace index.succ))
      rw [retryVisitsTarget_append_iff, ih]
      rfl

private theorem stoppingHistory_eq_self_of_miss {q : Nat}
    (start target : ZMod q) (coins : List Bool)
    (hmiss : ¬ PhaseRetry.visitsTarget start target coins) :
    stoppingHistory start target coins = coins := by
  induction coins generalizing start with
  | nil => rfl
  | cons coin coins ih =>
      have hstart : start ≠ target := by
        intro h
        apply hmiss
        unfold PhaseRetry.visitsTarget
        change target ∈ start :: PhaseRetry.positions
          (start + PhaseRetry.signedIncrement coin) coins
        rw [h]
        exact List.mem_cons_self
      have htail : ¬ PhaseRetry.visitsTarget
          (start + PhaseRetry.signedIncrement coin) target coins := by
        intro h
        apply hmiss
        unfold PhaseRetry.visitsTarget at h ⊢
        change target ∈ start :: PhaseRetry.positions
          (start + PhaseRetry.signedIncrement coin) coins
        exact List.mem_cons_of_mem start h
      simp [stoppingHistory, hstart, ih _ htail]

/-- The miss-event mass of the stopped physical protocol, summed over actual finite traces. -/
noncomputable def phaseInjectionStoppingMissMass {q blocks : Nat}
    (start target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : Real :=
  letI : Fintype (PhaseRetry.TargetMissTrace q blocks start target) :=
    PhaseRetry.targetMissTraceFintype q blocks start target
  ∑ trace : PhaseRetry.TargetMissTrace q blocks start target,
    phaseInjectionStoppingMass start target trace.1 psi hpsi

theorem phaseInjectionStoppingMass_uniform_on_miss {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.TargetMissTrace q blocks start target)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMass start target trace.1 psi hpsi =
      (1 / 2 : Real) ^ (q * blocks) := by
  have hmiss : ¬ PhaseRetry.visitsTarget start target
      (retryTraceCoins blocks trace.1) := by
    intro hvisit
    apply trace.2
    exact (retryTraceVisitsTarget_iff start target trace.1).mpr hvisit
  unfold phaseInjectionStoppingMass phaseInjectionStoppingTrace
  rw [stoppingHistory_eq_self_of_miss start target
    (retryTraceCoins blocks trace.1) hmiss]
  rw [repeatedPhaseInjectionPhysicalTrace_mass,
    repeatedPhaseInjectionHistoryWeight_uniform, retryTraceCoins_length]

private theorem retryBlockTrace_card (q blocks : Nat) :
    Fintype.card (PhaseRetry.BlockTrace q blocks) = 2 ^ (q * blocks) := by
  simp [PhaseRetry.BlockTrace, PhaseRetry.CoinBlock, pow_mul]

/-- The physical finite miss event has exactly the retry-calculus miss probability. -/
theorem phaseInjectionStoppingMissMass_eq_targetMissProbability {q blocks : Nat}
    (start target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi =
      PhaseRetry.targetMissProbability q blocks start target := by
  classical
  letI : Fintype (PhaseRetry.TargetMissTrace q blocks start target) :=
    PhaseRetry.targetMissTraceFintype q blocks start target
  unfold phaseInjectionStoppingMissMass
  simp_rw [phaseInjectionStoppingMass_uniform_on_miss start target]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (Fintype.card (PhaseRetry.TargetMissTrace q blocks start target) : Real) *
      (1 / 2 : Real) ^ (q * blocks) =
    (Fintype.card (PhaseRetry.TargetMissTrace q blocks start target) : Real) /
      Fintype.card (PhaseRetry.BlockTrace q blocks)
  rw [retryBlockTrace_card]
  rw [div_pow]
  norm_num [Nat.cast_pow]
  rw [div_eq_mul_inv]

/-- The stopped physical order-eight protocol inherits the concrete retry tail. -/
theorem phaseInjectionStoppingMissMass_eight_exponential_bound
    (blocks : Nat) (start target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi ≤
      (255 / 256 : Real) ^ blocks := by
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  exact PhaseRetry.targetMissProbability_eight_exponential_bound start target blocks

/-- The stopped physical order-twelve protocol inherits the concrete retry tail. -/
theorem phaseInjectionStoppingMissMass_twelve_exponential_bound
    (blocks : Nat) (start target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi ≤
      (4095 / 4096 : Real) ^ blocks := by
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  exact PhaseRetry.targetMissProbability_twelve_exponential_bound start target blocks

/-- The physical stopped target-hit mass is the complement of its actual miss event. -/
noncomputable def phaseInjectionStoppingHitMass {q blocks : Nat}
    (start target : ZMod q) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : Real :=
  1 - phaseInjectionStoppingMissMass (blocks := blocks) start target psi hpsi

theorem phaseInjectionStoppingHitMass_eight_probability_one
    (start target : ZMod 8) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks) start target psi hpsi)
      Filter.atTop (nhds 1) := by
  convert PhaseRetry.finiteCyclicRetry_eight_target_hit_probability_one start target using 1
  funext blocks
  unfold phaseInjectionStoppingHitMass
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  rfl

theorem phaseInjectionStoppingHitMass_twelve_probability_one
    (start target : ZMod 12) (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    Filter.Tendsto (fun blocks =>
      phaseInjectionStoppingHitMass (blocks := blocks) start target psi hpsi)
      Filter.atTop (nhds 1) := by
  convert PhaseRetry.finiteCyclicRetry_twelve_target_hit_probability_one start target using 1
  funext blocks
  unfold phaseInjectionStoppingHitMass
  rw [phaseInjectionStoppingMissMass_eq_targetMissProbability]
  rfl

private theorem stoppingHistory_endpoint_of_visit {q : Nat}
    (start target : ZMod q) (coins : List Bool)
    (hvisit : PhaseRetry.visitsTarget start target coins) :
    PhaseRetry.endpoint start (stoppingHistory start target coins) = target := by
  induction coins generalizing start with
  | nil =>
      unfold PhaseRetry.visitsTarget at hvisit
      change target ∈ [start] at hvisit
      rw [List.mem_singleton] at hvisit
      simpa [stoppingHistory, PhaseRetry.endpoint] using hvisit.symm
  | cons coin coins ih =>
      by_cases hstart : start = target
      · subst target
        simp [stoppingHistory, PhaseRetry.endpoint]
      · have htail : PhaseRetry.visitsTarget
            (start + PhaseRetry.signedIncrement coin) target coins := by
          unfold PhaseRetry.visitsTarget at hvisit ⊢
          change target ∈ start :: PhaseRetry.positions
            (start + PhaseRetry.signedIncrement coin) coins at hvisit
          rw [List.mem_cons] at hvisit
          rcases hvisit with hhead | htail
          · exact False.elim (hstart hhead.symm)
          · exact htail
        simpa [stoppingHistory, hstart, PhaseRetry.endpoint] using
          ih (start + PhaseRetry.signedIncrement coin) htail

private theorem phaseInjectionHistoryGlobalPhase_norm (theta : Real) (coins : List Bool) :
    ‖phaseInjectionHistoryGlobalPhase theta coins‖ = 1 := by
  induction coins with
  | nil => simp [phaseInjectionHistoryGlobalPhase]
  | cons coin coins ih =>
      rw [phaseInjectionHistoryGlobalPhase, norm_mul,
        oneShotAttemptGlobalPhase_norm, ih]
      norm_num

private theorem phaseInjection_rankOne_global_phase
    (z : Complex) (psi : QubitSpace)
    (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x b
  change ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap x) b =
    ((InnerProductSpace.rankOne Complex psi psi).toLinearMap x) b
  change (inner Complex (z • psi) x) * (z • psi) b =
    (inner Complex psi x) * psi b
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi b) =
        (z * star z) * inner Complex psi x * psi b := by ring
    _ = inner Complex psi x * psi b := by rw [hz]; ring

private theorem phaseInjectionHistoryGlobalPhase_mul_conj
    (theta : Real) (coins : List Bool) :
    phaseInjectionHistoryGlobalPhase theta coins *
      star (phaseInjectionHistoryGlobalPhase theta coins) = 1 := by
  rw [mul_comm]
  change (starRingEnd Complex) (phaseInjectionHistoryGlobalPhase theta coins) *
    phaseInjectionHistoryGlobalPhase theta coins = 1
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
    phaseInjectionHistoryGlobalPhase_norm]
  norm_num

private theorem repeatedPhaseInjection_norm (theta : Real) (coins : List Bool)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ‖repeatedPhaseInjection theta coins psi hpsi‖ = 1 := by
  induction coins generalizing psi with
  | nil => simpa [repeatedPhaseInjection] using hpsi
  | cons coin coins ih =>
      rw [repeatedPhaseInjection]
      exact ih (oneShotAttempt psi theta hpsi coin)
        (oneShotAttempt_norm psi theta hpsi coin)

private theorem phaseCycleTargetAction_norm (q : Nat) (target : ZMod q)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ‖phaseCycleTargetAction q target psi‖ = 1 := by
  calc
    ‖phaseCycleTargetAction q target psi‖ = ‖psi‖ := by
      change ‖OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle q * target.val) psi‖ = ‖psi‖
      exact (OneQubitMagic.phaseShiftTransport
        (phaseCycleAngle q * target.val)).toLinearIsometryEquiv.norm_map psi
    _ = 1 := hpsi

/-- A visited finite block trace stops at the target action on the concrete physical output. -/
theorem phaseInjectionStoppingTrace_output_target_of_visit {q blocks : Nat} [NeZero q]
    (target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget (0 : ZMod q) target blocks trace) :
    (phaseInjectionStoppingTrace (0 : ZMod q) target trace psi hpsi).1 =
      phaseInjectionHistoryGlobalPhase (phaseCycleAngle q)
        (stoppingHistory (0 : ZMod q) target (retryTraceCoins blocks trace)) •
          phaseCycleTargetAction q target psi := by
  unfold phaseInjectionStoppingTrace
  rw [repeatedPhaseInjectionPhysicalTrace_output]
  apply repeatedPhaseInjection_target_of_endpoint
  apply stoppingHistory_endpoint_of_visit
  exact (retryTraceVisitsTarget_iff (0 : ZMod q) target trace).mp hvisit

private theorem phaseInjectionStoppingTrace_output_norm {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) :
    ‖(phaseInjectionStoppingTrace start target trace psi hpsi).1‖ = 1 := by
  unfold phaseInjectionStoppingTrace
  rw [repeatedPhaseInjectionPhysicalTrace_output]
  exact repeatedPhaseInjection_norm _ _ _ hpsi

/-- The normalized output density of the stopped physical phase-injection trace. -/
noncomputable def phaseInjectionStoppingOutputDensity {q blocks : Nat}
    (start target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero (phaseInjectionStoppingTrace start target trace psi hpsi).1
    (by
      intro hzero
      have hnorm := phaseInjectionStoppingTrace_output_norm start target trace psi hpsi
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm)

/-- The density of the exact target phase action. -/
noncomputable def phaseCycleTargetOutputDensity (q : Nat) (target : ZMod q)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1) : DensityOperator QubitSpace :=
  DensityOperator.pureOfNonzero (phaseCycleTargetAction q target psi)
    (by
      intro hzero
      have hnorm := phaseCycleTargetAction_norm q target psi hpsi
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm)

/-- On every actual hit trace, the stopped physical channel has exactly the target output density. -/
theorem phaseInjectionStoppingOutputDensity_target_of_visit {q blocks : Nat} [NeZero q]
    (target : ZMod q) (trace : PhaseRetry.BlockTrace q blocks)
    (psi : QubitSpace) (hpsi : ‖psi‖ = 1)
    (hvisit : PhaseRetry.traceVisitsTarget (0 : ZMod q) target blocks trace) :
    phaseInjectionStoppingOutputDensity (0 : ZMod q) target trace psi hpsi =
      sourceInputDensity (phaseCycleTargetAction q target psi)
        (phaseCycleTargetAction_norm q target psi hpsi) := by
  apply densityOperator_ext_toOperator
  rw [phaseInjectionStoppingOutputDensity,
    DensityOperator.pureOfNonzero_toOperator,
    inner_self_eq_norm_sq_to_K,
    phaseInjectionStoppingTrace_output_norm]
  norm_num
  rw [sourceInputDensity_toOperator]
  rw [phaseInjectionStoppingTrace_output_target_of_visit target trace psi hpsi hvisit]
  exact phaseInjection_rankOne_global_phase _ _
    (phaseInjectionHistoryGlobalPhase_mul_conj _ _)
end PhaseInjection
end Distillation
end QEC

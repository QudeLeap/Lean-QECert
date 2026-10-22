import QEC.Coding.Stabilizer.Measurement
import QEC.Distillation.FifteenQubitH.Code
import QEC.Distillation.Universality.HResourcePhase
import QEC.Distillation.Core.MagicStateProtocol
import QEC.Distillation.Core.TransversalGate
import QEC.Semantics.Entropy.Purification
/-!
# BK15 noisy input

This internal first layer for the Bravyi--Kitaev fifteen-to-one route fixes the
source A-basis input before any syndrome, decoder, recurrence, or protocol
wrapper is introduced.  In particular, the source `A₀` orientation is the
literal `K†`-then-`H` circuit, not the opposite H-resource conversion already
used elsewhere in the library.

The module supplies an actual finite A-basis dephasing channel, the twelve
explicit H/S normalizers of the H-magic orbit, an admissible input-error domain,
and a physical-order fifteen-fold resource product.  The error-word mixture is
kept as a concrete finite density construction for the later instrument layer.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK15
namespace NoisyInput

open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct

universe u v w

attribute [local instance 100] Fintype.ofFinite

private theorem densityOperator_ext
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

private theorem densityOperator_ext_toOperator {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-! ## Source A basis -/

/-- The source conversion in its literal order: first `K†`, then `H`. -/
noncomputable def sourceA0Transport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := phaseTransport.toLinearEquiv.symm.trans
    hadamardTransport.toLinearEquiv
  map_inner := by
    intro x y
    exact (hadamardTransport.map_inner (phaseTransport.symm x)
      (phaseTransport.symm y)).trans (phaseTransport.symm.map_inner x y)

@[simp] theorem sourceA0Transport_apply (psi : QubitSpace) :
    sourceA0Transport psi = hadamardOperator (phaseInverseOperator psi) :=
  rfl

private theorem sourceA0Transport_sourceHState :
    sourceA0Transport sourceHState =
      phaseAmplitude (-Real.pi / 8) • phaseState (Real.pi / 4) := by
  have hproduct :
      phaseAmplitude (-Real.pi / 8) * phaseAmplitude (Real.pi / 4) =
        (Real.cos (Real.pi / 8) : Complex) +
          (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
    rw [← phaseAmplitude_add]
    rw [show -Real.pi / 8 + Real.pi / 4 = Real.pi / 8 by ring]
    exact phaseAmplitude_pi_div_eight
  ext bit
  fin_cases bit
  · change hadamardOperator (phaseInverseOperator sourceHState) 0 =
      phaseAmplitude (-Real.pi / 8) * phaseState (Real.pi / 4) 0
    rw [hadamardOperator_apply_zero, phaseInverseOperator_apply_zero,
      phaseInverseOperator_apply_one, sourceHState_apply_zero,
      sourceHState_apply_one, phaseState_apply_zero,
      phaseAmplitude_neg_pi_div_eight]
    ring
  · change hadamardOperator (phaseInverseOperator sourceHState) 1 =
      phaseAmplitude (-Real.pi / 8) * phaseState (Real.pi / 4) 1
    rw [hadamardOperator_apply_one, phaseInverseOperator_apply_zero,
      phaseInverseOperator_apply_one, sourceHState_apply_zero,
      sourceHState_apply_one, phaseState_apply_one]
    calc
      (Real.sqrt 2 : Complex)⁻¹ *
          ((Real.cos (Real.pi / 8) : Complex) -
            (-Complex.I) * (Real.sin (Real.pi / 8) : Complex)) =
          (Real.sqrt 2 : Complex)⁻¹ *
            (phaseAmplitude (-Real.pi / 8) * phaseAmplitude (Real.pi / 4)) := by
              rw [hproduct]
              ring
      _ = phaseAmplitude (-Real.pi / 8) *
          ((Real.sqrt 2 : Complex)⁻¹ * phaseAmplitude (Real.pi / 4)) := by
            ring

private theorem rankOne_global_phase
    (z : Complex) (psi : QubitSpace) (hz : z * star z = 1) :
    (InnerProductSpace.rankOne Complex (z • psi) (z • psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by
  ext x bit
  change ((InnerProductSpace.rankOne Complex (z • psi) (z • psi)) x).ofLp bit =
    ((InnerProductSpace.rankOne Complex psi psi) x).ofLp bit
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply]
  simp only [PiLp.smul_apply, inner_smul_left, smul_eq_mul]
  calc
    (star z * inner Complex psi x) * (z * psi bit) =
        (z * star z) * inner Complex psi x * psi bit := by ring
    _ = inner Complex psi x * psi bit := by rw [hz]; ring

/-- The actual source `A₀` density produced from the H resource. -/
noncomputable def sourceA0Density : DensityOperator QubitSpace :=
  sourceA0Transport.conjDensity hMagicState

/-- The source-order `K†`-then-`H` preparation is exactly `|A₀⟩`. -/
theorem sourceA0Density_eq_phaseStateDensity :
    sourceA0Density = phaseStateDensity (Real.pi / 4) := by
  rw [sourceA0Density, hMagicState_eq_sourceHDensity]
  apply densityOperator_ext
  rw [UnitaryTransport.conjDensity_toOperator, sourceHDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne, sourceA0Transport_sourceHState,
    phaseStateDensity_toOperator]
  exact rankOne_global_phase (phaseAmplitude (-Real.pi / 8))
    (phaseState (Real.pi / 4)) (phaseAmplitude_mul_conj (-Real.pi / 8))

/-- Pauli `Z` as a self-inverse linear equivalence. -/
def zLinearEquiv : QubitSpace ≃ₗ[Complex] QubitSpace :=
  LinearEquiv.mk pauliZ pauliZ
    (fun psi => by
      have h := LinearMap.congr_fun pauliZ_square psi
      simpa [Module.End.mul_apply] using h)
    (fun psi => by
      have h := LinearMap.congr_fun pauliZ_square psi
      simpa [Module.End.mul_apply] using h)

@[simp] theorem zLinearEquiv_apply (psi : QubitSpace) :
    zLinearEquiv psi = pauliZ psi :=
  rfl

@[simp] theorem zLinearEquiv_symm_apply (psi : QubitSpace) :
    zLinearEquiv.symm psi = pauliZ psi :=
  rfl

private theorem pauliZ_map_inner (psi phi : QubitSpace) :
    inner Complex (pauliZ psi) (pauliZ phi) = inner Complex psi phi := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two, pauliZ_apply, RCLike.inner_apply, map_mul]
  ring_nf
  simp

/-- Pauli `Z` as a proof-relevant unitary transport. -/
def zTransport : UnitaryTransport QubitSpace QubitSpace where
  toLinearEquiv := zLinearEquiv
  map_inner := pauliZ_map_inner

/-- The two source A-basis eigenvectors. -/
def aZeroState : QubitSpace := phaseState (Real.pi / 4)

def aOneState : QubitSpace := zTransport aZeroState

@[simp] theorem aOneState_eq_pauliZ : aOneState = pauliZ aZeroState :=
  rfl

@[simp] theorem aZeroState_norm : ‖aZeroState‖ = 1 := by
  exact phaseState_norm (Real.pi / 4)

@[simp] theorem aOneState_norm : ‖aOneState‖ = 1 := by
  change ‖zTransport.toLinearIsometryEquiv aZeroState‖ = 1
  rw [zTransport.toLinearIsometryEquiv.norm_map, aZeroState_norm]

/-- The actual source `A₀` density. -/
noncomputable def aZeroDensity : DensityOperator QubitSpace := sourceA0Density

theorem aZeroDensity_eq_phaseStateDensity :
    aZeroDensity = phaseStateDensity (Real.pi / 4) :=
  sourceA0Density_eq_phaseStateDensity

/-- The actual source `A₁ = Z A₀` density. -/
noncomputable def aOneDensity : DensityOperator QubitSpace :=
  zTransport.conjDensity aZeroDensity

/-- The `T H` unitary whose computational eigenbasis is the A basis. -/
noncomputable def aBasisTransport : UnitaryTransport QubitSpace QubitSpace :=
  hadamardTransport.trans (phaseShiftTransport (Real.pi / 4))

@[simp] theorem aBasisTransport_basis_zero :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 0) = aZeroState := by
  ext bit
  fin_cases bit
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 0)) 0 =
      phaseState (Real.pi / 4) 0
    rw [phaseShiftOperator_apply_zero, hadamardOperator_apply_zero,
      phaseState_apply_zero]
    simp
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 0)) 1 =
      phaseState (Real.pi / 4) 1
    rw [phaseShiftOperator_apply_one, hadamardOperator_apply_one,
      phaseState_apply_one]
    simp <;> ring

@[simp] theorem aBasisTransport_basis_one :
    aBasisTransport (EuclideanSpace.basisFun (Fin 2) Complex 1) = aOneState := by
  ext bit
  fin_cases bit
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 1)) 0 =
      pauliZ (phaseState (Real.pi / 4)) 0
    rw [phaseShiftOperator_apply_zero, hadamardOperator_apply_zero,
      pauliZ_apply, zPhase, phaseState_apply_zero]
    simp
  · change phaseShiftOperator (Real.pi / 4)
        (hadamardOperator (EuclideanSpace.basisFun (Fin 2) Complex 1)) 1 =
      pauliZ (phaseState (Real.pi / 4)) 1
    rw [phaseShiftOperator_apply_one, hadamardOperator_apply_one,
      pauliZ_apply, zPhase, phaseState_apply_one]
    simp <;> ring

/-- The Hermitian A-basis observable. -/
def aBasisObservable : Operator QubitSpace := aBasisTransport.conjOperator pauliZ

/-- The literal source convention `A = (X + Y) / sqrt(2)`. -/
def sourceAObservable : Operator QubitSpace :=
  (Real.sqrt 2 : Complex)⁻¹ • (pauliX + pauliY)

private theorem inv_sqrt_two_eq_half_sqrt_two :
    (Real.sqrt 2 : Complex)⁻¹ = (Real.sqrt 2 / 2 : Complex) := by
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast sqrt_two_pos.ne'
  have hsqrt_sq :
      (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
    exact_mod_cast sqrt_two_mul_self
  field_simp [hsqrt_ne]
  rw [pow_two, hsqrt_sq]

private theorem phaseAmplitude_pi_div_four_local :
    phaseAmplitude (Real.pi / 4) =
      (Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
  unfold phaseAmplitude
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

private theorem fin2_one_eta (h : 1 < 2) : (⟨1, h⟩ : Fin 2) = 1 := rfl

private theorem phaseShift_pi_div_four_conj_pauliX :
    (phaseShiftTransport (Real.pi / 4)).conjOperator pauliX =
      sourceAObservable := by
  ext psi bit
  rw [UnitaryTransport.conjOperator_apply]
  rw [show (phaseShiftTransport (Real.pi / 4)).toLinearEquiv.symm =
    (phaseShiftLinearEquiv (Real.pi / 4)).symm by rfl]
  rw [phaseShiftLinearEquiv_symm_apply]
  simp only [sourceAObservable, LinearMap.smul_apply, LinearMap.add_apply,
    phaseShiftTransport_apply]
  fin_cases bit
  · simp only [Fin.zero_eta, PiLp.smul_apply, PiLp.add_apply]
    rw [phaseShiftOperator_apply_zero, pauliX_apply]
    simp [flipBit]
    rw [show -(Real.pi / 4) = -Real.pi / 4 by ring,
      phaseAmplitude_neg_pi_div_four, inv_sqrt_two_eq_half_sqrt_two]
    ring
  · simp only [fin2_one_eta, PiLp.smul_apply, PiLp.add_apply]
    rw [phaseShiftOperator_apply_one, pauliX_apply]
    simp [flipBit]
    rw [phaseAmplitude_pi_div_four_local, inv_sqrt_two_eq_half_sqrt_two]
    ring

private theorem trans_conjOperator
    {H K L : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
    (U : UnitaryTransport H K) (V : UnitaryTransport K L) (A : Operator H) :
    (U.trans V).conjOperator A = V.conjOperator (U.conjOperator A) := by
  ext x
  rfl

/-- The transported observable is the literal source `A = (X + Y) / sqrt(2)`. -/
theorem aBasisObservable_eq_sourceAObservable :
    aBasisObservable = sourceAObservable := by
  rw [aBasisObservable, aBasisTransport, trans_conjOperator,
    hadamard_conj_pauliZ, phaseShift_pi_div_four_conj_pauliX]

theorem aBasisObservable_adjoint :
    LinearMap.adjoint aBasisObservable = aBasisObservable := by
  rw [aBasisObservable, UnitaryTransport.conjOperator_adjoint, pauliZ_adjoint]

theorem aBasisObservable_square : aBasisObservable * aBasisObservable = 1 := by
  rw [aBasisObservable, ← UnitaryTransport.conjOperator_mul, pauliZ_square]
  exact aBasisTransport.conjOperator_one

@[simp] theorem aBasisObservable_aZeroState :
    aBasisObservable aZeroState = aZeroState := by
  rw [← aBasisTransport_basis_zero]
  have hz : pauliZ (EuclideanSpace.basisFun (Fin 2) Complex 0) =
      EuclideanSpace.basisFun (Fin 2) Complex 0 := by
    ext bit
    fin_cases bit <;> simp
  rw [aBasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hz]

@[simp] theorem aBasisObservable_aOneState :
    aBasisObservable aOneState = -aOneState := by
  rw [← aBasisTransport_basis_one]
  have hz : pauliZ (EuclideanSpace.basisFun (Fin 2) Complex 1) =
      -(EuclideanSpace.basisFun (Fin 2) Complex 1) := by
    ext bit
    fin_cases bit <;> simp
  rw [aBasisObservable, UnitaryTransport.conjOperator_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [hz, map_neg]

/-- The two literal spectral projectors of the A-basis observable. -/
def aBasisProjector
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) : Operator QubitSpace :=
  (1 / 2 : Complex) • (1 + outcome.sign • aBasisObservable)

theorem aBasisProjector_adjoint
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    LinearMap.adjoint (aBasisProjector outcome) = aBasisProjector outcome := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold aBasisProjector
  apply LinearMap.IsSymmetric.smul
  · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) = (2 : Complex)⁻¹ := by
      rw [map_inv₀]
      have htwo : starRingEnd Complex (2 : Complex) = 2 :=
        map_natCast (starRingEnd Complex) 2
      rw [htwo]
    simpa only [one_div] using hreal
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · apply LinearMap.IsSymmetric.smul
      · cases outcome <;>
          simp [Coding.PauliSymplectic.StabilizerOutcome.sign]
      · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
        exact aBasisObservable_adjoint

theorem aBasisProjector_idempotent
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    aBasisProjector outcome * aBasisProjector outcome = aBasisProjector outcome := by
  cases outcome <;>
    simp only [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign,
      smul_mul_assoc,
      mul_smul_comm, mul_add, add_mul, one_mul, mul_one,
      aBasisObservable_square] <;>
    module

theorem aBasisProjector_add :
    aBasisProjector Coding.PauliSymplectic.StabilizerOutcome.positive +
      aBasisProjector Coding.PauliSymplectic.StabilizerOutcome.negative = 1 := by
  simp only [aBasisProjector, Coding.PauliSymplectic.StabilizerOutcome.sign]
  module

theorem aBasisProjector_isSymmetricProjection
    (outcome : Coding.PauliSymplectic.StabilizerOutcome) :
    (aBasisProjector outcome).IsSymmetricProjection := by
  refine ⟨aBasisProjector_idempotent outcome, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact aBasisProjector_adjoint outcome

private theorem pauliZ_positive_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 + pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 0)
        (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.add_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply] <;>
    ring

private theorem pauliZ_negative_projector_eq_rankOne :
    (1 / 2 : Complex) • (1 - pauliZ) =
      (InnerProductSpace.rankOne Complex
        (EuclideanSpace.basisFun (Fin 2) Complex 1)
        (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap := by
  ext psi bit
  fin_cases bit <;>
    simp [LinearMap.smul_apply, LinearMap.sub_apply, pauliZ_apply, zPhase,
      InnerProductSpace.rankOne_apply, PiLp.inner_apply] <;>
    ring

private theorem aBasisTransport_conj_positive_projector :
    aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 + pauliZ)) =
      aBasisProjector .positive := by
  unfold aBasisProjector
  rw [show Coding.PauliSymplectic.StabilizerOutcome.sign
      Coding.PauliSymplectic.StabilizerOutcome.positive = (1 : Complex) by rfl]
  ext psi
  simp [aBasisObservable, UnitaryTransport.conjOperator,
    map_add, map_smul]

private theorem aBasisTransport_conj_negative_projector :
    aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 - pauliZ)) =
      aBasisProjector .negative := by
  unfold aBasisProjector
  rw [show Coding.PauliSymplectic.StabilizerOutcome.sign
      Coding.PauliSymplectic.StabilizerOutcome.negative = (-1 : Complex) by rfl]
  ext psi
  simp [aBasisObservable, UnitaryTransport.conjOperator,
    map_sub, map_smul]
  ring

private theorem aZeroDensity_toOperator_rankOne :
    aZeroDensity.toOperator =
      (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
  rw [aZeroDensity_eq_phaseStateDensity, phaseStateDensity_toOperator]
  rfl

private theorem aOneDensity_toOperator_rankOne :
    aOneDensity.toOperator =
      (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
  rw [aOneDensity, UnitaryTransport.conjDensity_toOperator,
    aZeroDensity_toOperator_rankOne, QuditSubsystem.conjOperator_rankOne]
  rfl

theorem aBasisProjector_positive_eq_aZeroDensity_toOperator :
    aBasisProjector .positive = aZeroDensity.toOperator := by
  calc
    aBasisProjector .positive =
        aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 + pauliZ)) :=
      aBasisTransport_conj_positive_projector.symm
    _ = aBasisTransport.conjOperator
        ((InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex 0)
          (EuclideanSpace.basisFun (Fin 2) Complex 0)).toLinearMap) := by
      rw [pauliZ_positive_projector_eq_rankOne]
    _ = (InnerProductSpace.rankOne Complex aZeroState aZeroState).toLinearMap := by
      rw [QuditSubsystem.conjOperator_rankOne, aBasisTransport_basis_zero]
    _ = aZeroDensity.toOperator := aZeroDensity_toOperator_rankOne.symm

theorem aBasisProjector_negative_eq_aOneDensity_toOperator :
    aBasisProjector .negative = aOneDensity.toOperator := by
  calc
    aBasisProjector .negative =
        aBasisTransport.conjOperator ((1 / 2 : Complex) • (1 - pauliZ)) :=
      aBasisTransport_conj_negative_projector.symm
    _ = aBasisTransport.conjOperator
        ((InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Fin 2) Complex 1)
          (EuclideanSpace.basisFun (Fin 2) Complex 1)).toLinearMap) := by
      rw [pauliZ_negative_projector_eq_rankOne]
    _ = (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by
      rw [QuditSubsystem.conjOperator_rankOne, aBasisTransport_basis_one]
    _ = aOneDensity.toOperator := aOneDensity_toOperator_rankOne.symm

/-- The projective A-basis measurement with outcome forgotten. -/
def aBasisDephasingKrausFamily :
    FiniteKrausFamily Coding.PauliSymplectic.StabilizerOutcome QubitSpace QubitSpace where
  operator := aBasisProjector

theorem aBasisDephasingKrausFamily_complete :
    aBasisDephasingKrausFamily.Complete := by
  unfold FiniteKrausFamily.Complete
  simp only [aBasisDephasingKrausFamily, aBasisProjector_adjoint]
  change (∑ outcome : Coding.PauliSymplectic.StabilizerOutcome,
    aBasisProjector outcome * aBasisProjector outcome) = 1
  rw [show (Finset.univ : Finset Coding.PauliSymplectic.StabilizerOutcome) =
      {Coding.PauliSymplectic.StabilizerOutcome.positive,
        Coding.PauliSymplectic.StabilizerOutcome.negative} by decide]
  simpa [aBasisProjector_idempotent] using aBasisProjector_add

/-- The actual CPTP A-basis dephasing channel. -/
def aBasisDephasing : QuantumChannel QubitSpace QubitSpace :=
  aBasisDephasingKrausFamily.toQuantumChannel aBasisDephasingKrausFamily_complete

/-- The source A-basis dephasing, expressed as a finite projective channel. -/
theorem aBasisDephasing_apply (A : Operator QubitSpace) :
    aBasisDephasing A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) := by
  rw [aBasisDephasing, FiniteKrausFamily.toQuantumChannel_apply_sum]
  simp only [aBasisDephasingKrausFamily, aBasisProjector_adjoint]
  change (∑ outcome : Coding.PauliSymplectic.StabilizerOutcome,
      aBasisProjector outcome * (A * aBasisProjector outcome)) =
    (1 / 2 : Complex) • (A + aBasisObservable * (A * aBasisObservable))
  rw [show (Finset.univ : Finset Coding.PauliSymplectic.StabilizerOutcome) =
      {Coding.PauliSymplectic.StabilizerOutcome.positive,
        Coding.PauliSymplectic.StabilizerOutcome.negative} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  unfold aBasisProjector
  simp only [Coding.PauliSymplectic.StabilizerOutcome.sign, one_smul,
    smul_mul_assoc, mul_smul_comm,
    mul_add, add_mul, one_mul, mul_one, neg_mul, mul_neg, neg_smul]
  module

/-! ## Finite H/S normalization -/

private theorem transport_trans_conjDensity
    (U V : UnitaryTransport QubitSpace QubitSpace)
    (rho : DensityOperator QubitSpace) :
    (U.trans V).conjDensity rho = V.conjDensity (U.conjDensity rho) := by
  apply densityOperator_ext
  rfl

private def hStep (d : HDirection) : HDirection := hadamardClifford • d

private def sStep (d : HDirection) : HDirection := phaseClifford • d

private theorem hMagicStateOfReference :
    hMagicStateOfDirection hReference = hMagicState := by
  apply densityOperator_ext
  change blochProjector (hBlochOfDirection hReference) = blochProjector hBloch
  congr 1
  funext axis
  fin_cases axis <;>
    norm_num [hReference, hBlochOfDirection, hBloch, signedCoordinateValue]

/-- A literal twelve-entry H/S table, one entry for each signed H direction. -/
noncomputable def hCanonicalizerCandidate : Fin 12 →
    UnitaryTransport QubitSpace QubitSpace
  | 0 => phaseTransport.trans (phaseTransport.trans phaseTransport)
  | 1 => hadamardTransport.trans
      (phaseTransport.trans (phaseTransport.trans
        (hadamardTransport.trans phaseTransport)))
  | 2 => phaseTransport
  | 3 => phaseTransport.trans
      (hadamardTransport.trans (phaseTransport.trans phaseTransport))
  | 4 => UnitaryTransport.identity QubitSpace
  | 5 => hadamardTransport.trans (phaseTransport.trans phaseTransport)
  | 6 => phaseTransport.trans phaseTransport
  | 7 => phaseTransport.trans (phaseTransport.trans
      (hadamardTransport.trans (phaseTransport.trans phaseTransport)))
  | 8 => hadamardTransport.trans phaseTransport
  | 9 => phaseTransport.trans (hadamardTransport.trans phaseTransport)
  | 10 => hadamardTransport.trans (phaseTransport.trans
      (hadamardTransport.trans (phaseTransport.trans phaseTransport)))
  | 11 => phaseTransport.trans
      (phaseTransport.trans (hadamardTransport.trans phaseTransport))

private def hCanonicalizerTarget : Fin 12 → HDirection → HDirection
  | 0 => fun d => sStep (sStep (sStep d))
  | 1 => fun d => sStep (hStep (sStep (sStep (hStep d))))
  | 2 => fun d => sStep d
  | 3 => fun d => sStep (sStep (hStep (sStep d)))
  | 4 => fun d => d
  | 5 => fun d => sStep (sStep (hStep d))
  | 6 => fun d => sStep (sStep d)
  | 7 => fun d => sStep (sStep (hStep (sStep (sStep d))))
  | 8 => fun d => sStep (hStep d)
  | 9 => fun d => sStep (hStep (sStep d))
  | 10 => fun d => sStep (sStep (hStep (sStep (hStep d))))
  | 11 => fun d => sStep (hStep (sStep (sStep d)))

private theorem hCanonicalizerCandidate_conj
    (i : Fin 12) (d : HDirection) :
    (hCanonicalizerCandidate i).conjDensity (hMagicStateOfDirection d) =
      hMagicStateOfDirection (hCanonicalizerTarget i d) := by
  fin_cases i <;>
    simp [hCanonicalizerCandidate, hCanonicalizerTarget, hStep, sStep,
      transport_trans_conjDensity, hadamard_conj_hMagicState,
      phase_conj_hMagicState, UnitaryTransport.identity]
  all_goals rfl

private theorem hCanonicalizerCandidate_complete (d : HDirection) :
    ∃ i : Fin 12, hCanonicalizerTarget i d = hReference := by
  revert d
  native_decide

/-- The chosen member of the explicit twelve-entry table for one H direction. -/
noncomputable def hCanonicalizerIndex (d : HDirection) : Fin 12 :=
  Classical.choose (hCanonicalizerCandidate_complete d)

/-- The actual finite H/S transport sending a chosen direction to the reference. -/
noncomputable def hCanonicalizer (d : HDirection) :
    UnitaryTransport QubitSpace QubitSpace :=
  hCanonicalizerCandidate (hCanonicalizerIndex d)

theorem hCanonicalizer_conj_hMagicState (d : HDirection) :
    (hCanonicalizer d).conjDensity (hMagicStateOfDirection d) = hMagicState := by
  calc
    (hCanonicalizer d).conjDensity (hMagicStateOfDirection d) =
        hMagicStateOfDirection
          (hCanonicalizerTarget (hCanonicalizerIndex d) d) :=
      hCanonicalizerCandidate_conj (hCanonicalizerIndex d) d
    _ = hMagicStateOfDirection hReference := congrArg hMagicStateOfDirection
      (Classical.choose_spec (hCanonicalizerCandidate_complete d))
    _ = hMagicState := hMagicStateOfReference

/-- The observed squared overlap with the reference H direction. -/
def hInputSquaredOverlap (rho : DensityOperator QubitSpace) : Real :=
  projectionSquaredOverlap (hProjector hReference) rho

/-- The corresponding square-root A-basis fidelity. -/
def hInputFidelity (rho : DensityOperator QubitSpace) : Real :=
  hDirectionFidelity rho hReference

/-- The operational input error, defined from the observed reference overlap. -/
def hInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - hInputSquaredOverlap rho

/-- Canonicalize using the maximizing H direction before A-basis dephasing. -/
noncomputable def hCanonicalizedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  (hCanonicalizer (hMaximizingDirection rho)).conjDensity rho

theorem hInputSquaredOverlap_eq_hInputFidelity_sq
    (rho : DensityOperator QubitSpace) :
    hInputSquaredOverlap rho = hInputFidelity rho ^ 2 := by
  unfold hInputSquaredOverlap hInputFidelity hDirectionFidelity projectionFidelity
  rw [Real.sq_sqrt]
  exact projectionSquaredOverlap_nonneg (hProjector hReference) rho
    (hProjector_isSymmetricProjection hReference)

theorem hCanonicalizer_conj_hProjector (d : HDirection) :
    (hCanonicalizer d).conjOperator (hProjector d) = hProjector hReference := by
  have h := congrArg (fun sigma : DensityOperator QubitSpace => sigma.toOperator)
    (hCanonicalizer_conj_hMagicState d)
  have hReferenceOperator : hMagicState.toOperator = hProjector hReference := by
    rw [← hMagicStateOfReference]
    rfl
  rw [UnitaryTransport.conjDensity_toOperator, hReferenceOperator] at h
  exact h

theorem hCanonicalizedInput_hInputFidelity (rho : DensityOperator QubitSpace) :
    hInputFidelity (hCanonicalizedInput rho) = hFidelity rho := by
  unfold hCanonicalizedInput hInputFidelity hDirectionFidelity
  rw [← hCanonicalizer_conj_hProjector (hMaximizingDirection rho)]
  rw [projectionFidelity_conjDensity]
  exact (hMaximizingDirection_attains rho).symm

/-- Canonicalization identifies the operational error with `1 - F_H²`. -/
theorem hCanonicalizedInput_error_eq_one_sub_hFidelity_sq
    (rho : DensityOperator QubitSpace) :
    hInputError (hCanonicalizedInput rho) = 1 - hFidelity rho ^ 2 := by
  rw [hInputError, hInputSquaredOverlap_eq_hInputFidelity_sq,
    hCanonicalizedInput_hInputFidelity]

/-! ## Corrected H-to-A input frame -/

/-- The H reference projector transported by the literal `K†`-then-`H` route
is exactly the positive source-A projector. -/
theorem sourceA0Transport_conj_hReference_projector :
    sourceA0Transport.conjOperator (hProjector hReference) =
      aBasisProjector .positive := by
  have hReferenceOperator : hMagicState.toOperator = hProjector hReference := by
    rw [← hMagicStateOfReference]
    rfl
  calc
    sourceA0Transport.conjOperator (hProjector hReference) =
        sourceA0Transport.conjOperator hMagicState.toOperator := by
      rw [hReferenceOperator]
    _ = sourceA0Density.toOperator := by
      rw [sourceA0Density, UnitaryTransport.conjDensity_toOperator]
    _ = aZeroDensity.toOperator := rfl
    _ = aBasisProjector .positive :=
      aBasisProjector_positive_eq_aZeroDensity_toOperator.symm

/-- Canonical H-frame input moved into the literal source-A frame. -/
noncomputable def sourceAFramedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  sourceA0Transport.conjDensity (hCanonicalizedInput rho)

/-- Every ideal H-orbit witness is mapped to the source `A₀` density. -/
theorem sourceAFramed_hMagicStateOfDirection (d : HDirection) :
    sourceA0Transport.conjDensity
      ((hCanonicalizer d).conjDensity (hMagicStateOfDirection d)) = aZeroDensity := by
  rw [hCanonicalizer_conj_hMagicState]
  rfl

/-- The squared positive-A overlap of a source-framed input. -/
def aInputSquaredOverlap (rho : DensityOperator QubitSpace) : Real :=
  projectionSquaredOverlap (aBasisProjector .positive) rho

/-- The negative-A probability of a source-framed input. -/
def aInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - aInputSquaredOverlap rho

theorem sourceAFramedInput_aInputSquaredOverlap (rho : DensityOperator QubitSpace) :
    aInputSquaredOverlap (sourceAFramedInput rho) = hFidelity rho ^ 2 := by
  unfold aInputSquaredOverlap sourceAFramedInput
  calc
    projectionSquaredOverlap (aBasisProjector .positive)
        (sourceA0Transport.conjDensity (hCanonicalizedInput rho)) =
        projectionSquaredOverlap
          (sourceA0Transport.conjOperator (hProjector hReference))
          (sourceA0Transport.conjDensity (hCanonicalizedInput rho)) := by
      rw [sourceA0Transport_conj_hReference_projector]
    _ = projectionSquaredOverlap (hProjector hReference)
          (hCanonicalizedInput rho) :=
      projectionSquaredOverlap_conjDensity sourceA0Transport
        (hProjector hReference) (hCanonicalizedInput rho)
    _ = hInputSquaredOverlap (hCanonicalizedInput rho) := rfl
    _ = hInputFidelity (hCanonicalizedInput rho) ^ 2 :=
      hInputSquaredOverlap_eq_hInputFidelity_sq (hCanonicalizedInput rho)
    _ = hFidelity rho ^ 2 := by rw [hCanonicalizedInput_hInputFidelity]

/-- Once the H frame is transported to A, the error is exactly `1 - F_H²`. -/
theorem sourceAFramedInput_error_eq_one_sub_hFidelity_sq
    (rho : DensityOperator QubitSpace) :
    aInputError (sourceAFramedInput rho) = 1 - hFidelity rho ^ 2 := by
  rw [aInputError, sourceAFramedInput_aInputSquaredOverlap]

/-! ## Admissible diagonal resources -/

/-- The closed physical source domain for the literal A-basis input mixture.

Strict positivity is deliberately not part of this raw-input object: the
zero-error endpoint is needed by the later protocol layer as a raw branch
statement.  Normalized accepted and rejected branches separately require a
strict positivity witness. -/
structure BK15Epsilon where
  epsilon : Real
  nonneg : 0 ≤ epsilon
  le_half : epsilon ≤ 1 / 2

namespace BK15Epsilon

theorem le_one (epsilon : BK15Epsilon) : epsilon.epsilon ≤ 1 := by
  linarith [epsilon.le_half]

/-- The no-error probability. -/
def cleanWeight (epsilon : BK15Epsilon) : Real := 1 - epsilon.epsilon

theorem cleanWeight_nonneg (epsilon : BK15Epsilon) : 0 ≤ epsilon.cleanWeight :=
  sub_nonneg.mpr epsilon.le_one

theorem cleanWeight_add_error (epsilon : BK15Epsilon) :
    epsilon.cleanWeight + epsilon.epsilon = 1 := by
  simp [cleanWeight]

end BK15Epsilon

/-- The two literal A-basis density components indexed by an error bit. -/
noncomputable def aInputComponent : Fin 2 → DensityOperator QubitSpace
  | 0 => aZeroDensity
  | 1 => aOneDensity

/-- The normalized one-site A-basis error weights. -/
def aInputWeight (epsilon : BK15Epsilon) : Fin 2 → Real
  | 0 => epsilon.cleanWeight
  | 1 => epsilon.epsilon

theorem aInputWeight_nonneg (epsilon : BK15Epsilon) (bit : Fin 2) :
    0 ≤ aInputWeight epsilon bit := by
  fin_cases bit
  · exact epsilon.cleanWeight_nonneg
  · exact epsilon.nonneg

theorem sum_aInputWeight (epsilon : BK15Epsilon) :
    ∑ bit : Fin 2, aInputWeight epsilon bit = 1 := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp [aInputWeight, epsilon.cleanWeight_add_error]

/-- The actual one-site diagonal A-basis density. -/
noncomputable def diagonalAResource (epsilon : BK15Epsilon) :
    DensityOperator QubitSpace :=
  DensityOperator.convexCombination Finset.univ (aInputWeight epsilon) aInputComponent
    (by
      intro bit _hbit
      exact aInputWeight_nonneg epsilon bit)
    (by simpa using sum_aInputWeight epsilon)

/-! ## A-basis dephasing as the literal error mixture -/

private theorem rankOne_sandwich
    (u : QubitSpace) (_hu : inner Complex u u = 1) (A : Operator QubitSpace) :
    (InnerProductSpace.rankOne Complex u u).toLinearMap *
        (A * (InnerProductSpace.rankOne Complex u u).toLinearMap) =
        (inner Complex u (A u)) •
        (InnerProductSpace.rankOne Complex u u).toLinearMap := by
  ext vector
  simp [Module.End.mul_eq_comp, LinearMap.comp_apply,
    InnerProductSpace.rankOne_apply]
  ring

private theorem trace_rankOne_mul
    (u : QubitSpace) (A : Operator QubitSpace) :
    LinearMap.trace Complex QubitSpace
      ((InnerProductSpace.rankOne Complex u u).toLinearMap * A) =
        inner Complex u (A u) := by
  rw [LinearMap.trace_mul_comm]
  exact trace_mul_rankOne A u

private theorem inner_apply_real_of_positive
    (rho : DensityOperator QubitSpace) (u : QubitSpace) :
    ((inner Complex u (rho.toOperator u)).re : Complex) =
      inner Complex u (rho.toOperator u) := by
  have hpositive := (LinearMap.isPositive_iff_complex rho.toOperator).mp rho.positive u
  simpa [rho.positive.isSymmetric u u] using hpositive.1

private theorem aBasisSquaredOverlap_add_negative
    (rho : DensityOperator QubitSpace) :
    aInputSquaredOverlap rho +
        projectionSquaredOverlap (aBasisProjector .negative) rho = 1 := by
  unfold aInputSquaredOverlap projectionSquaredOverlap
  have htrace :
      LinearMap.trace Complex QubitSpace
          (aBasisProjector .positive * rho.toOperator) +
        LinearMap.trace Complex QubitSpace
          (aBasisProjector .negative * rho.toOperator) = 1 := by
    calc
      LinearMap.trace Complex QubitSpace
          (aBasisProjector .positive * rho.toOperator) +
        LinearMap.trace Complex QubitSpace
          (aBasisProjector .negative * rho.toOperator) =
          LinearMap.trace Complex QubitSpace
            ((aBasisProjector .positive + aBasisProjector .negative) * rho.toOperator) := by
              rw [add_mul, map_add]
      _ = LinearMap.trace Complex QubitSpace rho.toOperator := by
        rw [aBasisProjector_add, one_mul]
      _ = 1 := rho.trace_one
  have hre := congrArg Complex.re htrace
  exact_mod_cast hre

private theorem aBasisDephasing_mapDensity_toOperator_eq_components
    (rho : DensityOperator QubitSpace) :
    (aBasisDephasing.mapDensity rho).toOperator =
      (aInputSquaredOverlap rho : Complex) • aZeroDensity.toOperator +
        (aInputError rho : Complex) • aOneDensity.toOperator := by
  have hzeroInner : inner Complex aZeroState aZeroState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aZeroState_norm]
    norm_num
  have honeInner : inner Complex aOneState aOneState = 1 := by
    rw [inner_self_eq_norm_sq_to_K, aOneState_norm]
    norm_num
  have hplusWeight :
      (aInputSquaredOverlap rho : Complex) =
        inner Complex aZeroState (rho.toOperator aZeroState) := by
    unfold aInputSquaredOverlap projectionSquaredOverlap
    rw [aBasisProjector_positive_eq_aZeroDensity_toOperator,
      aZeroDensity_toOperator_rankOne, trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aZeroState
  have hnegativeSquaredWeight :
      (projectionSquaredOverlap (aBasisProjector .negative) rho : Complex) =
        inner Complex aOneState (rho.toOperator aOneState) := by
    unfold projectionSquaredOverlap
    rw [aBasisProjector_negative_eq_aOneDensity_toOperator,
      aOneDensity_toOperator_rankOne, trace_rankOne_mul]
    exact inner_apply_real_of_positive rho aOneState
  have hnegativeWeight :
      (aInputError rho : Complex) =
        inner Complex aOneState (rho.toOperator aOneState) := by
    have hsum := aBasisSquaredOverlap_add_negative rho
    unfold aInputError
    have hreal : projectionSquaredOverlap (aBasisProjector .negative) rho =
        1 - aInputSquaredOverlap rho := by
      linarith
    rw [← hreal, hnegativeSquaredWeight]
  rw [QuantumChannel.mapDensity_toOperator, aBasisDephasing,
    FiniteKrausFamily.toQuantumChannel_apply_sum]
  change (∑ outcome : Coding.PauliSymplectic.StabilizerOutcome,
      aBasisProjector outcome *
        (rho.toOperator * LinearMap.adjoint (aBasisProjector outcome))) = _
  rw [show (Finset.univ : Finset Coding.PauliSymplectic.StabilizerOutcome) =
      {Coding.PauliSymplectic.StabilizerOutcome.positive,
        Coding.PauliSymplectic.StabilizerOutcome.negative} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [aBasisProjector_adjoint .positive, aBasisProjector_adjoint .negative,
    aBasisProjector_positive_eq_aZeroDensity_toOperator,
    aBasisProjector_negative_eq_aOneDensity_toOperator,
    aZeroDensity_toOperator_rankOne, aOneDensity_toOperator_rankOne,
    rankOne_sandwich aZeroState hzeroInner rho.toOperator,
    rankOne_sandwich aOneState honeInner rho.toOperator,
    ← hplusWeight, ← hnegativeWeight,
    ← aZeroDensity_toOperator_rankOne, ← aOneDensity_toOperator_rankOne]

theorem aBasisDephasing_mapDensity_eq_diagonalAResource
    (rho : DensityOperator QubitSpace) (epsilon : BK15Epsilon)
    (hepsilon : epsilon.epsilon = aInputError rho) :
    aBasisDephasing.mapDensity rho = diagonalAResource epsilon := by
  have hclean : epsilon.cleanWeight = aInputSquaredOverlap rho := by
    unfold BK15Epsilon.cleanWeight
    rw [hepsilon]
    unfold aInputError
    ring
  apply densityOperator_ext
  rw [aBasisDephasing_mapDensity_toOperator_eq_components]
  rw [diagonalAResource, DensityOperator.convexCombination_toOperator]
  change (aInputSquaredOverlap rho : Complex) • aZeroDensity.toOperator +
      (aInputError rho : Complex) • aOneDensity.toOperator =
    ∑ bit ∈ (Finset.univ : Finset (Fin 2)),
      (aInputWeight epsilon bit : Complex) • (aInputComponent bit).toOperator
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  simp [aInputWeight, aInputComponent, hclean, hepsilon]

/-- The source-domain error extracted from an H input after the required
canonical-H then `K†`-then-`H` transport. -/
noncomputable def hCanonicalizedInputEpsilon
    (rho : DensityOperator QubitSpace) (hpositive : 0 < 1 - hFidelity rho ^ 2)
    (hleHalf : 1 - hFidelity rho ^ 2 ≤ 1 / 2) : BK15Epsilon where
  epsilon := 1 - hFidelity rho ^ 2
  nonneg := hpositive.le
  le_half := hleHalf

/-- The actual A-basis dephased input, after first changing from the H frame
to the source-A frame. -/
noncomputable def hCanonicalizedDephasedInput (rho : DensityOperator QubitSpace) :
    DensityOperator QubitSpace :=
  aBasisDephasing.mapDensity (sourceAFramedInput rho)

theorem hCanonicalizedDephasedInput_eq_diagonalAResource
    (rho : DensityOperator QubitSpace) (hpositive : 0 < 1 - hFidelity rho ^ 2)
    (hleHalf : 1 - hFidelity rho ^ 2 ≤ 1 / 2) :
    hCanonicalizedDephasedInput rho =
      diagonalAResource (hCanonicalizedInputEpsilon rho hpositive hleHalf) := by
  unfold hCanonicalizedDephasedInput
  apply aBasisDephasing_mapDensity_eq_diagonalAResource
  exact (sourceAFramedInput_error_eq_one_sub_hFidelity_sq rho).symm

/-! ## Fifteen-resource product and error-word mixture -/

/-- Fixed right-associated tensor factors, kept explicit so elaboration never
has to synthesize analytic instances at a symbolic tensor depth. -/
abbrev BK1Tensor := QubitSpace
abbrev BK2Tensor := CompositeSystem QubitSpace BK1Tensor
abbrev BK3Tensor := CompositeSystem QubitSpace BK2Tensor
abbrev BK4Tensor := CompositeSystem QubitSpace BK3Tensor
abbrev BK5Tensor := CompositeSystem QubitSpace BK4Tensor
abbrev BK6Tensor := CompositeSystem QubitSpace BK5Tensor
abbrev BK7Tensor := CompositeSystem QubitSpace BK6Tensor
abbrev BK8Tensor := CompositeSystem QubitSpace BK7Tensor
abbrev BK9Tensor := CompositeSystem QubitSpace BK8Tensor
abbrev BK10Tensor := CompositeSystem QubitSpace BK9Tensor
abbrev BK11Tensor := CompositeSystem QubitSpace BK10Tensor
abbrev BK12Tensor := CompositeSystem QubitSpace BK11Tensor
abbrev BK13Tensor := CompositeSystem QubitSpace BK12Tensor
abbrev BK14Tensor := CompositeSystem QubitSpace BK13Tensor
abbrev BK15Tensor := CompositeSystem QubitSpace BK14Tensor

/-- Fixed right-associated binary labels in the same physical site order. -/
abbrev BK1BitTuple := Fin 2
abbrev BK2BitTuple := Fin 2 × BK1BitTuple
abbrev BK3BitTuple := Fin 2 × BK2BitTuple
abbrev BK4BitTuple := Fin 2 × BK3BitTuple
abbrev BK5BitTuple := Fin 2 × BK4BitTuple
abbrev BK6BitTuple := Fin 2 × BK5BitTuple
abbrev BK7BitTuple := Fin 2 × BK6BitTuple
abbrev BK8BitTuple := Fin 2 × BK7BitTuple
abbrev BK9BitTuple := Fin 2 × BK8BitTuple
abbrev BK10BitTuple := Fin 2 × BK9BitTuple
abbrev BK11BitTuple := Fin 2 × BK10BitTuple
abbrev BK12BitTuple := Fin 2 × BK11BitTuple
abbrev BK13BitTuple := Fin 2 × BK12BitTuple
abbrev BK14BitTuple := Fin 2 × BK13BitTuple
abbrev BK15BitTuple := Fin 2 × BK14BitTuple

/-- The physical BK15 Hilbert space. -/
abbrev BK15Register := QubitRegister (Fin 15)

/-- Reassemble a tensor computational label as a physical Fin-15 bitstring. -/
def bk15TupleBitstring (bits : BK15BitTuple) : Bitstring (Fin 15) :=
  fun site =>
    match site.1 with
    | 0 => bits.1
    | 1 => bits.2.1
    | 2 => bits.2.2.1
    | 3 => bits.2.2.2.1
    | 4 => bits.2.2.2.2.1
    | 5 => bits.2.2.2.2.2.1
    | 6 => bits.2.2.2.2.2.2.1
    | 7 => bits.2.2.2.2.2.2.2.1
    | 8 => bits.2.2.2.2.2.2.2.2.1
    | 9 => bits.2.2.2.2.2.2.2.2.2.1
    | 10 => bits.2.2.2.2.2.2.2.2.2.2.1
    | 11 => bits.2.2.2.2.2.2.2.2.2.2.2.1
    | 12 => bits.2.2.2.2.2.2.2.2.2.2.2.2.1
    | 13 => bits.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    | _ => bits.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Split a physical Fin-15 bitstring in the fixed tensor order. -/
def splitBK15Bitstring (bits : Bitstring (Fin 15)) : BK15BitTuple :=
  (bits 0, (bits 1, (bits 2, (bits 3, (bits 4, (bits 5, (bits 6,
    (bits 7, (bits 8, (bits 9, (bits 10, (bits 11, (bits 12,
      (bits 13, bits 14))))))))))))))

@[simp] theorem splitBK15Bitstring_bk15TupleBitstring (bits : BK15BitTuple) :
    splitBK15Bitstring (bk15TupleBitstring bits) = bits := by
  rcases bits with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14⟩
  rfl

@[simp] theorem bk15TupleBitstring_splitBK15Bitstring
    (bits : Bitstring (Fin 15)) :
    bk15TupleBitstring (splitBK15Bitstring bits) = bits := by
  funext site
  fin_cases site <;> rfl

/-- The concrete basis-label equivalence from the tensor product to Fin-15. -/
def bk15BitstringEquiv : BK15BitTuple ≃ Bitstring (Fin 15) where
  toFun := bk15TupleBitstring
  invFun := splitBK15Bitstring
  left_inv := splitBK15Bitstring_bk15TupleBitstring
  right_inv := bk15TupleBitstring_splitBK15Bitstring

section

set_option maxRecDepth 65536

/-- The basis-preserving unitary from the ordered fifteen-fold tensor to the
physical Fin-15 register. -/
noncomputable def bk15TensorRegisterTransport :
    UnitaryTransport BK15Tensor BK15Register := by
  let oneBasis := EuclideanSpace.basisFun (Fin 2) Complex
  let sourceBasis := oneBasis.tensorProduct
    (oneBasis.tensorProduct
      (oneBasis.tensorProduct
        (oneBasis.tensorProduct
          (oneBasis.tensorProduct
            (oneBasis.tensorProduct
              (oneBasis.tensorProduct
                (oneBasis.tensorProduct
                  (oneBasis.tensorProduct
                    (oneBasis.tensorProduct
                      (oneBasis.tensorProduct
                        (oneBasis.tensorProduct
                          (oneBasis.tensorProduct
                            (oneBasis.tensorProduct oneBasis)))))))))))))
  let targetBasis := EuclideanSpace.basisFun (Bitstring (Fin 15)) Complex
  let U := sourceBasis.equiv targetBasis bk15BitstringEquiv
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }

end

private theorem tensorDensity_convexCombination
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type w} {κ : Type*} [Fintype ι] [Fintype κ]
    (weight : ι → Real) (rho : ι → DensityOperator H)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_sum : ∑ i, weight i = 1)
    (tailWeight : κ → Real) (sigma : κ → DensityOperator K)
    (htail_nonneg : ∀ j, 0 ≤ tailWeight j) (htail_sum : ∑ j, tailWeight j = 1) :
    DensityOperator.tensorDensity
        (DensityOperator.convexCombination Finset.univ weight rho
          (by intro i _; exact hweight_nonneg i) hweight_sum)
        (DensityOperator.convexCombination Finset.univ tailWeight sigma
          (by intro j _; exact htail_nonneg j) htail_sum) =
      DensityOperator.convexCombination Finset.univ
        (fun pair : ι × κ => weight pair.1 * tailWeight pair.2)
        (fun pair => DensityOperator.tensorDensity (rho pair.1) (sigma pair.2))
        (by
          intro pair _
          exact mul_nonneg (hweight_nonneg pair.1) (htail_nonneg pair.2))
        (by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, htail_sum, mul_one]
          exact hweight_sum) := by
  apply densityOperator_ext_toOperator
  simp only [DensityOperator.tensorDensity_toOperator,
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  rw [DensityOperator.tensorMap_sum_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right]
  simp only [smul_smul, Complex.ofReal_mul]
  rw [DensityOperator.tensorDensity_toOperator]

/-- A full-support finite mixture together with the physical density it expands. -/
private structure FlatExpansion (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (ι : Type) [Fintype ι] where
  weight : ι → Real
  component : ι → DensityOperator H
  nonneg : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  physical : DensityOperator H
  physical_eq_flat : physical = DensityOperator.convexCombination Finset.univ
    weight component (by intro i _; exact nonneg i) sum_one

private noncomputable def FlatExpansion.flat
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type} [Fintype ι]
    (expansion : FlatExpansion H ι) : DensityOperator H :=
  DensityOperator.convexCombination Finset.univ expansion.weight expansion.component
    (by intro i _; exact expansion.nonneg i) expansion.sum_one

private theorem conjDensity_convexCombination
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type v} [Fintype ι]
    (U : UnitaryTransport H K) (weight : ι → Real) (rho : ι → DensityOperator H)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_sum : ∑ i, weight i = 1) :
    U.conjDensity
        (DensityOperator.convexCombination Finset.univ weight rho
          (by intro i _; exact hweight_nonneg i) hweight_sum) =
      DensityOperator.convexCombination Finset.univ weight
        (fun i => U.conjDensity (rho i))
        (by intro i _; exact hweight_nonneg i) hweight_sum := by
  apply densityOperator_ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator]
  simp only [
    DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  change U.conjOperatorLinearMap (∑ i ∈ Finset.univ,
      (weight i : Complex) • (rho i).toOperator) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl

private theorem convexCombination_equiv
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (equiv : ι ≃ κ) (weight : ι → Real)
    (rho : ι → DensityOperator H)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) (hweight_sum : ∑ i, weight i = 1) :
    DensityOperator.convexCombination Finset.univ weight rho
        (by intro i _; exact hweight_nonneg i) hweight_sum =
      DensityOperator.convexCombination Finset.univ
        (fun j => weight (equiv.symm j)) (fun j => rho (equiv.symm j))
        (by intro j _; exact hweight_nonneg (equiv.symm j))
        ((equiv.symm.sum_comp weight).trans hweight_sum) := by
  apply densityOperator_ext_toOperator
  simp only [DensityOperator.convexCombination_toOperator]
  unfold DensityOperator.convexCombinationOperator
  apply Fintype.sum_equiv equiv
  intro i
  simp

private noncomputable def aBasisFlatExpansion (epsilon : BK15Epsilon) :
    FlatExpansion QubitSpace (Fin 2) where
  weight := aInputWeight epsilon
  component := aInputComponent
  nonneg := aInputWeight_nonneg epsilon
  sum_one := sum_aInputWeight epsilon
  physical := diagonalAResource epsilon
  physical_eq_flat := rfl

private noncomputable def prependABasisFlatExpansion {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι : Type} [Fintype ι] (epsilon : BK15Epsilon)
    (tail : FlatExpansion K ι) :
    FlatExpansion (CompositeSystem QubitSpace K) (Fin 2 × ι) where
  weight := fun pair => aInputWeight epsilon pair.1 * tail.weight pair.2
  component := fun pair => DensityOperator.tensorDensity
    (aInputComponent pair.1) (tail.component pair.2)
  nonneg := by
    intro pair
    exact mul_nonneg (aInputWeight_nonneg epsilon pair.1) (tail.nonneg pair.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, tail.sum_one, mul_one]
    exact sum_aInputWeight epsilon
  physical := DensityOperator.tensorDensity (diagonalAResource epsilon) tail.physical
  physical_eq_flat := by
    calc
      DensityOperator.tensorDensity (diagonalAResource epsilon) tail.physical =
          DensityOperator.tensorDensity (diagonalAResource epsilon) tail.flat := by
            unfold FlatExpansion.flat
            exact congrArg (DensityOperator.tensorDensity (diagonalAResource epsilon))
              tail.physical_eq_flat
      _ = _ := tensorDensity_convexCombination
        (aInputWeight epsilon) aInputComponent (aInputWeight_nonneg epsilon)
        (sum_aInputWeight epsilon) tail.weight tail.component tail.nonneg tail.sum_one

/-- The explicit fifteen-level full-support A-basis mixture.  Each `prepend`
adds one physical site and therefore doubles the displayed finite support. -/
private noncomputable def bk15FlatExpansion (epsilon : BK15Epsilon) :
    FlatExpansion BK15Tensor BK15BitTuple := by
  let m1 := aBasisFlatExpansion epsilon
  let m2 := prependABasisFlatExpansion epsilon m1
  let m3 := prependABasisFlatExpansion epsilon m2
  let m4 := prependABasisFlatExpansion epsilon m3
  let m5 := prependABasisFlatExpansion epsilon m4
  let m6 := prependABasisFlatExpansion epsilon m5
  let m7 := prependABasisFlatExpansion epsilon m6
  let m8 := prependABasisFlatExpansion epsilon m7
  let m9 := prependABasisFlatExpansion epsilon m8
  let m10 := prependABasisFlatExpansion epsilon m9
  let m11 := prependABasisFlatExpansion epsilon m10
  let m12 := prependABasisFlatExpansion epsilon m11
  let m13 := prependABasisFlatExpansion epsilon m12
  let m14 := prependABasisFlatExpansion epsilon m13
  exact prependABasisFlatExpansion epsilon m14

/-- The genuine tensor product of fifteen arbitrary supplied resource states. -/
noncomputable def bk15TensorDensity
    (inputs : ResourceInput 15 QubitSpace) : DensityOperator BK15Tensor :=
  DensityOperator.tensorDensity (inputs 0)
    (DensityOperator.tensorDensity (inputs 1)
      (DensityOperator.tensorDensity (inputs 2)
        (DensityOperator.tensorDensity (inputs 3)
          (DensityOperator.tensorDensity (inputs 4)
            (DensityOperator.tensorDensity (inputs 5)
              (DensityOperator.tensorDensity (inputs 6)
                (DensityOperator.tensorDensity (inputs 7)
                  (DensityOperator.tensorDensity (inputs 8)
                    (DensityOperator.tensorDensity (inputs 9)
                      (DensityOperator.tensorDensity (inputs 10)
                        (DensityOperator.tensorDensity (inputs 11)
                          (DensityOperator.tensorDensity (inputs 12)
                            (DensityOperator.tensorDensity (inputs 13)
                              (inputs 14))))))))))))))

/-- Prepare all fifteen supplied resources in their physical site order. -/
noncomputable def bk15PrepareInput
    (inputs : ResourceInput 15 QubitSpace) : DensityOperator BK15Register :=
  bk15TensorRegisterTransport.conjDensity (bk15TensorDensity inputs)

/-- Fifteen identical dephased A-basis resources. -/
noncomputable def bk15NoisyResources (epsilon : BK15Epsilon) :
    ResourceInput 15 QubitSpace :=
  fun _ => diagonalAResource epsilon

@[simp] theorem bk15PrepareInput_noisyResources (epsilon : BK15Epsilon) :
    bk15PrepareInput (bk15NoisyResources epsilon) =
      bk15TensorRegisterTransport.conjDensity
        (bk15TensorDensity (bk15NoisyResources epsilon)) :=
  rfl

private theorem aInputWeight_eq_wordFactor (epsilon : BK15Epsilon) (bit : Fin 2) :
    aInputWeight epsilon bit =
      if bit = 0 then epsilon.cleanWeight else epsilon.epsilon := by
  fin_cases bit <;> rfl

/-- The independent Bernoulli probability of one concrete Fin-15 error word. -/
def bk15WordWeight (epsilon : BK15Epsilon) (word : Word) : Real :=
  ∏ site : Fin 15, aInputWeight epsilon (word site)

theorem bk15WordWeight_nonneg (epsilon : BK15Epsilon) (word : Word) :
    0 ≤ bk15WordWeight epsilon word := by
  unfold bk15WordWeight
  exact Finset.prod_nonneg fun site _ => aInputWeight_nonneg epsilon (word site)

/-- Independent physical error-word weights sum to one. -/
theorem sum_bk15WordWeight (epsilon : BK15Epsilon) :
    ∑ word : Word, bk15WordWeight epsilon word = 1 := by
  classical
  calc
    _ = ∑ word : Fin 15 → Fin 2,
        ∏ site : Fin 15, aInputWeight epsilon (word site) := by
      apply Fintype.sum_equiv (Equiv.refl (Fin 15 → Fin 2))
      intro word
      rfl
    _ = ∏ _site : Fin 15, ∑ bit : Fin 2, aInputWeight epsilon bit :=
      (Fintype.prod_sum (fun (_site : Fin 15) (bit : Fin 2) =>
        aInputWeight epsilon bit)).symm
    _ = 1 := by simp only [sum_aInputWeight, Finset.prod_const_one]

/-- The literal A-basis component selected by one error word at every site. -/
noncomputable def bk15WordResources (word : Word) : ResourceInput 15 QubitSpace :=
  fun site => aInputComponent (word site)

/-- The physical register density for one concrete A-basis error word. -/
noncomputable def bk15ErrorWordDensity (word : Word) :
    DensityOperator BK15Register :=
  bk15PrepareInput (bk15WordResources word)

private theorem bk15TensorDensity_noisy_eq_flat (epsilon : BK15Epsilon) :
    bk15TensorDensity (bk15NoisyResources epsilon) =
      (bk15FlatExpansion epsilon).flat := by
  change (bk15FlatExpansion epsilon).physical = (bk15FlatExpansion epsilon).flat
  exact (bk15FlatExpansion epsilon).physical_eq_flat

private theorem bk15FlatExpansion_weight_eq_bk15WordWeight
    (epsilon : BK15Epsilon) (bits : BK15BitTuple) :
    (bk15FlatExpansion epsilon).weight bits =
      bk15WordWeight epsilon (bk15TupleBitstring bits) := by
  rcases bits with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14⟩
  change aInputWeight epsilon b0 *
      (aInputWeight epsilon b1 *
        (aInputWeight epsilon b2 *
          (aInputWeight epsilon b3 *
            (aInputWeight epsilon b4 *
              (aInputWeight epsilon b5 *
                (aInputWeight epsilon b6 *
                  (aInputWeight epsilon b7 *
                    (aInputWeight epsilon b8 *
                      (aInputWeight epsilon b9 *
                        (aInputWeight epsilon b10 *
                          (aInputWeight epsilon b11 *
                            (aInputWeight epsilon b12 *
                              (aInputWeight epsilon b13 *
                                aInputWeight epsilon b14))))))))))))) =
      bk15WordWeight epsilon
        (bk15TupleBitstring
          (b0, (b1, (b2, (b3, (b4, (b5, (b6, (b7, (b8, (b9, (b10,
            (b11, (b12, (b13, b14)))))))))))))))
  unfold bk15WordWeight
  rw [show (Finset.univ : Finset (Fin 15)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} by decide]
  simp [bk15TupleBitstring] <;> ring

private theorem bk15FlatExpansion_component_eq_bk15ErrorWordDensity
    (epsilon : BK15Epsilon) (bits : BK15BitTuple) :
    bk15TensorRegisterTransport.conjDensity
      ((bk15FlatExpansion epsilon).component bits) =
      bk15ErrorWordDensity (bk15TupleBitstring bits) := by
  rcases bits with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14⟩
  rfl

/-- The physical `2^15`-term independent error-word expansion.  The underlying
full-support convex combination is formed on the fixed right-associated tensor
word labels, then transported basis-preservingly to the Fin-15 register. -/
noncomputable def bk15FlatErrorWordMixture (epsilon : BK15Epsilon) :
    DensityOperator BK15Register :=
  DensityOperator.convexCombination Finset.univ (bk15WordWeight epsilon)
    bk15ErrorWordDensity
    (by
      intro word _
      exact bk15WordWeight_nonneg epsilon word)
    (sum_bk15WordWeight epsilon)

set_option maxHeartbeats 1000000 in
private theorem bk15TensorRegisterTransport_conj_flat_eq_bk15FlatErrorWordMixture
    (epsilon : BK15Epsilon) :
    bk15TensorRegisterTransport.conjDensity ((bk15FlatExpansion epsilon).flat) =
      bk15FlatErrorWordMixture epsilon := by
  calc
    bk15TensorRegisterTransport.conjDensity ((bk15FlatExpansion epsilon).flat) =
        DensityOperator.convexCombination Finset.univ
          (bk15FlatExpansion epsilon).weight
          (fun bits => bk15TensorRegisterTransport.conjDensity
            ((bk15FlatExpansion epsilon).component bits))
          (by
            intro bits _
            exact (bk15FlatExpansion epsilon).nonneg bits)
          (bk15FlatExpansion epsilon).sum_one := by
      unfold FlatExpansion.flat
      exact conjDensity_convexCombination bk15TensorRegisterTransport
        (bk15FlatExpansion epsilon).weight (bk15FlatExpansion epsilon).component
        (bk15FlatExpansion epsilon).nonneg (bk15FlatExpansion epsilon).sum_one
    _ = DensityOperator.convexCombination Finset.univ
          (fun word => (bk15FlatExpansion epsilon).weight
            (bk15BitstringEquiv.symm word))
          (fun word => bk15TensorRegisterTransport.conjDensity
            ((bk15FlatExpansion epsilon).component (bk15BitstringEquiv.symm word)))
          (by
            intro word _
            exact (bk15FlatExpansion epsilon).nonneg (bk15BitstringEquiv.symm word))
          ((bk15BitstringEquiv.symm.sum_comp
            (bk15FlatExpansion epsilon).weight).trans
            (bk15FlatExpansion epsilon).sum_one) :=
      convexCombination_equiv bk15BitstringEquiv
        (bk15FlatExpansion epsilon).weight
        (fun bits => bk15TensorRegisterTransport.conjDensity
          ((bk15FlatExpansion epsilon).component bits))
        (bk15FlatExpansion epsilon).nonneg (bk15FlatExpansion epsilon).sum_one
    _ = bk15FlatErrorWordMixture epsilon := by
      have hweight :
          (fun word => (bk15FlatExpansion epsilon).weight
            (bk15BitstringEquiv.symm word)) = bk15WordWeight epsilon := by
        funext word
        change (bk15FlatExpansion epsilon).weight (splitBK15Bitstring word) =
          bk15WordWeight epsilon word
        simpa using bk15FlatExpansion_weight_eq_bk15WordWeight epsilon
          (splitBK15Bitstring word)
      have hcomponent :
          (fun word => bk15TensorRegisterTransport.conjDensity
            ((bk15FlatExpansion epsilon).component (bk15BitstringEquiv.symm word))) =
          bk15ErrorWordDensity := by
        funext word
        change bk15TensorRegisterTransport.conjDensity
          ((bk15FlatExpansion epsilon).component (splitBK15Bitstring word)) =
          bk15ErrorWordDensity word
        simpa using bk15FlatExpansion_component_eq_bk15ErrorWordDensity epsilon
          (splitBK15Bitstring word)
      unfold bk15FlatErrorWordMixture
      apply densityOperator_ext_toOperator
      simp only [DensityOperator.convexCombination_toOperator]
      unfold DensityOperator.convexCombinationOperator
      apply Finset.sum_congr rfl
      intro word _
      exact congrArg₂ (fun (weight : Complex) (component : Operator BK15Register) =>
        weight • component)
        (congrArg (fun weight : Real => (weight : Complex)) (congrFun hweight word))
        (congrArg DensityOperator.toOperator (congrFun hcomponent word))

/-- The actual finite independent error-word mixture used by the later BK15
instrument is the explicit flat physical mixture. -/
noncomputable def bk15ErrorWordMixture (epsilon : BK15Epsilon) :
    DensityOperator BK15Register :=
  bk15FlatErrorWordMixture epsilon

/-- The physical fifteen-site noisy product is exactly the explicit flat
`2^15`-term error-word mixture. -/
theorem bk15PrepareInput_noisyResources_eq_bk15ErrorWordMixture
    (epsilon : BK15Epsilon) :
    bk15PrepareInput (bk15NoisyResources epsilon) = bk15ErrorWordMixture epsilon := by
  unfold bk15PrepareInput bk15ErrorWordMixture bk15FlatErrorWordMixture
  rw [bk15TensorDensity_noisy_eq_flat]
  exact bk15TensorRegisterTransport_conj_flat_eq_bk15FlatErrorWordMixture epsilon

end NoisyInput
end BK15
end Distillation
end QEC

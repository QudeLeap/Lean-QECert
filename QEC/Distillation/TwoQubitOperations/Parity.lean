import QEC.Distillation.TwoQubitOperations.Clifford
/-!
# Two-qubit parity projectors

The product of the two register-local `Z` operators and its even and odd
spectral projectors on the computational basis.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace TwoQubit

open Semantics Semantics.Qubit

def zzOperator : Operator TwoQubitSpace :=
  localZ 0 * localZ 1

@[simp] theorem zzOperator_apply (psi : TwoQubitSpace)
    (bits : Bitstring (Fin 2)) :
    zzOperator psi bits =
      zPhase (bits 0) * zPhase (bits 1) * psi bits := by
  simp [zzOperator, Module.End.mul_apply, mul_assoc]

@[simp] theorem zzOperator_apply_basis (bits : Bitstring (Fin 2)) :
    zzOperator
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      (zPhase (bits 0) * zPhase (bits 1)) •
        EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits := by
  ext coordinate
  by_cases h : coordinate = bits
  · subst coordinate
    simp [zzOperator_apply]
  · simp [zzOperator_apply, h]

theorem zzOperator_square :
    zzOperator * zzOperator = (1 : Operator TwoQubitSpace) := by
  unfold zzOperator
  calc
    (localZ (0 : Fin 2) * localZ (1 : Fin 2)) *
          (localZ (0 : Fin 2) * localZ (1 : Fin 2)) =
        (localZ (0 : Fin 2) *
            (localZ (1 : Fin 2) * localZ (0 : Fin 2))) *
          localZ (1 : Fin 2) := by
      simp only [mul_assoc]
    _ = (localZ (0 : Fin 2) *
          (localZ (0 : Fin 2) * localZ (1 : Fin 2))) *
        localZ (1 : Fin 2) := by
      rw [localZ_localZ_commute (1 : Fin 2) (0 : Fin 2)]
    _ = (localZ (0 : Fin 2) * localZ (0 : Fin 2)) *
        (localZ (1 : Fin 2) * localZ (1 : Fin 2)) := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [localZ_square, localZ_square, one_mul]

theorem zzOperator_adjoint :
    LinearMap.adjoint zzOperator = zzOperator := by
  unfold zzOperator
  simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    localZ_adjoint] using
      (localZ_localZ_commute (1 : Fin 2) (0 : Fin 2))

def zzEvenProjector : Operator TwoQubitSpace :=
  (2 : Complex)⁻¹ • (1 + zzOperator)

def zzOddProjector : Operator TwoQubitSpace :=
  (2 : Complex)⁻¹ • (1 - zzOperator)

theorem zzEvenProjector_adjoint :
    LinearMap.adjoint zzEvenProjector = zzEvenProjector := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold zzEvenProjector
  apply LinearMap.IsSymmetric.smul
  · simp only [starRingEnd_apply, star_inv₀, star_ofNat]
  · apply LinearMap.IsSymmetric.add
    · exact LinearMap.IsSymmetric.one
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact zzOperator_adjoint

theorem zzOddProjector_adjoint :
    LinearMap.adjoint zzOddProjector = zzOddProjector := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold zzOddProjector
  apply LinearMap.IsSymmetric.smul
  · simp only [starRingEnd_apply, star_inv₀, star_ofNat]
  · apply LinearMap.IsSymmetric.sub
    · exact LinearMap.IsSymmetric.one
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact zzOperator_adjoint

theorem zzEvenProjector_idempotent :
    zzEvenProjector * zzEvenProjector = zzEvenProjector := by
  simp only [zzEvenProjector, smul_mul_assoc, mul_smul_comm,
    mul_add, add_mul, one_mul, mul_one, zzOperator_square]
  module

theorem zzOddProjector_idempotent :
    zzOddProjector * zzOddProjector = zzOddProjector := by
  simp only [zzOddProjector, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, one_mul, mul_one, zzOperator_square]
  module

theorem zzEvenProjector_isSymmetricProjection :
    zzEvenProjector.IsSymmetricProjection := by
  refine ⟨zzEvenProjector_idempotent, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact zzEvenProjector_adjoint

theorem zzOddProjector_isSymmetricProjection :
    zzOddProjector.IsSymmetricProjection := by
  refine ⟨zzOddProjector_idempotent, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact zzOddProjector_adjoint

theorem zzEvenProjector_mul_zzOddProjector :
    zzEvenProjector * zzOddProjector = (0 : Operator TwoQubitSpace) := by
  simp only [zzEvenProjector, zzOddProjector, smul_mul_assoc,
    mul_smul_comm, mul_sub, add_mul, one_mul, mul_one,
    zzOperator_square]
  module

theorem zzOddProjector_mul_zzEvenProjector :
    zzOddProjector * zzEvenProjector = (0 : Operator TwoQubitSpace) := by
  simp only [zzEvenProjector, zzOddProjector, smul_mul_assoc,
    mul_smul_comm, mul_add, sub_mul, one_mul, mul_one,
    zzOperator_square]
  module

theorem zzProjectors_complete :
    zzEvenProjector + zzOddProjector =
      (1 : Operator TwoQubitSpace) := by
  simp only [zzEvenProjector, zzOddProjector]
  module

@[simp] theorem zzEvenProjector_apply_basis (bits : Bitstring (Fin 2)) :
    zzEvenProjector
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      if bits 0 = bits 1 then
        EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits
      else 0 := by
  change
    (2 : Complex)⁻¹ •
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits +
          zzOperator
            (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits)) =
      _
  rw [zzOperator_apply_basis]
  by_cases h : bits 0 = bits 1
  · simp only [if_pos h]
    rw [h, zPhase_sq]
    module
  · simp only [if_neg h]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at *
      generalize hsecond : bits 1 = secondBit at *
      fin_cases firstBit <;> fin_cases secondBit <;> simp_all [zPhase]
    rw [hphase]
    module

@[simp] theorem zzOddProjector_apply_basis (bits : Bitstring (Fin 2)) :
    zzOddProjector
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      if bits 0 = bits 1 then 0
      else EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits := by
  change
    (2 : Complex)⁻¹ •
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits -
          zzOperator
            (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits)) =
      _
  rw [zzOperator_apply_basis]
  by_cases h : bits 0 = bits 1
  · simp only [if_pos h]
    rw [h, zPhase_sq]
    module
  · simp only [if_neg h]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at *
      generalize hsecond : bits 1 = secondBit at *
      fin_cases firstBit <;> fin_cases secondBit <;> simp_all [zPhase]
    rw [hphase]
    module

end TwoQubit
end Distillation
end QEC

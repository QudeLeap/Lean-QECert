import QEC.Coding.Stabilizer.PauliSemantics

/-!
# Signed Hermitian binary Pauli semantics

The existing binary Pauli interpretation uses the normal order
`phase * X-support * Z-support`.  A coordinate carrying both `X` and `Z`
therefore contributes `XZ = -iY`.  This module restores the source-level
signed Hermitian `I/X/Y/Z` convention by multiplying by one factor of `i` for
each overlapping coordinate.
-/

noncomputable section

namespace QEC
namespace Coding
namespace PauliSymplectic

open Classical
open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Coordinates at which a binary Pauli carries both an `X` and a `Z` bit. -/
def binaryOverlapSupport (P : Binary ι) : Finset ι :=
  zSupport P ∩ xSupport P

/-- The number of local `Y` factors in a binary Pauli coordinate vector. -/
def binaryOverlapCount (P : Binary ι) : Nat :=
  (binaryOverlapSupport P).card

/-- The `i^|X∩Z|` correction from normal-ordered `XZ` to Hermitian `Y`. -/
def hermitianPhaseScalar (P : Binary ι) : Complex :=
  Complex.I ^ binaryOverlapCount P

/--
Interpret a binary Pauli as the signed Hermitian `I/X/Y/Z` tensor represented
by its phase and symplectic coordinates.
-/
def toHermitianQubitOperator (P : Binary ι) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  hermitianPhaseScalar P • toQubitOperator P

@[simp]
theorem toHermitianQubitOperator_apply (P : Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι)
    (bits : Semantics.Qubit.Bitstring ι) :
    toHermitianQubitOperator P ψ bits =
      hermitianPhaseScalar P * toQubitOperator P ψ bits := by
  simp [toHermitianQubitOperator, smul_eq_mul]

/--
The raw normal-order swap phase is exactly `(-1)` to the number of local
`Y` coordinates.
-/
theorem binarySwapPhase_eq_neg_one_pow_binaryOverlapCount (P : Binary ι) :
    binarySwapPhase P.vector.xPart P.vector.zPart =
      (-1 : Complex) ^ binaryOverlapCount P := by
  change
    (∏ i ∈ zSupport P,
      if i ∈ xSupport P then (-1 : Complex) else 1) =
        (-1 : Complex) ^ (zSupport P ∩ xSupport P).card
  calc
    (∏ i ∈ zSupport P,
        if i ∈ xSupport P then (-1 : Complex) else 1) =
        (∏ i ∈ (zSupport P).filter (fun i => i ∈ xSupport P),
          (-1 : Complex)) *
        ∏ i ∈ (zSupport P).filter (fun i => i ∉ xSupport P),
          (1 : Complex) :=
      Finset.prod_ite (s := zSupport P) (p := fun i => i ∈ xSupport P)
        (fun _ => (-1 : Complex)) (fun _ => (1 : Complex))
    _ = (-1 : Complex) ^
        ((zSupport P).filter (fun i => i ∈ xSupport P)).card := by
          rw [Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    _ = (-1 : Complex) ^ (zSupport P ∩ xSupport P).card := by
          rw [Finset.filter_mem_eq_inter]

private theorem hermitianPhaseScalar_mul_self (P : Binary ι) :
    hermitianPhaseScalar P * hermitianPhaseScalar P =
      binarySwapPhase P.vector.xPart P.vector.zPart := by
  calc
    hermitianPhaseScalar P * hermitianPhaseScalar P =
        Complex.I ^ binaryOverlapCount P *
          Complex.I ^ binaryOverlapCount P := rfl
    _ = (Complex.I * Complex.I) ^ binaryOverlapCount P := by
          rw [mul_pow]
    _ = (-1 : Complex) ^ binaryOverlapCount P := by
          rw [Complex.I_mul_I]
    _ = binarySwapPhase P.vector.xPart P.vector.zPart :=
          (binarySwapPhase_eq_neg_one_pow_binaryOverlapCount P).symm

private theorem star_hermitianPhaseScalar_mul_self (P : Binary ι) :
    star (hermitianPhaseScalar P) * hermitianPhaseScalar P = 1 := by
  rw [hermitianPhaseScalar, star_pow, Complex.star_def, Complex.conj_I,
    ← mul_pow]
  simp [Complex.I_mul_I]

private theorem adjoint_toQubitOperator_eq_binarySwapPhase_smul
    (P : Binary ι) :
    LinearMap.adjoint (toQubitOperator P) =
      binarySwapPhase P.vector.xPart P.vector.zPart •
        toQubitOperator P := by
  rw [adjoint_toQubitOperator_eq_binaryDagger]
  unfold toQubitOperator
  simp only [binaryDagger, xSupport, zSupport]
  rw [binaryPhaseScalar_binaryDaggerPhase]
  simp only [smul_smul]
  congr 1
  exact mul_comm _ _

@[simp]
theorem toHermitianQubitOperator_binaryOne :
    toHermitianQubitOperator (binaryOne (ι := ι)) = 1 := by
  rw [toHermitianQubitOperator, toQubitOperator_one]
  simp [hermitianPhaseScalar, binaryOverlapCount, binaryOverlapSupport,
    xSupport, zSupport, binaryOne]

private theorem binaryOverlapCount_binarySign_mul
    (phase : ZMod 2) (P : Binary ι) :
    binaryOverlapCount (binaryMul (binarySign phase) P) =
      binaryOverlapCount P := by
  apply congrArg Finset.card
  ext i
  simp [binaryOverlapSupport, xSupport, zSupport, binarySupport, binaryMul,
    binarySign]

private theorem toQubitOperator_binarySign (phase : ZMod 2) :
    toQubitOperator (binarySign (ι := ι) phase) =
      binaryPhaseScalar phase •
        (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) := by
  simp [toQubitOperator, binarySign, xSupport, zSupport, binarySupport]

/-- The original binary global phase remains the exact global Hermitian sign. -/
theorem toHermitianQubitOperator_binarySign_mul
    (phase : ZMod 2) (P : Binary ι) :
    toHermitianQubitOperator (binaryMul (binarySign phase) P) =
      binaryPhaseScalar phase • toHermitianQubitOperator P := by
  unfold toHermitianQubitOperator hermitianPhaseScalar
  rw [binaryOverlapCount_binarySign_mul, toQubitOperator_binaryMul,
    toQubitOperator_binarySign]
  simp only [smul_mul_assoc, one_mul, smul_smul]
  rw [mul_comm]

/-- Every phase-corrected signed binary Pauli is self-adjoint. -/
theorem adjoint_toHermitianQubitOperator_eq_self (P : Binary ι) :
    LinearMap.adjoint (toHermitianQubitOperator P) =
      toHermitianQubitOperator P := by
  calc
    LinearMap.adjoint (toHermitianQubitOperator P) =
        star (hermitianPhaseScalar P) •
          LinearMap.adjoint (toQubitOperator P) := by
            exact
              map_smulₛₗ
                (LinearMap.adjoint :
                  (Semantics.Operator (Semantics.Qubit.QubitRegister ι)) ≃ₗ⋆[Complex]
                    Semantics.Operator (Semantics.Qubit.QubitRegister ι))
                (hermitianPhaseScalar P) (toQubitOperator P)
    _ = star (hermitianPhaseScalar P) •
        (binarySwapPhase P.vector.xPart P.vector.zPart •
          toQubitOperator P) := by
          rw [adjoint_toQubitOperator_eq_binarySwapPhase_smul]
    _ = star (hermitianPhaseScalar P) •
        ((hermitianPhaseScalar P * hermitianPhaseScalar P) •
          toQubitOperator P) := by
          rw [hermitianPhaseScalar_mul_self]
    _ = toHermitianQubitOperator P := by
          rw [smul_smul, ← mul_assoc,
            star_hermitianPhaseScalar_mul_self, one_mul]
          rfl

/-- Every phase-corrected signed binary Pauli squares to the identity. -/
theorem toHermitianQubitOperator_square (P : Binary ι) :
    toHermitianQubitOperator P * toHermitianQubitOperator P = 1 := by
  calc
    toHermitianQubitOperator P * toHermitianQubitOperator P =
        (hermitianPhaseScalar P * hermitianPhaseScalar P) •
          (toQubitOperator P * toQubitOperator P) := by
            exact smul_mul_smul_comm _ _ _ _
    _ = binarySwapPhase P.vector.xPart P.vector.zPart •
        (toQubitOperator P * toQubitOperator P) := by
          rw [hermitianPhaseScalar_mul_self]
    _ = (binarySwapPhase P.vector.xPart P.vector.zPart •
          toQubitOperator P) * toQubitOperator P := by
          rw [smul_mul_assoc]
    _ = LinearMap.adjoint (toQubitOperator P) * toQubitOperator P := by
          rw [adjoint_toQubitOperator_eq_binarySwapPhase_smul]
    _ = 1 := by
          simpa [Module.End.mul_eq_comp] using
            toQubitOperator_adjoint_comp_self P

/--
Binary symplectic commutation implies concrete commutation of the corrected
signed Hermitian operators.
-/
theorem toHermitianQubitOperator_commute_of_commutes
    (P Q : Binary ι) (h : Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      toHermitianQubitOperator Q * toHermitianQubitOperator P := by
  calc
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
        (hermitianPhaseScalar P * hermitianPhaseScalar Q) •
          (toQubitOperator P * toQubitOperator Q) := by
            exact smul_mul_smul_comm _ _ _ _
    _ = (hermitianPhaseScalar Q * hermitianPhaseScalar P) •
        (toQubitOperator Q * toQubitOperator P) := by
          rw [toQubitOperator_commute_of_commutes P Q h]
          rw [mul_comm (hermitianPhaseScalar P)]
    _ = toHermitianQubitOperator Q * toHermitianQubitOperator P := by
          exact (smul_mul_smul_comm _ _ _ _).symm

end PauliSymplectic
end Coding
end QEC

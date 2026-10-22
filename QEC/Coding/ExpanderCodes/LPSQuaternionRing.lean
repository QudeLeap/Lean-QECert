import QEC.Coding.ExpanderCodes.LPSQuaternion
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.TransferInstance

/-!
# The integral quaternion ring behind the LPS generators

The original LPS graph is a Hecke graph for an integral quaternion order.
This file equips the coordinate type already used by the concrete generator
construction with its Hamilton quaternion ring structure, and proves that
reduced norm, conjugation, and finite-field matrix reduction respect that
structure.
-/

open scoped MatrixGroups Quaternion

namespace QEC.Coding.TannerLiftedProduct

/-- Coordinate identification with Mathlib's Hamilton quaternions over the
integers. -/
def LPSQuaternion.equivQuaternion : LPSQuaternion ≃ Quaternion ℤ where
  toFun t := ⟨t.a, t.b, t.c, t.d⟩
  invFun t := ⟨t.re, t.imI, t.imJ, t.imK⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

/-- The Hamilton quaternion ring structure transported to the concrete LPS
coordinate type. -/
noncomputable instance : Ring LPSQuaternion :=
  Equiv.ring LPSQuaternion.equivQuaternion

/-- The coordinate identification as a ring equivalence. -/
noncomputable def LPSQuaternion.ringEquivQuaternion :
    LPSQuaternion ≃+* Quaternion ℤ :=
  Equiv.ringEquiv LPSQuaternion.equivQuaternion

@[simp] theorem LPSQuaternion.ringEquivQuaternion_apply
    (t : LPSQuaternion) :
    LPSQuaternion.ringEquivQuaternion t = ⟨t.a, t.b, t.c, t.d⟩ := rfl

@[simp] theorem LPSQuaternion.zero_a : (0 : LPSQuaternion).a = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 0).re = 0
  rw [map_zero]
  rfl

@[simp] theorem LPSQuaternion.zero_b : (0 : LPSQuaternion).b = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 0).imI = 0
  rw [map_zero]
  rfl

@[simp] theorem LPSQuaternion.zero_c : (0 : LPSQuaternion).c = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 0).imJ = 0
  rw [map_zero]
  rfl

@[simp] theorem LPSQuaternion.zero_d : (0 : LPSQuaternion).d = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 0).imK = 0
  rw [map_zero]
  rfl

@[simp] theorem LPSQuaternion.one_a : (1 : LPSQuaternion).a = 1 := by
  change (LPSQuaternion.ringEquivQuaternion 1).re = 1
  rw [map_one]
  rfl

@[simp] theorem LPSQuaternion.one_b : (1 : LPSQuaternion).b = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 1).imI = 0
  rw [map_one]
  rfl

@[simp] theorem LPSQuaternion.one_c : (1 : LPSQuaternion).c = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 1).imJ = 0
  rw [map_one]
  rfl

@[simp] theorem LPSQuaternion.one_d : (1 : LPSQuaternion).d = 0 := by
  change (LPSQuaternion.ringEquivQuaternion 1).imK = 0
  rw [map_one]
  rfl

@[simp] theorem LPSQuaternion.add_a (t u : LPSQuaternion) :
    (t + u).a = t.a + u.a := by
  change (LPSQuaternion.ringEquivQuaternion (t + u)).re = _
  rw [map_add]
  rfl

@[simp] theorem LPSQuaternion.add_b (t u : LPSQuaternion) :
    (t + u).b = t.b + u.b := by
  change (LPSQuaternion.ringEquivQuaternion (t + u)).imI = _
  rw [map_add]
  rfl

@[simp] theorem LPSQuaternion.add_c (t u : LPSQuaternion) :
    (t + u).c = t.c + u.c := by
  change (LPSQuaternion.ringEquivQuaternion (t + u)).imJ = _
  rw [map_add]
  rfl

@[simp] theorem LPSQuaternion.add_d (t u : LPSQuaternion) :
    (t + u).d = t.d + u.d := by
  change (LPSQuaternion.ringEquivQuaternion (t + u)).imK = _
  rw [map_add]
  rfl

@[simp] theorem LPSQuaternion.mul_a (t u : LPSQuaternion) :
    (t * u).a = t.a * u.a - t.b * u.b - t.c * u.c - t.d * u.d := by
  change (LPSQuaternion.ringEquivQuaternion (t * u)).re = _
  rw [map_mul, Quaternion.re_mul]
  rfl

@[simp] theorem LPSQuaternion.mul_b (t u : LPSQuaternion) :
    (t * u).b = t.a * u.b + t.b * u.a + t.c * u.d - t.d * u.c := by
  change (LPSQuaternion.ringEquivQuaternion (t * u)).imI = _
  rw [map_mul, Quaternion.imI_mul]
  rfl

@[simp] theorem LPSQuaternion.mul_c (t u : LPSQuaternion) :
    (t * u).c = t.a * u.c - t.b * u.d + t.c * u.a + t.d * u.b := by
  change (LPSQuaternion.ringEquivQuaternion (t * u)).imJ = _
  rw [map_mul, Quaternion.imJ_mul]
  rfl

@[simp] theorem LPSQuaternion.mul_d (t u : LPSQuaternion) :
    (t * u).d = t.a * u.d + t.b * u.c - t.c * u.b + t.d * u.a := by
  change (LPSQuaternion.ringEquivQuaternion (t * u)).imK = _
  rw [map_mul, Quaternion.imK_mul]
  rfl

@[simp] theorem LPSQuaternion.ringEquivQuaternion_conj
    (t : LPSQuaternion) :
    LPSQuaternion.ringEquivQuaternion t.conj =
      star (LPSQuaternion.ringEquivQuaternion t) := by
  change (⟨t.a, -t.b, -t.c, -t.d⟩ : Quaternion ℤ) =
    star (⟨t.a, t.b, t.c, t.d⟩ : Quaternion ℤ)
  rw [QuaternionAlgebra.star_mk]
  simp

/-- Quaternion conjugation reverses multiplication. -/
theorem LPSQuaternion.conj_mul (t u : LPSQuaternion) :
    (t * u).conj = u.conj * t.conj := by
  apply LPSQuaternion.ringEquivQuaternion.injective
  rw [LPSQuaternion.ringEquivQuaternion_conj, map_mul, star_mul,
    ← LPSQuaternion.ringEquivQuaternion_conj,
    ← LPSQuaternion.ringEquivQuaternion_conj, map_mul]

/-- The existing coordinate norm is Mathlib's multiplicative quaternion
reduced norm. -/
theorem LPSQuaternion.norm_eq_normSq (t : LPSQuaternion) :
    t.norm = Quaternion.normSq
      (LPSQuaternion.ringEquivQuaternion t) := by
  rw [Quaternion.normSq_def']
  rfl

@[simp] theorem LPSQuaternion.norm_one :
    (1 : LPSQuaternion).norm = 1 := by
  rw [LPSQuaternion.norm_eq_normSq, map_one, map_one]

/-- Multiplicativity of the integral reduced norm. -/
@[simp] theorem LPSQuaternion.norm_mul (t u : LPSQuaternion) :
    (t * u).norm = t.norm * u.norm := by
  rw [LPSQuaternion.norm_eq_normSq, map_mul,
    map_mul, ← LPSQuaternion.norm_eq_normSq,
    ← LPSQuaternion.norm_eq_normSq]

/-- Reduction of an integral quaternion to the LPS matrix model preserves
multiplication.  The only relation used by the model is the chosen finite
field identity `x² + y² + 1 = 0`. -/
@[simp] theorem lpsQuaternionMatrix_mul
    (q : ℕ) [Fact q.Prime] (t u : LPSQuaternion) :
    lpsQuaternionMatrix q (t * u) =
      lpsQuaternionMatrix q t * lpsQuaternionMatrix q u := by
  have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one q
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsQuaternionMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | linear_combination
        -((t.b : ZMod q) * (u.b : ZMod q) +
          (t.d : ZMod q) * (u.d : ZMod q)) * hroot
    | linear_combination
        ((t.d : ZMod q) * (u.b : ZMod q) -
          (t.b : ZMod q) * (u.d : ZMod q)) * hroot
    | linear_combination
        -((t.d : ZMod q) * (u.b : ZMod q) -
          (t.b : ZMod q) * (u.d : ZMod q)) * hroot

/-- The LPS finite-field matrix model as a ring homomorphism. -/
noncomputable def lpsQuaternionMatrixRingHom
    (q : ℕ) [Fact q.Prime] :
    LPSQuaternion →+* Matrix (Fin 2) (Fin 2) (ZMod q) where
  toFun := lpsQuaternionMatrix q
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix]
  map_mul' := lpsQuaternionMatrix_mul q
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix]
  map_add' t u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix] <;>
      ring

end QEC.Coding.TannerLiftedProduct

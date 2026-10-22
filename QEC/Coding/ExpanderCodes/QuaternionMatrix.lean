import QEC.Coding.ExpanderCodes.QuaternionGenerators
import QEC.Coding.ExpanderCodes.ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv

/-!
# A split quaternion matrix realization

When the quadratic parameter is an actual square `r²` in the coefficient
field, the quaternion algebra in [DEL21, Section 6.2] is explicitly the
two-by-two matrix algebra. The inverse coordinate map is proved, and the
projective unit groups are identified with PGL₂. This does not identify a
selected arithmetic image with PSL₂ or prove its spectral bound.
-/

namespace QEC.Coding.ExpanderCodes.QuaternionGenerators

universe u

variable {K : Type u} [Field K]

open Matrix

/-- Coordinates of the split quaternion representation. -/
def matrixCoordinates (r y : K) (q : Model (r ^ 2) y) : Matrix (Fin 2) (Fin 2) K :=
  !![q.re + q.imI * r, (q.imJ + q.imK * r) * (1 + y);
     q.imJ - q.imK * r, q.re - q.imI * r]

/-- The multiplication law is checked on all four matrix entries. -/
def matrixHom (r y : K) : Model (r ^ 2) y →+* Matrix (Fin 2) (Fin 2) K where
  toFun := matrixCoordinates r y
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixCoordinates]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixCoordinates]
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixCoordinates] <;> ring
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixCoordinates, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def quaternionCoordinates (r y : K) (M : Matrix (Fin 2) (Fin 2) K) : Model (r ^ 2) y :=
  ⟨(M 0 0 + M 1 1) / 2,
   (M 0 0 - M 1 1) / (2 * r),
   (M 0 1 / (1 + y) + M 1 0) / 2,
   (M 0 1 / (1 + y) - M 1 0) / (2 * r)⟩

/-- An explicit splitting isomorphism, with no dimension or bijectivity input. -/
def matrixEquiv (r y : K) (hR : r ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Model (r ^ 2) y ≃+* Matrix (Fin 2) (Fin 2) K where
  __ := matrixHom r y
  invFun := quaternionCoordinates r y
  left_inv q := by
    ext <;> simp [matrixHom, matrixCoordinates, quaternionCoordinates] <;> field_simp <;> ring
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixHom, matrixCoordinates, quaternionCoordinates] <;> field_simp <;> ring

/-- Matrix determinant agrees with the norm derived from quaternion conjugation. -/
theorem det_matrixCoordinates (r y : K) (q : Model (r ^ 2) y) :
    Matrix.det (matrixCoordinates r y q) =
      q.re ^ 2 - r ^ 2 * q.imI ^ 2 - (1 + y) * q.imJ ^ 2 +
        r ^ 2 * (1 + y) * q.imK ^ 2 := by
  simp [matrixCoordinates, Matrix.det_fin_two]
  ring

private theorem center_map_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro h
    obtain ⟨x, rfl⟩ := e.surjective h
    change e x * e g = e g * e x
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hg x)
  · intro hh
    refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hh (e x)

/-- The split quaternion projective unit group is genuinely PGL₂. -/
def projectiveMatrixEquiv (r y : K) (hR : r ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    ProjectiveGroup (r ^ 2) y ≃* Matrix.ProjGenLinGroup (Fin 2) K :=
  QuotientGroup.congr _ _
    (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv)
    (center_map_eq _)

/-- Splitting for a parameter with a proved square root, rather than a
syntactically square parameter. -/
def matrixEquivOfRoot (epsilon r y : K) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Model epsilon y ≃+* Matrix (Fin 2) (Fin 2) K := by
  subst epsilon
  exact matrixEquiv r y hR hOne hTwo

def projectiveMatrixEquivOfRoot (epsilon r y : K) (hRoot : r ^ 2 = epsilon)
    (hR : r ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    ProjectiveGroup epsilon y ≃* Matrix.ProjGenLinGroup (Fin 2) K := by
  subst epsilon
  exact projectiveMatrixEquiv r y hR hOne hTwo

@[simp] theorem projectiveMatrixEquiv_mk (r y : K) (hR : r ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (q : (Model (r ^ 2) y)ˣ) :
    projectiveMatrixEquiv r y hR hOne hTwo (QuotientGroup.mk q) =
      Matrix.ProjGenLinGroup.mk
        (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv q) := rfl

/-- The precise norm-square condition for a quaternion unit to give a PSL₂ class. -/
theorem projectiveMatrixEquiv_mem_psl_iff (r y : K) (hR : r ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (q : (Model (r ^ 2) y)ˣ) :
    projectiveMatrixEquiv r y hR hOne hTwo (QuotientGroup.mk q) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 =
        (q : Model (r ^ 2) y).re ^ 2 - r ^ 2 * (q : Model (r ^ 2) y).imI ^ 2 -
          (1 + y) * (q : Model (r ^ 2) y).imJ ^ 2 +
          r ^ 2 * (1 + y) * (q : Model (r ^ 2) y).imK ^ 2 := by
  rw [projectiveMatrixEquiv_mk,
    ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square]
  change (∃ s : K, s ^ 2 = Matrix.det (matrixCoordinates r y (q : Model (r ^ 2) y))) ↔ _
  rw [det_matrixCoordinates]

theorem det_base_matrix (r y : K) (hOne : 1 + y ≠ 0) :
    Matrix.det (matrixCoordinates r y (base (r ^ 2) y)) = y / (1 + y) := by
  rw [det_matrixCoordinates]
  simp [base]
  field_simp
  ring

theorem det_prime_matrix (r y : K) (hOne : 1 + y ≠ 0) :
    Matrix.det (matrixCoordinates r y (prime (r ^ 2) y)) =
      -(r ^ 2) * y / (1 + y) := by
  rw [det_matrixCoordinates]
  simp [prime]
  field_simp
  ring

/-- Membership of the first arithmetic generator in PSL₂ is an explicit
square condition; it is not implied merely by quaternion splitting. -/
theorem projectiveBase_matrix_mem_psl_iff (r y : K) (hR : r ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveMatrixEquiv r y hR hOne hTwo (projectiveBase (r ^ 2) y hY hOne) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 = y / (1 + y) := by
  change Matrix.ProjGenLinGroup.mk
    (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv
      (baseUnit (r ^ 2) y hY hOne)) ∈ _ ↔ _
  rw [ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square]
  change (∃ s : K, s ^ 2 = Matrix.det (matrixCoordinates r y (base (r ^ 2) y))) ↔ _
  rw [det_base_matrix r y hOne]

theorem projectivePrime_matrix_mem_psl_iff (r y : K) (hR : r ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveMatrixEquiv r y hR hOne hTwo
      (projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 = -(r ^ 2) * y / (1 + y) := by
  rw [show projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne =
    QuotientGroup.mk (primeUnit (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) from rfl,
    projectiveMatrixEquiv_mk,
    ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square]
  change (∃ s : K, s ^ 2 = Matrix.det
    (matrixCoordinates r y (primeUnit (r ^ 2) y (pow_ne_zero 2 hR) hY hOne))) ↔ _
  rw [val_primeUnit, det_prime_matrix r y hOne]

end QEC.Coding.ExpanderCodes.QuaternionGenerators

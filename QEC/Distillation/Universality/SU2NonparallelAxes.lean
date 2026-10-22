import QEC.Distillation.Universality.SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Nonparallel special-unitary axis circles

This module develops the finite-word geometry required to pass from complete
circles about two nonparallel Bloch axes to all determinant-one one-qubit
unitaries. The nonparallel premise is the positive squared cross product, so
it excludes both parallel and antiparallel axes.

The implementation deliberately does not use a fixed three-factor Euler word
for arbitrary nonorthogonal axes.
-/

noncomputable section

namespace QEC
namespace Distillation

open Matrix

/-- The coordinate vector of a transparent Bloch axis. -/
def blochVector (axis : UnitBlochAxis) : Fin 3 → Real :=
  ![axis.x, axis.y, axis.z]

/-- The Euclidean dot product of two transparent Bloch axes. -/
def blochDot (axis axis' : UnitBlochAxis) : Real :=
  axis.x * axis'.x + axis.y * axis'.y + axis.z * axis'.z

/-- The squared Euclidean norm of the explicit Bloch cross product. -/
def blochCrossSq (axis axis' : UnitBlochAxis) : Real :=
  (axis.y * axis'.z - axis.z * axis'.y) ^ 2 +
    (axis.z * axis'.x - axis.x * axis'.z) ^ 2 +
    (axis.x * axis'.y - axis.y * axis'.x) ^ 2

/-- Two Bloch axes are nonparallel exactly when their squared cross product is positive. -/
def UnitBlochAxis.Nonparallel (axis axis' : UnitBlochAxis) : Prop :=
  0 < blochCrossSq axis axis'

/-- The raw Pauli matrix associated to an arbitrary real three-vector. -/
def blochPauliMatrix (v : Fin 3 → Real) : SingleQubitMatrix :=
  !![(v 2 : Complex), (v 0 : Complex) - Complex.I * (v 1 : Complex);
     (v 0 : Complex) + Complex.I * (v 1 : Complex), -(v 2 : Complex)]

@[simp] theorem blochPauliMatrix_blochVector (axis : UnitBlochAxis) :
    blochPauliMatrix (blochVector axis) = axisPauliMatrix axis := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochPauliMatrix, blochVector, axisPauliMatrix]

@[simp] theorem blochVector_dot_self (axis : UnitBlochAxis) :
    blochVector axis ⬝ᵥ blochVector axis = 1 := by
  simp [blochVector]
  nlinarith [axis.norm_sq]

@[simp] theorem blochVector_dot (axis axis' : UnitBlochAxis) :
    blochVector axis ⬝ᵥ blochVector axis' = blochDot axis axis' := by
  simp [blochVector, blochDot]
  ring

/-- The squared cross product is `1 - dot^2` for unit Bloch axes. -/
theorem blochCrossSq_eq_one_sub_blochDot_sq (axis axis' : UnitBlochAxis) :
    blochCrossSq axis axis' = 1 - blochDot axis axis' ^ 2 := by
  have hidentity : blochCrossSq axis axis' + blochDot axis axis' ^ 2 =
      (axis.x ^ 2 + axis.y ^ 2 + axis.z ^ 2) *
        (axis'.x ^ 2 + axis'.y ^ 2 + axis'.z ^ 2) := by
    dsimp [blochCrossSq, blochDot]
    ring
  rw [axis.norm_sq, axis'.norm_sq] at hidentity
  linarith

/-- A nonparallel pair has a nonzero explicit cross product. -/
theorem UnitBlochAxis.nonparallel_crossSq_ne_zero {axis axis' : UnitBlochAxis}
    (h : axis.Nonparallel axis') : blochCrossSq axis axis' ≠ 0 := by
  exact ne_of_gt h

/-- The Pauli product formula for arbitrary real Bloch vectors. -/
theorem blochPauliMatrix_mul (v w : Fin 3 → Real) :
    blochPauliMatrix v * blochPauliMatrix w =
      ((v ⬝ᵥ w : Real) : Complex) • 1 +
        Complex.I • blochPauliMatrix (v ⨯₃ w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochPauliMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vec3_dotProduct, cross_apply] <;>
    ring_nf
  all_goals
    try rw [Complex.I_sq]
    ring

/-- The Pauli commutator is twice `i` times the Bloch cross product. -/
theorem blochPauliMatrix_commutator (v w : Fin 3 → Real) :
    blochPauliMatrix v * blochPauliMatrix w - blochPauliMatrix w * blochPauliMatrix v =
      ((2 : Complex) * Complex.I) • blochPauliMatrix (v ⨯₃ w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochPauliMatrix, cross_apply] <;>
    ring_nf
  all_goals
    try rw [Complex.I_sq]
    ring

/-- Nonparallel axes have a nonzero Pauli commutator. -/
theorem UnitBlochAxis.nonparallel_pauli_commutator_ne_zero
    {axis axis' : UnitBlochAxis} (h : axis.Nonparallel axis') :
    axisPauliMatrix axis * axisPauliMatrix axis' -
        axisPauliMatrix axis' * axisPauliMatrix axis ≠ 0 := by
  intro hzero
  have hcomm := blochPauliMatrix_commutator (blochVector axis) (blochVector axis')
  rw [blochPauliMatrix_blochVector, blochPauliMatrix_blochVector, hzero] at hcomm
  have hscalar : (2 : Complex) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hpauli : blochPauliMatrix (blochVector axis ⨯₃ blochVector axis') = 0 := by
    apply smul_right_injective SingleQubitMatrix hscalar
    simpa using hcomm.symm
  have hcross : blochVector axis ⨯₃ blochVector axis' = 0 := by
    have h2 : (blochVector axis ⨯₃ blochVector axis') 2 = 0 := by
      simpa [blochPauliMatrix] using congrFun (congrFun hpauli 0) 0
    have h01 := congrFun (congrFun hpauli 0) 1
    have h0 : (blochVector axis ⨯₃ blochVector axis') 0 = 0 := by
      have hre := congrArg Complex.re h01
      simpa [blochPauliMatrix, Complex.mul_re] using hre
    have h1 : (blochVector axis ⨯₃ blochVector axis') 1 = 0 := by
      have him := congrArg Complex.im h01
      have hneg : -(blochVector axis ⨯₃ blochVector axis') 1 = 0 := by
        simpa [blochPauliMatrix, Complex.mul_im] using him
      exact neg_eq_zero.mp hneg
    ext i
    fin_cases i <;> assumption
  have hsq : blochCrossSq axis axis' = 0 := by
    rw [show blochCrossSq axis axis' =
      (blochVector axis ⨯₃ blochVector axis') 0 ^ 2 +
        (blochVector axis ⨯₃ blochVector axis') 1 ^ 2 +
        (blochVector axis ⨯₃ blochVector axis') 2 ^ 2 by
      simp [blochCrossSq, blochVector, cross_apply]]
    simp [hcross]
  exact UnitBlochAxis.nonparallel_crossSq_ne_zero h hsq

/-- The determinant-one subgroup of concrete one-qubit unitaries. -/
def determinantOneSubgroup : Subgroup SingleQubitGate where
  carrier := {U | (U : SingleQubitMatrix).det = 1}
  one_mem' := by simp
  mul_mem' := by
    intro U V hU hV
    change ((U * V : SingleQubitGate) : SingleQubitMatrix).det = 1
    rw [Matrix.UnitaryGroup.mul_val, Matrix.det_mul, hU, hV, mul_one]
  inv_mem' := by
    intro U hU
    change ((U⁻¹ : SingleQubitGate) : SingleQubitMatrix).det = 1
    rw [Matrix.UnitaryGroup.inv_val]
    change ((U : SingleQubitMatrix)ᴴ).det = 1
    rw [Matrix.det_conjTranspose, hU]
    simp

/-- The concrete group of determinant-one one-qubit unitaries. -/
abbrev SingleQubitSpecialUnitary := determinantOneSubgroup

/-- An axis-circle gate regarded as an element of the determinant-one group. -/
def axisCircleSU (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    SingleQubitSpecialUnitary :=
  ⟨axisCircle axis t, axisCircle_det axis t⟩

@[simp] theorem axisCircleSU_coe (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircleSU axis t : SingleQubitGate) = axisCircle axis t := rfl

@[simp] theorem axisCircleSU_matrix (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) :
    (axisCircleSU axis t : SingleQubitMatrix) = axisCircleMatrix axis (AddCircle.toCircle t) :=
  axisCircle_matrix axis t

example : IsTopologicalGroup SingleQubitGate := by infer_instance
example : IsTopologicalGroup SingleQubitSpecialUnitary := by infer_instance
/-- A determinant-one matrix in scalar-plus-Bloch-vector coordinates. -/
def su2Matrix (r : Real) (v : Fin 3 → Real) : SingleQubitMatrix :=
  (r : Complex) • 1 - Complex.I • blochPauliMatrix v

/-- Quaternion multiplication on scalar-plus-Bloch-vector coordinates. -/
def su2VectorProduct (r s : Real) (v w : Fin 3 → Real) : Fin 3 → Real :=
  r • w + s • v + v ⨯₃ w

/-- Multiplication of scalar-plus-Bloch-vector matrices is quaternion multiplication. -/
theorem su2Matrix_mul (r s : Real) (v w : Fin 3 → Real) :
    su2Matrix r v * su2Matrix s w =
      su2Matrix (r * s - v ⬝ᵥ w) (su2VectorProduct r s v w) := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1 : Complex) * Complex.I := by rw [Complex.I_sq]
      _ = -Complex.I := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, su2VectorProduct, blochPauliMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vec3_dotProduct, cross_apply] <;>
    ring_nf
  all_goals
    simp only [hI3, Complex.I_sq, Complex.I_pow_four]
    ring

/-- The scalar-plus-vector matrix with a unit axis is the #728 axis-circle matrix. -/
theorem su2Matrix_axisLinear (axis : UnitBlochAxis) (r s : Real) :
    su2Matrix r (s • blochVector axis) = axisLinearMatrix axis r s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, blochVector, blochPauliMatrix, axisLinearMatrix, axisPauliMatrix] <;>
    ring

/-- Conjugate transpose changes the sign of the Bloch vector. -/
theorem su2Matrix_conjTranspose (r : Real) (v : Fin 3 → Real) :
    (su2Matrix r v).conjTranspose = su2Matrix r (-v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, blochPauliMatrix, Complex.conj_ofReal] <;>
    ring

@[simp] theorem blochPauliMatrix_zero : blochPauliMatrix (0 : Fin 3 → Real) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochPauliMatrix]

/-- Squaring a raw Pauli matrix gives the vector's squared norm. -/
theorem blochPauliMatrix_sq (v : Fin 3 → Real) :
    blochPauliMatrix v * blochPauliMatrix v = ((v ⬝ᵥ v : Real) : Complex) • 1 := by
  rw [blochPauliMatrix_mul]
  simp [blochPauliMatrix_zero]

/-- Unit scalar-plus-vector coordinates define a unitary matrix. -/
theorem su2Matrix_unitary (r : Real) (v : Fin 3 → Real)
    (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    su2Matrix r v ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, su2Matrix_conjTranspose]
  rw [su2Matrix_mul]
  have hvec : su2VectorProduct r r v (-v) = 0 := by
    ext i
    simp [su2VectorProduct]
  rw [hvec]
  simp only [su2Matrix, blochPauliMatrix_zero, smul_zero, sub_zero]
  have hnormC : ((r ^ 2 + v ⬝ᵥ v : Real) : Complex) = 1 := by
    exact_mod_cast hnorm
  simpa [pow_two] using congrArg (fun z : Complex => z • (1 : SingleQubitMatrix)) hnormC

/-- A direct determinant formula for scalar-plus-vector coordinates. -/
theorem su2Matrix_det_formula (r : Real) (v : Fin 3 → Real) :
    (su2Matrix r v).det = ((r ^ 2 + v ⬝ᵥ v : Real) : Complex) := by
  rw [Matrix.det_fin_two]
  simp [su2Matrix, blochPauliMatrix]
  rw [Matrix.vec3_dotProduct]
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_four]
  push_cast
  ring

/-- Unit scalar-plus-vector coordinates have determinant one. -/
theorem su2Matrix_det (r : Real) (v : Fin 3 → Real)
    (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    (su2Matrix r v).det = 1 := by
  rw [su2Matrix_det_formula, hnorm]
  norm_num

/-- The determinant-one gate represented by unit scalar-plus-vector coordinates. -/
def su2Gate (r : Real) (v : Fin 3 → Real) (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    SingleQubitSpecialUnitary :=
  ⟨⟨su2Matrix r v, su2Matrix_unitary r v hnorm⟩, su2Matrix_det r v hnorm⟩

@[simp] theorem su2Gate_matrix (r : Real) (v : Fin 3 → Real)
    (hnorm : r ^ 2 + v ⬝ᵥ v = 1) :
    (su2Gate r v hnorm : SingleQubitMatrix) = su2Matrix r v := rfl
/-- The additive-circle parameter recovers the usual complex exponential. -/
theorem addCircle_toCircle_two_pi (x : Real) :
    (AddCircle.toCircle (x : AddCircle (2 * Real.pi)) : Complex) =
      (Real.cos x : Complex) + (Real.sin x : Complex) * Complex.I := by
  change (Circle.exp (2 * Real.pi / (2 * Real.pi) * x) : Complex) = _
  have hscale : 2 * Real.pi / (2 * Real.pi) * x = x := by
    field_simp [Real.pi_ne_zero]
  rw [hscale, Circle.coe_exp, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- A real-parameterized special-unitary axis circle. -/
def axisCircleRealSU (axis : UnitBlochAxis) (x : Real) : SingleQubitSpecialUnitary :=
  axisCircleSU axis (x : AddCircle (2 * Real.pi))

@[simp] theorem axisCircleRealSU_matrix (axis : UnitBlochAxis) (x : Real) :
    (axisCircleRealSU axis x : SingleQubitMatrix) =
      su2Matrix (Real.cos x) (Real.sin x • blochVector axis) := by
  rw [axisCircleRealSU, axisCircleSU_matrix, axisCircleMatrix]
  have hz := addCircle_toCircle_two_pi x
  rw [hz]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    sub_zero, add_zero]
  simpa [zero_add] using (su2Matrix_axisLinear axis (Real.cos x) (Real.sin x)).symm

/-- Real axis-circle coordinates are unit scalar-plus-vector coordinates. -/
theorem axisCircleRealSU_norm (axis : UnitBlochAxis) (x : Real) :
    Real.cos x ^ 2 + (Real.sin x • blochVector axis) ⬝ᵥ
      (Real.sin x • blochVector axis) = 1 := by
  simp [smul_eq_mul, blochVector_dot_self]
  simpa [pow_two] using Real.cos_sq_add_sin_sq x
/-- The scalar coordinate after the first two factors of an alternating axis word. -/
def alternatingWordFirstScalar (axis axis' : UnitBlochAxis) (x y : Real) : Real :=
  Real.cos x * Real.cos y - Real.sin x * Real.sin y * blochDot axis axis'

/-- The vector coordinate after the first two factors of an alternating axis word. -/
def alternatingWordFirstVector (axis axis' : UnitBlochAxis) (x y : Real) : Fin 3 → Real :=
  Real.cos x • (Real.sin y • blochVector axis') +
    Real.cos y • (Real.sin x • blochVector axis) +
    (Real.sin x • blochVector axis) ⨯₃ (Real.sin y • blochVector axis')

/-- The scalar coordinate of the finite three-factor alternating word. -/
def alternatingWordScalar (axis axis' : UnitBlochAxis) (x y z : Real) : Real :=
  alternatingWordFirstScalar axis axis' x y * Real.cos z -
    alternatingWordFirstVector axis axis' x y ⬝ᵥ (Real.sin z • blochVector axis)

/-- The vector coordinate of the finite three-factor alternating word. -/
def alternatingWordVector (axis axis' : UnitBlochAxis) (x y z : Real) : Fin 3 → Real :=
  alternatingWordFirstScalar axis axis' x y • (Real.sin z • blochVector axis) +
    Real.cos z • alternatingWordFirstVector axis axis' x y +
    alternatingWordFirstVector axis axis' x y ⨯₃ (Real.sin z • blochVector axis)

/-- The explicit finite alternating word made from the two complete axis circles. -/
def alternatingAxisWord (axis axis' : UnitBlochAxis) (x y z : Real) :
    SingleQubitSpecialUnitary :=
  axisCircleRealSU axis x * axisCircleRealSU axis' y * axisCircleRealSU axis z

/-- Every finite alternating word belongs to a subgroup containing both full circles. -/
theorem alternatingAxisWord_mem (K : Subgroup SingleQubitSpecialUnitary)
    (axis axis' : UnitBlochAxis)
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K)
    (x y z : Real) : alternatingAxisWord axis axis' x y z ∈ K := by
  apply K.mul_mem
  · apply K.mul_mem
    · exact haxis (x : AddCircle (2 * Real.pi))
    · exact haxis' (y : AddCircle (2 * Real.pi))
  · exact haxis (z : AddCircle (2 * Real.pi))

/-- The alternating word has exactly the displayed scalar-plus-vector coordinates. -/
theorem alternatingAxisWord_matrix (axis axis' : UnitBlochAxis) (x y z : Real) :
    (alternatingAxisWord axis axis' x y z : SingleQubitMatrix) =
      su2Matrix (alternatingWordScalar axis axis' x y z)
        (alternatingWordVector axis axis' x y z) := by
  change (axisCircleRealSU axis x : SingleQubitMatrix) *
      (axisCircleRealSU axis' y : SingleQubitMatrix) *
      (axisCircleRealSU axis z : SingleQubitMatrix) = _
  rw [axisCircleRealSU_matrix, axisCircleRealSU_matrix, axisCircleRealSU_matrix]
  rw [su2Matrix_mul, su2Matrix_mul]
  simp [alternatingWordScalar, alternatingWordVector, alternatingWordFirstScalar,
    alternatingWordFirstVector, su2VectorProduct]
  congr 1
  ring
  ext i
  ring
/-- Determinant-one unitarity identifies conjugate transpose with the adjugate. -/
theorem special_conjTranspose_eq_adjugate (U : SingleQubitSpecialUnitary) :
    (U : SingleQubitMatrix).conjTranspose = Matrix.adjugate (U : SingleQubitMatrix) := by
  let A : SingleQubitMatrix := U
  have hunit : A * A.conjTranspose = 1 := by
    have h := U.1.property
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hadj : Matrix.adjugate A * A = 1 := by
    rw [Matrix.adjugate_mul, U.2]
    simp
  change A.conjTranspose = Matrix.adjugate A
  calc
    A.conjTranspose = 1 * A.conjTranspose := by simp
    _ = (Matrix.adjugate A * A) * A.conjTranspose := by rw [hadj]
    _ = Matrix.adjugate A * (A * A.conjTranspose) := by rw [Matrix.mul_assoc]
    _ = Matrix.adjugate A := by rw [hunit, Matrix.mul_one]
/-- The real scalar coordinate of a determinant-one one-qubit unitary. -/
def specialScalar (U : SingleQubitSpecialUnitary) : Real :=
  ((U : SingleQubitMatrix) 0 0).re

/-- The real Bloch-vector coordinate of a determinant-one one-qubit unitary. -/
def specialVector (U : SingleQubitSpecialUnitary) : Fin 3 → Real :=
  ![-((U : SingleQubitMatrix) 0 1).im,
    -((U : SingleQubitMatrix) 0 1).re,
    -((U : SingleQubitMatrix) 0 0).im]

/-- The lower matrix entries of a determinant-one unitary are fixed by the upper row. -/
theorem special_matrix_lower_entries (U : SingleQubitSpecialUnitary) :
    (U : SingleQubitMatrix) 1 1 = star ((U : SingleQubitMatrix) 0 0) ∧
      (U : SingleQubitMatrix) 1 0 = -star ((U : SingleQubitMatrix) 0 1) := by
  have h := special_conjTranspose_eq_adjugate U
  constructor
  · have h00 := congrFun (congrFun h 0) 0
    simpa [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] using h00.symm
  · have h01 := congrFun (congrFun h 0) 1
    have h01' := congrArg star h01
    simpa [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] using h01'

/-- Every determinant-one unitary has scalar-plus-Bloch-vector coordinates. -/
theorem special_coordinate_matrix (U : SingleQubitSpecialUnitary) :
    (U : SingleQubitMatrix) = su2Matrix (specialScalar U) (specialVector U) := by
  rcases special_matrix_lower_entries U with ⟨h11, h10⟩
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
  · apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
  · change (U : SingleQubitMatrix) 1 0 = _
    rw [h10]
    apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]
  · change (U : SingleQubitMatrix) 1 1 = _
    rw [h11]
    apply Complex.ext <;> simp [su2Matrix, blochPauliMatrix, specialScalar, specialVector]

/-- The extracted scalar-plus-vector coordinates have unit norm. -/
theorem special_coordinate_norm (U : SingleQubitSpecialUnitary) :
    specialScalar U ^ 2 + specialVector U ⬝ᵥ specialVector U = 1 := by
  have hdet : (su2Matrix (specialScalar U) (specialVector U)).det = 1 := by
    rw [← special_coordinate_matrix U]
    exact U.2
  rw [su2Matrix_det_formula] at hdet
  exact_mod_cast hdet


/-- The finite alternating word's Bloch-vector coordinate map on three real parameters. -/
def alternatingWordMap (axis axis' : UnitBlochAxis) (p : Fin 3 → Real) : Fin 3 → Real :=
  alternatingWordVector axis axis' (p 0) (p 1) (p 2)

/-- The alternating Bloch-vector coordinate map is smooth. -/
theorem alternatingWordMap_contDiff (axis axis' : UnitBlochAxis) :
    ContDiff Real ⊤ (alternatingWordMap axis axis') := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;>
    simp [alternatingWordMap, alternatingWordVector, alternatingWordFirstScalar,
      alternatingWordFirstVector, blochVector, blochDot, cross_apply] <;>
    fun_prop
/-- The parameter point used for the local alternating-word chart. -/
def alternatingWordBase : Fin 3 → Real := ![0, Real.pi / 4, 0]

/-- Scalar coefficient of the first axis in the local alternating-word chart. -/
def alternatingWordCoeffA (axis axis' : UnitBlochAxis) (p : Fin 3 → Real) : Real :=
  let x := p 0
  let y := p 1
  let z := p 2
  (Real.cos x * Real.cos y - Real.sin x * Real.sin y * blochDot axis axis') *
      Real.sin z +
    Real.cos z * Real.cos y * Real.sin x -
    Real.sin z * Real.sin x * Real.sin y * blochDot axis axis'

/-- Scalar coefficient of the second axis in the local alternating-word chart. -/
def alternatingWordCoeffB (_axis _axis' : UnitBlochAxis) (p : Fin 3 → Real) : Real :=
  let x := p 0
  let y := p 1
  let z := p 2
  Real.cos z * Real.cos x * Real.sin y + Real.sin z * Real.sin x * Real.sin y

/-- Scalar coefficient of the cross axis in the local alternating-word chart. -/
def alternatingWordCoeffCross (_axis _axis' : UnitBlochAxis) (p : Fin 3 → Real) : Real :=
  let x := p 0
  let y := p 1
  let z := p 2
  Real.cos z * Real.sin x * Real.sin y - Real.sin z * Real.cos x * Real.sin y

/-- Bilinearity of the concrete three-dimensional cross product. -/
theorem smul_cross_smul (r s : Real) (v w : Fin 3 → Real) :
    (r • v) ⨯₃ (s • w) = (r * s) • (v ⨯₃ w) := by
  ext i
  fin_cases i <;> simp [cross_apply, smul_eq_mul] <;> ring

/-- Additivity of the concrete cross product in its first argument. -/
theorem add_cross (u v w : Fin 3 → Real) :
    (u + v) ⨯₃ w = u ⨯₃ w + v ⨯₃ w := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- The cross of the two Bloch axes crossed back with the first axis is explicit. -/
theorem blochCross_cross_blochVector (axis axis' : UnitBlochAxis) :
    (blochVector axis ⨯₃ blochVector axis') ⨯₃ blochVector axis =
      blochVector axis' - blochDot axis axis' • blochVector axis := by
  rw [cross_cross_eq_smul_sub_smul]
  simp [blochVector_dot, blochDot]
  ring
/-- The local alternating-word map has coordinates in the axis, second-axis, cross basis. -/
theorem alternatingWordMap_formula (axis axis' : UnitBlochAxis) (p : Fin 3 → Real) :
    alternatingWordMap axis axis' p =
      alternatingWordCoeffA axis axis' p • blochVector axis +
        alternatingWordCoeffB axis axis' p • blochVector axis' +
        alternatingWordCoeffCross axis axis' p •
          (blochVector axis ⨯₃ blochVector axis') := by
  simp only [alternatingWordMap, alternatingWordVector, alternatingWordFirstScalar,
    alternatingWordFirstVector, alternatingWordCoeffA, alternatingWordCoeffB,
    alternatingWordCoeffCross, smul_cross_smul, smul_smul]
  rw [add_cross, add_cross]
  rw [smul_cross_smul, smul_cross_smul, smul_cross_smul]
  rw [← cross_anticomm (blochVector axis) (blochVector axis')]
  rw [cross_self]
  rw [blochCross_cross_blochVector]
  module
/-- A coordinate projection on the three-parameter word space. -/
def wordParameterProjection (i : Fin 3) : (Fin 3 → Real) →L[Real] Real :=
  ContinuousLinearMap.proj i

/-- Fréchet derivative of a sine coordinate on the three-parameter word space. -/
theorem hasFDerivAt_sin_parameter (i : Fin 3) (p : Fin 3 → Real) :
    HasFDerivAt (fun q : Fin 3 → Real => Real.sin (q i))
      (Real.cos (p i) • wordParameterProjection i) p := by
  have hproj : HasFDerivAt (fun q : Fin 3 → Real => q i) (wordParameterProjection i) p := by
    simpa [wordParameterProjection] using (hasFDerivAt_apply i p)
  exact hproj.sin

/-- Fréchet derivative of a cosine coordinate on the three-parameter word space. -/
theorem hasFDerivAt_cos_parameter (i : Fin 3) (p : Fin 3 → Real) :
    HasFDerivAt (fun q : Fin 3 → Real => Real.cos (q i))
      (-Real.sin (p i) • wordParameterProjection i) p := by
  have hproj : HasFDerivAt (fun q : Fin 3 → Real => q i) (wordParameterProjection i) p := by
    simpa [wordParameterProjection] using (hasFDerivAt_apply i p)
  exact hproj.cos
/-- The first local word coefficient has the stated derivative at the chart base. -/
theorem alternatingWordCoeffA_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordCoeffA axis axis')
      (Real.cos (Real.pi / 4) • wordParameterProjection 0 +
        Real.cos (Real.pi / 4) • wordParameterProjection 2)
      alternatingWordBase := by
  have hsx := hasFDerivAt_sin_parameter 0 alternatingWordBase
  have hcx := hasFDerivAt_cos_parameter 0 alternatingWordBase
  have hsy := hasFDerivAt_sin_parameter 1 alternatingWordBase
  have hcy := hasFDerivAt_cos_parameter 1 alternatingWordBase
  have hsz := hasFDerivAt_sin_parameter 2 alternatingWordBase
  have hcz := hasFDerivAt_cos_parameter 2 alternatingWordBase
  have hr := (hcx.mul hcy).sub (((hsx.mul hsy).mul_const (blochDot axis axis')))
  have h := (hr.mul hsz).add ((hcz.mul hcy).mul hsx) |>.sub
    ((((hsz.mul hsx).mul hsy).mul_const (blochDot axis axis')))
  convert h using 1 <;> try rfl
  ext q
  simp [alternatingWordBase, Real.sin_pi_div_four, Real.cos_pi_div_four,
    wordParameterProjection, ContinuousLinearMap.smul_apply] <;> ring
/-- The second local word coefficient has the stated derivative at the chart base. -/
theorem alternatingWordCoeffB_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordCoeffB axis axis')
      (Real.cos (Real.pi / 4) • wordParameterProjection 1)
      alternatingWordBase := by
  have hsx := hasFDerivAt_sin_parameter 0 alternatingWordBase
  have hcx := hasFDerivAt_cos_parameter 0 alternatingWordBase
  have hsy := hasFDerivAt_sin_parameter 1 alternatingWordBase
  have hsz := hasFDerivAt_sin_parameter 2 alternatingWordBase
  have hcz := hasFDerivAt_cos_parameter 2 alternatingWordBase
  have h := ((hcz.mul hcx).mul hsy).add ((hsz.mul hsx).mul hsy)
  convert h using 1 <;> try rfl
  ext q
  simp [alternatingWordBase, Real.sin_pi_div_four, Real.cos_pi_div_four,
    wordParameterProjection, ContinuousLinearMap.smul_apply]

/-- The cross-axis local word coefficient has the stated derivative at the chart base. -/
theorem alternatingWordCoeffCross_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordCoeffCross axis axis')
      (Real.sin (Real.pi / 4) • wordParameterProjection 0 -
        Real.sin (Real.pi / 4) • wordParameterProjection 2)
      alternatingWordBase := by
  have hsx := hasFDerivAt_sin_parameter 0 alternatingWordBase
  have hcx := hasFDerivAt_cos_parameter 0 alternatingWordBase
  have hsy := hasFDerivAt_sin_parameter 1 alternatingWordBase
  have hsz := hasFDerivAt_sin_parameter 2 alternatingWordBase
  have hcz := hasFDerivAt_cos_parameter 2 alternatingWordBase
  have h := ((hcz.mul hsx).mul hsy).sub ((hsz.mul hcx).mul hsy)
  convert h using 1 <;> try rfl
  ext q
  simp [alternatingWordBase, Real.sin_pi_div_four, Real.cos_pi_div_four,
    wordParameterProjection]

/-- The local alternating-word coordinate derivative at its chart base. -/
def alternatingWordDerivative (axis axis' : UnitBlochAxis) :
    (Fin 3 → Real) →ₗ[Real] Fin 3 → Real where
  toFun := fun h =>
    (Real.cos (Real.pi / 4) * (h 0 + h 2)) • blochVector axis +
      (Real.cos (Real.pi / 4) * h 1) • blochVector axis' +
      (Real.sin (Real.pi / 4) * (h 0 - h 2)) •
        (blochVector axis ⨯₃ blochVector axis')
  map_add' := by
    intro h k
    ext i
    simp [smul_eq_mul]
    ring
  map_smul' := by
    intro c h
    ext i
    simp [smul_eq_mul]
    ring

/-- The continuous local alternating-word coordinate derivative. -/
def alternatingWordDerivativeCLM (axis axis' : UnitBlochAxis) :
    (Fin 3 → Real) →L[Real] Fin 3 → Real :=
  ⟨alternatingWordDerivative axis axis',
    (alternatingWordDerivative axis axis').continuous_of_finiteDimensional⟩

/-- The local alternating-word coordinate map has the displayed derivative. -/
theorem alternatingWordMap_hasFDerivAt (axis axis' : UnitBlochAxis) :
    HasFDerivAt (alternatingWordMap axis axis')
      (alternatingWordDerivativeCLM axis axis') alternatingWordBase := by
  have hA := alternatingWordCoeffA_hasFDerivAt axis axis'
  have hB := alternatingWordCoeffB_hasFDerivAt axis axis'
  have hC := alternatingWordCoeffCross_hasFDerivAt axis axis'
  have h := (hA.smul_const (blochVector axis)).add
    ((hB.smul_const (blochVector axis')).add
      (hC.smul_const (blochVector axis ⨯₃ blochVector axis')))
  convert h using 1 <;> try rfl
  · funext p
    rw [alternatingWordMap_formula]
    simp only [Pi.add_apply]
    abel
  · ext q i
    simp [alternatingWordDerivativeCLM, alternatingWordDerivative,
      wordParameterProjection, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul] <;> ring

/-- The squared norm of the explicit Bloch cross product is the transparent cross square. -/
theorem blochCross_dot_self (axis axis' : UnitBlochAxis) :
    (blochVector axis ⨯₃ blochVector axis') ⬝ᵥ
      (blochVector axis ⨯₃ blochVector axis') = blochCrossSq axis axis' := by
  simp [blochCrossSq, blochVector, cross_apply]
  ring

/-- The local alternating-word derivative is injective for nonparallel axes. -/
theorem alternatingWordDerivative_injective (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    Function.Injective (alternatingWordDerivative axis axis') := by
  intro h k heq
  apply sub_eq_zero.mp
  let u : Fin 3 → Real := h - k
  have hzero : alternatingWordDerivative axis axis' u = 0 := by
    dsimp [u]
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  have hcross := congrArg (fun q =>
    (blochVector axis ⨯₃ blochVector axis') ⬝ᵥ q) hzero
  have haxis := congrArg (fun q => blochVector axis ⬝ᵥ q) hzero
  have haxis' := congrArg (fun q => blochVector axis' ⬝ᵥ q) hzero
  have hcross' :
      Real.sin (Real.pi / 4) * (u 0 - u 2) * blochCrossSq axis axis' = 0 := by
    simpa [alternatingWordDerivative, dotProduct_add, dotProduct_smul,
      dotProduct_comm, blochCross_dot_self, smul_eq_mul] using hcross
  have hsin : Real.sin (Real.pi / 4) ≠ 0 := by
    rw [Real.sin_pi_div_four]
    positivity
  have hdiff : u 0 - u 2 = 0 := by
    have hprod : Real.sin (Real.pi / 4) * (u 0 - u 2) = 0 :=
      (mul_eq_zero.mp hcross').resolve_right (ne_of_gt hnonparallel)
    exact (mul_eq_zero.mp hprod).resolve_left hsin
  have hu2 : u 2 = u 0 := (sub_eq_zero.mp hdiff).symm
  have ha :
      (2 * Real.cos (Real.pi / 4) * u 0) +
        (Real.cos (Real.pi / 4) * u 1) * blochDot axis axis' = 0 := by
    convert haxis using 1 <;>
      simp [alternatingWordDerivative, dotProduct_add, dotProduct_smul,
        blochVector_dot_self, blochVector_dot, smul_eq_mul, hu2] <;>
      ring
  have hb :
      (2 * Real.cos (Real.pi / 4) * u 0) * blochDot axis axis' +
        (Real.cos (Real.pi / 4) * u 1) = 0 := by
    convert haxis' using 1 <;>
      simp [alternatingWordDerivative, dotProduct_add, dotProduct_smul,
        blochVector_dot_self, blochVector_dot, blochDot, smul_eq_mul, hu2] <;>
      ring
  have hA :
      (2 * Real.cos (Real.pi / 4) * u 0) *
        (1 - blochDot axis axis' ^ 2) = 0 := by
    linear_combination ha - blochDot axis axis' * hb
  have hA0 : 2 * Real.cos (Real.pi / 4) * u 0 = 0 := by
    apply (mul_eq_zero.mp hA).resolve_right
    rw [← blochCrossSq_eq_one_sub_blochDot_sq]
    exact ne_of_gt hnonparallel
  have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  have hu0 : u 0 = 0 := by
    rcases mul_eq_zero.mp hA0 with hleft | hu0
    · exfalso
      rcases mul_eq_zero.mp hleft with htwo | hcos0
      · norm_num at htwo
      · exact hcos hcos0
    · exact hu0
  have hu1 : u 1 = 0 := by
    rw [hu0] at hb
    have hcu : Real.cos (Real.pi / 4) * u 1 = 0 := by
      convert hb using 1 <;> ring
    exact (mul_eq_zero.mp hcu).resolve_left hcos
  have hu : u = 0 := by
    ext i
    fin_cases i <;> simp [u, hu0, hu1, hu2]
  simpa [u] using hu

/-- The nonparallel local word derivative is a continuous linear equivalence. -/
noncomputable def alternatingWordDerivativeEquiv (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    (Fin 3 → Real) ≃L[Real] Fin 3 → Real := by
  apply ContinuousLinearEquiv.ofBijective (alternatingWordDerivativeCLM axis axis')
  · exact LinearMap.ker_eq_bot.mpr (alternatingWordDerivative_injective axis axis' hnonparallel)
  · apply LinearMap.range_eq_top.mpr
    exact LinearMap.surjective_of_injective
      (alternatingWordDerivative_injective axis axis' hnonparallel)

/-- The inverse-function-theorem local homeomorphism for the alternating word map. -/
noncomputable def alternatingWordLocalHomeomorph (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    OpenPartialHomeomorph (Fin 3 → Real) (Fin 3 → Real) := by
  have hcont : ContDiffAt Real ⊤ (alternatingWordMap axis axis') alternatingWordBase :=
    (alternatingWordMap_contDiff axis axis').contDiffAt
  refine hcont.toOpenPartialHomeomorph (alternatingWordMap axis axis')
    (f' := alternatingWordDerivativeEquiv axis axis' hnonparallel) ?_ (by simp)
  exact alternatingWordMap_hasFDerivAt axis axis'

/-- The scalar coordinate is continuous on the determinant-one group. -/
theorem continuous_specialScalar : Continuous specialScalar := by
  unfold specialScalar
  have hgate : Continuous (fun U : SingleQubitGate => (U : SingleQubitMatrix)) :=
    continuous_induced_dom
  exact Complex.continuous_re.comp
    ((continuous_apply 0).comp ((continuous_apply 0).comp
      (hgate.comp continuous_subtype_val)))

/-- The Bloch-vector coordinate is continuous on the determinant-one group. -/
theorem continuous_specialVector : Continuous specialVector := by
  have hgate : Continuous (fun U : SingleQubitGate => (U : SingleQubitMatrix)) :=
    continuous_induced_dom
  have hmatrix : Continuous (fun U : SingleQubitSpecialUnitary =>
      (U : SingleQubitMatrix)) :=
    hgate.comp continuous_subtype_val
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · exact (Complex.continuous_im.comp
      ((continuous_apply 1).comp ((continuous_apply 0).comp hmatrix))).neg
  · exact (Complex.continuous_re.comp
      ((continuous_apply 1).comp ((continuous_apply 0).comp hmatrix))).neg
  · exact (Complex.continuous_im.comp
      ((continuous_apply 0).comp ((continuous_apply 0).comp hmatrix))).neg
/-- The scalar coordinate of an alternating word is the displayed word scalar. -/
theorem specialScalar_alternatingAxisWord (axis axis' : UnitBlochAxis) (x y z : Real) :
    specialScalar (alternatingAxisWord axis axis' x y z) =
      alternatingWordScalar axis axis' x y z := by
  unfold specialScalar
  rw [alternatingAxisWord_matrix]
  simp [su2Matrix, blochPauliMatrix]

/-- The vector coordinate of an alternating word is the displayed word vector. -/
theorem specialVector_alternatingAxisWord (axis axis' : UnitBlochAxis) (x y z : Real) :
    specialVector (alternatingAxisWord axis axis' x y z) =
      alternatingWordVector axis axis' x y z := by
  ext i
  fin_cases i <;>
    simp only [specialVector, Matrix.vecEmpty, Fin.isValue]
  all_goals
    rw [alternatingAxisWord_matrix]
    simp [su2Matrix, blochPauliMatrix]

/-- The local alternating-word scalar is positive at the chart base. -/
theorem alternatingWordScalar_base (axis axis' : UnitBlochAxis) :
    alternatingWordScalar axis axis' 0 (Real.pi / 4) 0 = Real.cos (Real.pi / 4) := by
  simp [alternatingWordScalar, alternatingWordFirstScalar, alternatingWordFirstVector]

/-- The parameter set on which the local word scalar has positive sign. -/
def alternatingWordPositiveSet (axis axis' : UnitBlochAxis) : Set (Fin 3 → Real) :=
  {p | 0 < alternatingWordScalar axis axis' (p 0) (p 1) (p 2)}

/-- The positive-scalar word parameter set is open. -/
theorem isOpen_alternatingWordPositiveSet (axis axis' : UnitBlochAxis) :
    IsOpen (alternatingWordPositiveSet axis axis') := by
  apply isOpen_lt continuous_const
  simp only [alternatingWordScalar,
    alternatingWordFirstScalar, alternatingWordFirstVector]
  fun_prop

/-- The local word chart restricted to positive scalar coordinate. -/
noncomputable def alternatingWordPositiveLocalHomeomorph (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    OpenPartialHomeomorph (Fin 3 → Real) (Fin 3 → Real) :=
  (alternatingWordLocalHomeomorph axis axis' hnonparallel).restrOpen
    (alternatingWordPositiveSet axis axis') (isOpen_alternatingWordPositiveSet axis axis')

/-- The alternating-word chart base belongs to the unrestricted local source. -/
theorem alternatingWordBase_mem_localHomeomorph_source (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis') :
    alternatingWordBase ∈ (alternatingWordLocalHomeomorph axis axis' hnonparallel).source := by
  unfold alternatingWordLocalHomeomorph
  apply ContDiffAt.mem_toOpenPartialHomeomorph_source

/-- The alternating-word chart base has positive scalar coordinate. -/
theorem alternatingWordBase_mem_positiveSet (axis axis' : UnitBlochAxis) :
    alternatingWordBase ∈ alternatingWordPositiveSet axis axis' := by
  change 0 < alternatingWordScalar axis axis' 0 (Real.pi / 4) 0
  rw [alternatingWordScalar_base, Real.cos_pi_div_four]
  positivity
/-- The alternating-word chart base belongs to the positive local source. -/
theorem alternatingWordBase_mem_positiveLocalHomeomorph_source
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis') :
    alternatingWordBase ∈
      (alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel).source := by
  rw [alternatingWordPositiveLocalHomeomorph,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨alternatingWordBase_mem_localHomeomorph_source axis axis' hnonparallel,
    alternatingWordBase_mem_positiveSet axis axis'⟩



/-- A positive-scalar special unitary in the local word target is a finite word. -/
theorem exists_alternatingAxisWord_of_mem_positiveLocalTarget
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis')
    (U : SingleQubitSpecialUnitary)
    (hscalar : 0 < specialScalar U)
    (htarget : specialVector U ∈
      (alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel).target) :
    ∃ p : Fin 3 → Real,
      alternatingAxisWord axis axis' (p 0) (p 1) (p 2) = U := by
  let H := alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel
  let p : Fin 3 → Real := H.symm (specialVector U)
  have hpSource : p ∈ H.source := by
    simpa [p] using H.symm.map_source htarget
  have hpSource' : p ∈
      (alternatingWordLocalHomeomorph axis axis' hnonparallel).source ∩
        alternatingWordPositiveSet axis axis' := by
    simpa [H, alternatingWordPositiveLocalHomeomorph,
      OpenPartialHomeomorph.restrOpen_source] using hpSource
  have hpMap : alternatingWordMap axis axis' p = specialVector U := by
    exact H.right_inv htarget
  let W := alternatingAxisWord axis axis' (p 0) (p 1) (p 2)
  have hscalarW : 0 < specialScalar W := by
    rw [specialScalar_alternatingAxisWord]
    simpa [alternatingWordPositiveSet] using hpSource'.2
  have hvectorW : specialVector W = alternatingWordMap axis axis' p := by
    simpa [W, alternatingWordMap] using
      (specialVector_alternatingAxisWord axis axis' (p 0) (p 1) (p 2))
  have hvector : specialVector U = specialVector W := by
    rw [hvectorW, hpMap]
  have hnormU := special_coordinate_norm U
  have hnormW := special_coordinate_norm W
  have hsquares : specialScalar U ^ 2 = specialScalar W ^ 2 := by
    rw [hvector] at hnormU
    linarith
  have hsum : 0 < specialScalar U + specialScalar W := add_pos hscalar hscalarW
  have hproduct :
      (specialScalar U - specialScalar W) *
        (specialScalar U + specialScalar W) = 0 := by
    nlinarith [hsquares]
  have hscalarEq : specialScalar U = specialScalar W :=
    sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hsum))
  refine ⟨p, ?_⟩
  change W = U
  apply Subtype.ext
  apply Subtype.ext
  change (W : SingleQubitMatrix) = (U : SingleQubitMatrix)
  rw [special_coordinate_matrix W, special_coordinate_matrix U, hscalarEq, hvector]

/-- A subgroup containing two nonparallel complete axis circles is open. -/
theorem subgroup_isOpen_of_contains_nonparallel_axisCircles
    (K : Subgroup SingleQubitSpecialUnitary) (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K) :
    IsOpen (K : Set SingleQubitSpecialUnitary) := by
  let H := alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel
  let V : Set SingleQubitSpecialUnitary :=
    {U | 0 < specialScalar U ∧ specialVector U ∈ H.target}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const continuous_specialScalar).inter
      (continuous_specialVector.isOpen_preimage H.target H.open_target)
  let W := alternatingAxisWord axis axis' 0 (Real.pi / 4) 0
  have hbaseSource : alternatingWordBase ∈ H.source := by
    simpa [H] using
      (alternatingWordBase_mem_positiveLocalHomeomorph_source axis axis' hnonparallel)
  have hbaseTarget : alternatingWordMap axis axis' alternatingWordBase ∈ H.target :=
    H.map_source hbaseSource
  have hWscalar : 0 < specialScalar W := by
    rw [specialScalar_alternatingAxisWord]
    exact alternatingWordBase_mem_positiveSet axis axis'
  have hWvector : specialVector W =
      alternatingWordMap axis axis' alternatingWordBase := by
    exact specialVector_alternatingAxisWord axis axis' 0 (Real.pi / 4) 0
  have hWV : W ∈ V := ⟨hWscalar, by simpa [hWvector] using hbaseTarget⟩
  have hVK : V ⊆ K := by
    intro U hU
    obtain ⟨p, hp⟩ :=
      exists_alternatingAxisWord_of_mem_positiveLocalTarget axis axis' hnonparallel U hU.1 hU.2
    rw [← hp]
    exact alternatingAxisWord_mem K axis axis' haxis haxis' (p 0) (p 1) (p 2)
  apply Subgroup.isOpen_of_mem_nhds K
  exact Filter.mem_of_superset (hVopen.mem_nhds hWV) hVK

/-- The dot product of a real three-vector with itself is nonnegative. -/
theorem vector_dot_self_nonneg (v : Fin 3 → Real) : 0 ≤ v ⬝ᵥ v := by
  simpa using (dotProduct_star_self_nonneg v)

/-- A fixed unit Bloch axis used when a vector coordinate vanishes. -/
def standardBlochAxis : UnitBlochAxis :=
  ⟨0, 0, 1, by norm_num⟩

/-- Normalize a nonzero real Bloch vector to a unit axis. -/
noncomputable def normalizedBlochAxis (v : Fin 3 → Real) (hnonzero : v ⬝ᵥ v ≠ 0) :
    UnitBlochAxis := by
  let m : Real := Real.sqrt (v ⬝ᵥ v)
  have hnonneg : 0 ≤ v ⬝ᵥ v := vector_dot_self_nonneg v
  have hpos : 0 < m :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hnonzero))
  refine ⟨v 0 / m, v 1 / m, v 2 / m, ?_⟩
  rw [div_pow, div_pow, div_pow]
  have hsq : m ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hnonneg
  field_simp
  rw [hsq]
  simp only [Matrix.vec3_dotProduct]
  ring

/-- Rescaling the normalized nonzero vector recovers the original Bloch vector. -/
theorem sqrt_smul_blochVector_normalizedBlochAxis (v : Fin 3 → Real)
    (hnonzero : v ⬝ᵥ v ≠ 0) :
    Real.sqrt (v ⬝ᵥ v) • blochVector (normalizedBlochAxis v hnonzero) = v := by
  let m : Real := Real.sqrt (v ⬝ᵥ v)
  have hnonneg : 0 ≤ v ⬝ᵥ v := vector_dot_self_nonneg v
  have hpos : 0 < m :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hnonzero))
  ext i
  fin_cases i <;> simp [normalizedBlochAxis, blochVector]
  all_goals
    field_simp

/-- The real-parameter axis circle is continuous as a special-unitary-valued map. -/
theorem axisCircleRealSU_continuous (axis : UnitBlochAxis) :
    Continuous (axisCircleRealSU axis) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : Real => axisCircle axis (x : AddCircle (2 * Real.pi)))
  exact (axisCircle_continuous axis).comp (AddCircle.continuous_mk' _)

/-- Every determinant-one one-qubit gate has an explicit real axis-angle form. -/
theorem exists_axisCircleRealSU_eq (U : SingleQubitSpecialUnitary) :
    ∃ axis : UnitBlochAxis, ∃ theta : Real, axisCircleRealSU axis theta = U := by
  let r := specialScalar U
  let v := specialVector U
  have hnorm : r ^ 2 + v ⬝ᵥ v = 1 := by
    simpa [r, v] using special_coordinate_norm U
  have hnonneg : 0 ≤ v ⬝ᵥ v := vector_dot_self_nonneg v
  have hsqle : r ^ 2 ≤ 1 := by
    nlinarith
  have hrabs : |r| ≤ 1 := (sq_le_one_iff_abs_le_one r).mp hsqle
  have hrneg : -1 ≤ r := (abs_le.mp hrabs).1
  have hrpos : r ≤ 1 := (abs_le.mp hrabs).2
  let theta := Real.arccos r
  have hcos : Real.cos theta = r := by
    dsimp [theta]
    exact Real.cos_arccos hrneg hrpos
  have hsin : Real.sin theta = Real.sqrt (v ⬝ᵥ v) := by
    dsimp [theta]
    rw [Real.sin_arccos]
    congr 1
    nlinarith
  by_cases hvzero : v ⬝ᵥ v = 0
  · have hv : v = 0 := dotProduct_self_eq_zero.mp hvzero
    refine ⟨standardBlochAxis, theta, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (axisCircleRealSU standardBlochAxis theta : SingleQubitMatrix) =
      (U : SingleQubitMatrix)
    rw [axisCircleRealSU_matrix, special_coordinate_matrix U]
    change su2Matrix (Real.cos theta)
      (Real.sin theta • blochVector standardBlochAxis) = su2Matrix r v
    rw [hcos, hsin, hv]
    simp
  · let axis := normalizedBlochAxis v hvzero
    have hscale : Real.sqrt (v ⬝ᵥ v) • blochVector axis = v := by
      simpa [axis] using sqrt_smul_blochVector_normalizedBlochAxis v hvzero
    refine ⟨axis, theta, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (axisCircleRealSU axis theta : SingleQubitMatrix) =
      (U : SingleQubitMatrix)
    rw [axisCircleRealSU_matrix, special_coordinate_matrix U]
    change su2Matrix (Real.cos theta)
      (Real.sin theta • blochVector axis) = su2Matrix r v
    rw [hcos, hsin, hscale]

/-- The real-parameter axis circle starts at the special-unitary identity. -/
@[simp] theorem axisCircleRealSU_zero (axis : UnitBlochAxis) :
    axisCircleRealSU axis 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (axisCircle axis (0 : AddCircle (2 * Real.pi)) : SingleQubitMatrix) = 1
  simp

/-- The real axis circle supplies a concrete path from identity to each axis rotation. -/
noncomputable def axisCircleRealSUPath (axis : UnitBlochAxis) (theta : Real) :
    Path 1 (axisCircleRealSU axis theta) where
  toFun := fun s : unitInterval => axisCircleRealSU axis ((s : Real) * theta)
  continuous_toFun :=
    (axisCircleRealSU_continuous axis).comp (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by simp

/-- A concrete axis-angle path exists from identity to every determinant-one gate. -/
theorem nonempty_specialUnitaryPath (U : SingleQubitSpecialUnitary) :
    Nonempty (Path 1 U) := by
  rcases exists_axisCircleRealSU_eq U with ⟨axis, theta, haxis⟩
  exact ⟨haxis ▸ axisCircleRealSUPath axis theta⟩

/-- A chosen concrete axis-angle path from identity to each determinant-one gate. -/
noncomputable def specialUnitaryPath (U : SingleQubitSpecialUnitary) : Path 1 U :=
  Classical.choice (nonempty_specialUnitaryPath U)

/-- Two nonparallel complete axis circles generate every determinant-one special unitary. -/
theorem subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
    (K : Subgroup SingleQubitSpecialUnitary) (axis axis' : UnitBlochAxis)
    (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K)
    (U : SingleQubitSpecialUnitary) : U ∈ K := by
  have hopen : IsOpen (K : Set SingleQubitSpecialUnitary) :=
    subgroup_isOpen_of_contains_nonparallel_axisCircles K axis axis'
      hnonparallel haxis haxis'
  have hclopen : IsClopen (K : Set SingleQubitSpecialUnitary) :=
    ⟨Subgroup.isClosed_of_isOpen K hopen, hopen⟩
  let gamma := specialUnitaryPath U
  have hpreconnected : IsPreconnected (Set.range gamma) :=
    isPreconnected_range gamma.continuous
  have hrange : Set.range gamma ⊆ K :=
    hpreconnected.subset_isClopen hclopen
      ⟨1, ⟨0, gamma.source⟩, K.one_mem⟩
  exact hrange ⟨1, gamma.target⟩

/-- The closed-subgroup form needed by the next determinant-one generation layer. -/
theorem closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
    (K : Subgroup SingleQubitSpecialUnitary)
    (_hclosed : IsClosed (K : Set SingleQubitSpecialUnitary))
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K) :
    K = ⊤ := by
  apply top_unique
  intro U _
  exact subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
    K axis axis' hnonparallel haxis haxis' U
end Distillation
end QEC

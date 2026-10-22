import QEC.Distillation.Universality.SU2GeneratedDensity
import Mathlib.NumberTheory.Niven

/-!
# Clifford plus the `-pi/6` phase is projectively universal

The source boundary is [BK05, Section III, T-state route], pinned arXiv v2 TeX
`final.tex:599-627`.  Bravyi--Kitaev derive the injected phase state
`A_{-pi/6}` there and assert that `Lambda(exp(-i pi / 6))` together with
Clifford operations is universal.

The determinant-one word `T H S T H T`, its trace `3 / 2`, and the Niven
irrationality certificate below are project-derived formalization witnesses;
BK05 does not state that word or argument.  A Clifford conjugate supplies the
second nonparallel axis at the same angle.

The conclusion is finite-precision one-qubit universality modulo global phase,
not raw density in `U(2)`.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitMagic

open GeneratedUniversality

/-- The phase obtained from the ideal `T`-resource conversion in BK05. -/
def tResourcePhaseAngle : Real := -Real.pi / 6

/--
The concrete determinant-one word `T H S T H T`, where
`T = Lambda(exp(-i pi / 6))` and `S` is the Clifford phase gate.
-/
def tResourceAxisWord : SingleQubitGate :=
  phaseShiftGate tResourcePhaseAngle * hadamardGate * phaseGate *
    phaseShiftGate tResourcePhaseAngle * hadamardGate *
      phaseShiftGate tResourcePhaseAngle

/-- The rotation angle recovered from the real coordinate `3 / 4`. -/
def tResourceAxisAngle : Real := Real.arccos (3 / 4)

private theorem sqrt_two_ne_zero_complex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast sqrt_two_pos.ne'

private theorem sqrt_two_sq_complex : (Real.sqrt 2 : Complex) ^ 2 = 2 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2))

private theorem sqrt_three_sq_complex : (Real.sqrt 3 : Complex) ^ 2 = 3 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3))

private theorem sqrt_seven_pos : 0 < Real.sqrt 7 :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_seven_ne_zero : Real.sqrt 7 ≠ 0 :=
  sqrt_seven_pos.ne'

private theorem sqrt_seven_ne_zero_complex : (Real.sqrt 7 : Complex) ≠ 0 := by
  exact_mod_cast sqrt_seven_ne_zero

/-- The Bloch axis read off from the exact `T H S T H T` matrix. -/
def tResourceAxis : UnitBlochAxis where
  x := 2 / Real.sqrt 7
  y := 0
  z := -Real.sqrt 3 / Real.sqrt 7
  norm_sq := by
    have hseven : Real.sqrt 7 ^ 2 = 7 :=
      Real.sq_sqrt (by norm_num)
    have hthree : Real.sqrt 3 ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    field_simp [sqrt_seven_ne_zero]
    nlinarith

/-- The Clifford phase conjugate of `tResourceAxis`. -/
def tResourceConjugateAxis : UnitBlochAxis where
  x := 0
  y := 2 / Real.sqrt 7
  z := -Real.sqrt 3 / Real.sqrt 7
  norm_sq := by
    simpa [tResourceAxis] using tResourceAxis.norm_sq

/-- The selected angle has cosine `3 / 4`. -/
theorem tResourceAxisAngle_cos :
    Real.cos tResourceAxisAngle = 3 / 4 := by
  rw [tResourceAxisAngle, Real.cos_arccos (by norm_num) (by norm_num)]

/-- The selected angle has positive sine `sqrt 7 / 4`. -/
theorem tResourceAxisAngle_sin :
    Real.sin tResourceAxisAngle = Real.sqrt 7 / 4 := by
  rw [tResourceAxisAngle, Real.sin_arccos]
  norm_num [Real.sqrt_div (by norm_num : (0 : Real) ≤ 7) 16]

/-- Exact complex-circle coordinate of the selected angle. -/
theorem tResourceAxisAngle_toCircle :
    (AddCircle.toCircle
        (tResourceAxisAngle : AddCircle (2 * Real.pi)) : Complex) =
      (3 / 4 : Complex) + (Real.sqrt 7 / 4 : Complex) * Complex.I := by
  rw [AddCircle.toCircle_apply_mk]
  have hscale : (2 * Real.pi) / (2 * Real.pi) = (1 : Real) := by
    exact div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [hscale, one_mul, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    tResourceAxisAngle_cos, tResourceAxisAngle_sin]
  push_cast
  ring

/-- Exact matrix of the determinant-one irrational-angle word. -/
theorem tResourceAxisWord_matrix :
    (tResourceAxisWord : SingleQubitMatrix) =
      !![(3 / 4 : Complex) + (Real.sqrt 3 / 4 : Complex) * Complex.I,
          -(2 : Complex)⁻¹ * Complex.I;
         -(2 : Complex)⁻¹ * Complex.I,
          (3 / 4 : Complex) - (Real.sqrt 3 / 4 : Complex) * Complex.I] := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [tResourceAxisWord, tResourcePhaseAngle, phaseShiftGate,
      phaseShiftMatrix, hadamardGate, hadamardMatrix, phaseGate, phaseMatrix,
      phaseAmplitude_neg_pi_div_six]
    field_simp [sqrt_two_ne_zero_complex]
    ring_nf
    simp only [Complex.I_sq, hI3, Complex.I_pow_four]
    ring_nf
    try rw [sqrt_two_sq_complex]
    try rw [sqrt_three_sq_complex]
    try rw [show (Real.sqrt 3 : Complex) ^ 3 =
      (Real.sqrt 3 : Complex) * (Real.sqrt 3 : Complex) ^ 2 by ring,
      sqrt_three_sq_complex]
    ring

/-- The concrete word is literally the selected special-unitary axis-circle point. -/
theorem tResourceAxisWord_eq_axisCircle :
    tResourceAxisWord =
      axisCircle tResourceAxis
        (tResourceAxisAngle : AddCircle (2 * Real.pi)) := by
  apply Subtype.ext
  rw [tResourceAxisWord_matrix, axisCircle_matrix_entries,
    tResourceAxisAngle_toCircle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tResourceAxis] <;>
    field_simp [sqrt_seven_ne_zero_complex] <;>
    ring

/-- The explicit word has determinant one. -/
theorem tResourceAxisWord_det :
    (tResourceAxisWord : SingleQubitMatrix).det = 1 := by
  rw [tResourceAxisWord_matrix]
  simp [Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq, sqrt_three_sq_complex]
  ring

/-- The explicit word has the rational trace used in the Niven argument. -/
theorem tResourceAxisWord_trace :
    Matrix.trace (tResourceAxisWord : SingleQubitMatrix) = 3 / 2 := by
  rw [tResourceAxisWord_matrix, Matrix.trace_fin_two]
  simp
  ring

/-- The explicit word belongs to the subgroup generated by Clifford plus `-pi/6`. -/
theorem tResourceAxisWord_mem_generated :
    tResourceAxisWord ∈
      generatedUnitarySubgroup (cliffordPhaseGenerators tResourcePhaseAngle) := by
  repeat' apply cliffordPhaseGenerators_compose_mem
  · exact phaseShiftGate_mem_generated tResourcePhaseAngle
  · exact hadamardGate_mem_generated tResourcePhaseAngle
  · exact phaseGate_mem_generated tResourcePhaseAngle
  · exact phaseShiftGate_mem_generated tResourcePhaseAngle
  · exact hadamardGate_mem_generated tResourcePhaseAngle
  · exact phaseShiftGate_mem_generated tResourcePhaseAngle

/-- Clifford phase conjugation rotates the word's axis from the `x-z` plane to `y-z`. -/
theorem phaseGate_tResourceAxis_transport :
    (phaseGate : SingleQubitMatrix) * axisPauliMatrix tResourceAxis *
        (((phaseGate⁻¹ : SingleQubitGate) : SingleQubitMatrix)) =
      axisPauliMatrix tResourceConjugateAxis := by
  rw [phaseGate_inverse]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [axisPauliMatrix, tResourceAxis, tResourceConjugateAxis,
      phaseGate, phaseMatrix, phaseInverseGate, phaseInverseMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
    try ring_nf
  all_goals
    rw [Complex.I_sq]
    ring

/-- A Clifford conjugate of the determinant-one irrational-angle word. -/
def tResourceConjugateWord : SingleQubitGate :=
  phaseGate * tResourceAxisWord * phaseGate⁻¹

/-- The conjugate word remains in the generated Clifford-plus-phase subgroup. -/
theorem tResourceConjugateWord_mem_generated :
    tResourceConjugateWord ∈
      generatedUnitarySubgroup (cliffordPhaseGenerators tResourcePhaseAngle) := by
  exact cliffordPhaseGenerators_conjugate_mem tResourcePhaseAngle
    (phaseGate_mem_generated tResourcePhaseAngle)
    tResourceAxisWord_mem_generated

/-- The Clifford conjugate is literally an axis-circle point at the same angle. -/
theorem tResourceConjugateWord_eq_axisCircle :
    tResourceConjugateWord =
      axisCircle tResourceConjugateAxis
        (tResourceAxisAngle : AddCircle (2 * Real.pi)) := by
  rw [tResourceConjugateWord, tResourceAxisWord_eq_axisCircle]
  exact axisCircle_conjugate phaseGate tResourceAxis tResourceConjugateAxis
    phaseGate_tResourceAxis_transport _

/-- The two explicit Bloch axes are genuinely nonparallel. -/
theorem tResourceAxes_nonparallel :
    tResourceAxis.Nonparallel tResourceConjugateAxis := by
  simp [UnitBlochAxis.Nonparallel, blochCrossSq, tResourceAxis,
    tResourceConjugateAxis]
  positivity

/-- The circle angle of the word is an irrational fraction of a full turn. -/
theorem tResourceAxisAngle_irrational :
    Irrational (tResourceAxisAngle / (2 * Real.pi)) := by
  by_contra hrat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  have hangle_rat : ∃ r : Rat, tResourceAxisAngle = r * Real.pi := by
    refine ⟨2 * q, ?_⟩
    calc
      tResourceAxisAngle =
          (tResourceAxisAngle / (2 * Real.pi)) * (2 * Real.pi) := by
            field_simp
      _ = (q : Real) * (2 * Real.pi) := by rw [hq]
      _ = ((2 * q : Rat) : Real) * Real.pi := by push_cast; ring
  have hcos_value : Real.cos tResourceAxisAngle = 3 / 4 := by
    rw [tResourceAxisAngle, Real.cos_arccos (by norm_num) (by norm_num)]
  have hcos : ∃ q : Rat, Real.cos tResourceAxisAngle = q := by
    refine ⟨3 / 4, ?_⟩
    norm_num at hcos_value ⊢
    exact hcos_value
  have hniven := niven hangle_rat hcos
  rw [hcos_value] at hniven
  norm_num at hniven

/--
Clifford gates together with the BK05 `-pi/6` injected phase approximate every
one-qubit unitary to arbitrary precision modulo global phase.
-/
theorem cliffordTResourceFinitePrecisionOneQubitUniversal :
    FinitePrecisionOneQubitUniversal
      (cliffordPhaseGenerators tResourcePhaseAngle) := by
  exact finitePrecisionOneQubitUniversal_of_irrational_axis_words
    (generators := cliffordPhaseGenerators tResourcePhaseAngle)
    (axis := tResourceAxis)
    (axis' := tResourceConjugateAxis)
    (theta := tResourceAxisAngle)
    (word := tResourceAxisWord)
    (word' := tResourceConjugateWord)
    tResourceAxisWord_mem_generated
    tResourceAxisWord_eq_axisCircle
    tResourceConjugateWord_mem_generated
    tResourceConjugateWord_eq_axisCircle
    tResourceAxisAngle_irrational
    tResourceAxes_nonparallel

/-- The terminal theorem with the source angle displayed literally. -/
theorem cliffordNegativePiDivSixFinitePrecisionOneQubitUniversal :
    FinitePrecisionOneQubitUniversal
      (cliffordPhaseGenerators (-Real.pi / 6)) := by
  simpa [tResourcePhaseAngle] using
    cliffordTResourceFinitePrecisionOneQubitUniversal

end OneQubitMagic
end Distillation
end QEC

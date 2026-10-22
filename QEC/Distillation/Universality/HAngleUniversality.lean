import QEC.Distillation.Universality.SU2GeneratedDensity
import Mathlib.NumberTheory.Niven

/-!
# The concrete BK05 H-angle universality word

This module specializes the reusable irrational-axis criterion to the phase
`-pi / 4`.  It constructs an explicit determinant-one word from the concrete
Hadamard, Clifford phase, and phase-shift gates, identifies its literal Bloch
axis and angle, and obtains a second nonparallel axis by Clifford conjugation.

The pinned `[BK05, Section III, H-state route]` source (arXiv v2,
`final.tex:582-597`) supplies only the operational H-to-`A_{-pi/4}` claim and
the universality claim for that operation together with Clifford gates.  The
determinant-one word, its matrix and axis, the Niven argument, and the
Clifford-conjugate witness below are Lean-QEC project-derived.

Under the owner-approved physical convention, the conclusion is
finite-precision one-qubit universality modulo global phase, not literal
density in raw `U(2)`.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace OneQubitMagic

open GeneratedUniversality

private theorem sqrt_two_ne_zero_complex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast sqrt_two_pos.ne'

private theorem sqrt_two_mul_self_complex :
    (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
  exact_mod_cast sqrt_two_mul_self

@[simp] private theorem complex_I_pow_two : Complex.I ^ 2 = -1 :=
  Complex.I_sq

@[simp] private theorem complex_I_pow_three : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, complex_I_pow_two]
  ring

@[simp] private theorem complex_I_pow_four : Complex.I ^ 4 = 1 := by
  rw [pow_succ, complex_I_pow_three]
  ring_nf
  rw [Complex.I_sq]
  norm_num

@[simp] private theorem complex_I_pow_five : Complex.I ^ 5 = Complex.I := by
  rw [pow_succ, complex_I_pow_four, one_mul]

@[simp] private theorem complex_I_pow_six : Complex.I ^ 6 = -1 := by
  rw [pow_succ, complex_I_pow_five, Complex.I_mul_I]

@[simp] private theorem complex_I_pow_seven : Complex.I ^ 7 = -Complex.I := by
  rw [pow_succ, complex_I_pow_six]
  ring

@[simp] private theorem complex_I_pow_eight : Complex.I ^ 8 = 1 := by
  rw [pow_succ, complex_I_pow_seven]
  ring_nf
  rw [Complex.I_sq]
  norm_num

@[simp] private theorem sqrt_two_pow_two_complex :
    (Real.sqrt 2 : Complex) ^ 2 = 2 := by
  simpa [pow_two] using sqrt_two_mul_self_complex

@[simp] private theorem sqrt_two_pow_three_complex :
    (Real.sqrt 2 : Complex) ^ 3 = 2 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_pow_two_complex]

@[simp] private theorem sqrt_two_pow_four_complex :
    (Real.sqrt 2 : Complex) ^ 4 = 4 := by
  rw [pow_succ, sqrt_two_pow_three_complex]
  calc
    2 * (Real.sqrt 2 : Complex) * Real.sqrt 2 =
        2 * ((Real.sqrt 2 : Complex) * Real.sqrt 2) := by ring
    _ = 4 := by rw [sqrt_two_mul_self_complex]; norm_num

@[simp] private theorem sqrt_two_pow_five_complex :
    (Real.sqrt 2 : Complex) ^ 5 = 4 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_pow_four_complex]

@[simp] private theorem sqrt_two_pow_six_complex :
    (Real.sqrt 2 : Complex) ^ 6 = 8 := by
  rw [pow_succ, sqrt_two_pow_five_complex]
  calc
    4 * (Real.sqrt 2 : Complex) * Real.sqrt 2 =
        4 * ((Real.sqrt 2 : Complex) * Real.sqrt 2) := by ring
    _ = 8 := by rw [sqrt_two_mul_self_complex]; norm_num

@[simp] private theorem sqrt_two_pow_seven_complex :
    (Real.sqrt 2 : Complex) ^ 7 = 8 * Real.sqrt 2 := by
  rw [pow_succ, sqrt_two_pow_six_complex]

@[simp] private theorem sqrt_two_pow_eight_complex :
    (Real.sqrt 2 : Complex) ^ 8 = 16 := by
  rw [pow_succ, sqrt_two_pow_seven_complex]
  calc
    8 * (Real.sqrt 2 : Complex) * Real.sqrt 2 =
        8 * ((Real.sqrt 2 : Complex) * Real.sqrt 2) := by ring
    _ = 16 := by rw [sqrt_two_mul_self_complex]; norm_num

private theorem sqrt_seven_pos : 0 < Real.sqrt 7 :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_seven_sq : Real.sqrt 7 ^ 2 = 7 :=
  Real.sq_sqrt (by norm_num)

/-- The concrete irrational rotation angle used by the H route. -/
noncomputable def hAngle : Real :=
  Real.arccos (3 / 4)

/-- The Bloch axis of the explicit determinant-one H-route word. -/
noncomputable def hAngleAxis : UnitBlochAxis where
  x := -(Real.sqrt 2 + 1) / Real.sqrt 7
  y := 1 / Real.sqrt 7
  z := (1 - Real.sqrt 2) / Real.sqrt 7
  norm_sq := by
    field_simp [sqrt_seven_pos.ne']
    nlinarith [sqrt_two_mul_self, sqrt_seven_sq]

/-- The image of `hAngleAxis` under the concrete Clifford phase gate. -/
noncomputable def hAngleConjugateAxis : UnitBlochAxis where
  x := -hAngleAxis.y
  y := hAngleAxis.x
  z := hAngleAxis.z
  norm_sq := by
    nlinarith [hAngleAxis.norm_sq]

/--
The determinant-one H-route word
`((H K)^3) (H P)^4 K`, where `P` is the `-pi/4` phase shift.
-/
noncomputable def hAngleWord : SingleQubitGate :=
  ((hadamardGate * phaseGate) ^ 3) *
    ((hadamardGate * phaseShiftGate (-Real.pi / 4)) ^ 4) * phaseGate

/-- Exact concrete matrix of the H-route word. -/
theorem hAngleWord_matrix :
    (hAngleWord : SingleQubitMatrix) =
      !![(3 : Complex) / 4 + Complex.I * ((Real.sqrt 2 - 1 : Real) / 4),
         -(1 : Complex) / 4 + Complex.I * ((1 + Real.sqrt 2 : Real) / 4);
         (1 : Complex) / 4 + Complex.I * ((1 + Real.sqrt 2 : Real) / 4),
         (3 : Complex) / 4 + Complex.I * ((1 - Real.sqrt 2 : Real) / 4)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hAngleWord, hadamardGate, phaseGate, phaseShiftGate,
      hadamardMatrix, phaseMatrix, phaseShiftMatrix,
      phaseAmplitude_neg_pi_div_four, pow_succ]
  all_goals
    field_simp [sqrt_two_ne_zero_complex]
    ring_nf
    simp only [complex_I_pow_two, complex_I_pow_three, complex_I_pow_four,
      complex_I_pow_five, complex_I_pow_six, complex_I_pow_seven,
      complex_I_pow_eight, sqrt_two_pow_two_complex, sqrt_two_pow_three_complex,
      sqrt_two_pow_six_complex, sqrt_two_pow_seven_complex, sqrt_two_pow_eight_complex]
    ring

/-- The explicit H-route word has determinant one. -/
theorem hAngleWord_det :
    (hAngleWord : SingleQubitMatrix).det = 1 := by
  rw [hAngleWord_matrix]
  simp [Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq, sqrt_two_pow_two_complex]
  ring

/-- The word trace is the concrete rational value `3/2`. -/
theorem hAngleWord_trace :
    Matrix.trace (hAngleWord : SingleQubitMatrix) = 3 / 2 := by
  rw [hAngleWord_matrix]
  simp [Matrix.trace_fin_two]
  ring

/-- The explicit word belongs to the subgroup generated by `H`, `K`, and `P`. -/
theorem hAngleWord_mem_generated :
    hAngleWord ∈ generatedUnitarySubgroup
      (cliffordPhaseGenerators (-Real.pi / 4)) := by
  let G := generatedUnitarySubgroup (cliffordPhaseGenerators (-Real.pi / 4))
  have hH : hadamardGate ∈ G := hadamardGate_mem_generated _
  have hK : phaseGate ∈ G := phaseGate_mem_generated _
  have hP : phaseShiftGate (-Real.pi / 4) ∈ G := phaseShiftGate_mem_generated _
  exact G.mul_mem
    (G.mul_mem (G.pow_mem (G.mul_mem hH hK) 3)
      (G.pow_mem (G.mul_mem hH hP) 4)) hK

@[simp] theorem hAngle_cos : Real.cos hAngle = 3 / 4 := by
  rw [hAngle, Real.cos_arccos (by norm_num) (by norm_num)]

theorem hAngle_sin : Real.sin hAngle = Real.sqrt 7 / 4 := by
  rw [hAngle, Real.sin_arccos]
  have hroot : Real.sqrt (1 - ((3 : Real) / 4) ^ 2) = Real.sqrt 7 / 4 := by
    rw [show 1 - ((3 : Real) / 4) ^ 2 = 7 / 16 by norm_num]
    rw [Real.sqrt_div (by norm_num : 0 ≤ (7 : Real))]
    norm_num
  exact hroot

/-- Literal determinant-one axis-circle equality consumed by the #730 criterion. -/
theorem hAngleWord_eq_axisCircle :
    hAngleWord = axisCircle hAngleAxis
      (hAngle : AddCircle (2 * Real.pi)) := by
  apply Subtype.ext
  rw [hAngleWord_matrix, axisCircle_matrix_entries, addCircle_toCircle_two_pi]
  rw [hAngle_cos, hAngle_sin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hAngleAxis]
  all_goals field_simp [sqrt_seven_pos.ne'] <;> ring

/-- The phase Clifford transports the concrete H-route Pauli axis as stated. -/
theorem phaseGate_conjugates_hAngleAxis :
    (phaseGate : SingleQubitMatrix) * axisPauliMatrix hAngleAxis *
        ((phaseGate⁻¹ : SingleQubitGate) : SingleQubitMatrix) =
      axisPauliMatrix hAngleConjugateAxis := by
  rw [phaseGate_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, phaseInverseGate, phaseMatrix, phaseInverseMatrix,
      axisPauliMatrix, hAngleAxis, hAngleConjugateAxis,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The second generated word is the concrete Clifford conjugate. -/
noncomputable def hAngleConjugateWord : SingleQubitGate :=
  phaseGate * hAngleWord * phaseGate⁻¹

theorem hAngleConjugateWord_mem_generated :
    hAngleConjugateWord ∈ generatedUnitarySubgroup
      (cliffordPhaseGenerators (-Real.pi / 4)) := by
  exact cliffordPhaseGenerators_conjugate_mem _
    (phaseGate_mem_generated _) hAngleWord_mem_generated

/-- The Clifford conjugate is literally the same angle about the transported axis. -/
theorem hAngleConjugateWord_eq_axisCircle :
    hAngleConjugateWord = axisCircle hAngleConjugateAxis
      (hAngle : AddCircle (2 * Real.pi)) := by
  rw [hAngleConjugateWord, hAngleWord_eq_axisCircle]
  exact axisCircle_conjugate phaseGate hAngleAxis hAngleConjugateAxis
    phaseGate_conjugates_hAngleAxis _

/-- The two explicit H-route axes are neither parallel nor antiparallel. -/
theorem hAngleAxis_nonparallel :
    hAngleAxis.Nonparallel hAngleConjugateAxis := by
  rw [UnitBlochAxis.Nonparallel]
  simp [blochCrossSq, hAngleAxis, hAngleConjugateAxis]
  field_simp [sqrt_seven_pos.ne']
  nlinarith [sqrt_two_pos, sqrt_two_mul_self, sqrt_seven_sq]

/-- The concrete cosine `3/4` forces the axis angle to be irrational modulo `2*pi`. -/
theorem hAngle_div_two_pi_irrational :
    Irrational (hAngle / (2 * Real.pi)) := by
  by_contra hrat
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  have htheta : hAngle = ((2 * q : Rat) : Real) * Real.pi := by
    calc
      hAngle = (hAngle / (2 * Real.pi)) * (2 * Real.pi) := by
        field_simp [Real.pi_ne_zero]
      _ = (q : Real) * (2 * Real.pi) := by rw [hq]
      _ = ((2 * q : Rat) : Real) * Real.pi := by
        push_cast
        ring
  have hvalues := niven (θ := hAngle) ⟨2 * q, htheta⟩
    ⟨(3 / 4 : Rat), by simp [hAngle_cos]⟩
  rw [hAngle_cos] at hvalues
  norm_num at hvalues

/--
The theorem-level realization of the operational H-to-`A_{-pi/4}`/Clifford
universality claim pinned at `[BK05, Section III, H-state route]`, arXiv v2
`final.tex:582-597`.  The source supplies only that operational claim; the
determinant-one word, matrix and axis, Niven argument, and Clifford-conjugate
witness are Lean-QEC project-derived.  Under the owner-approved physical
convention, this conclusion is modulo global phase; it is not literal density
in raw `U(2)`.
-/
theorem finitePrecisionOneQubitUniversal_cliffordPhase_neg_pi_div_four :
    FinitePrecisionOneQubitUniversal
      (cliffordPhaseGenerators (-Real.pi / 4)) :=
  finitePrecisionOneQubitUniversal_of_irrational_axis_words
    (cliffordPhaseGenerators (-Real.pi / 4))
    hAngleAxis hAngleConjugateAxis hAngle hAngleWord hAngleConjugateWord
    hAngleWord_mem_generated hAngleWord_eq_axisCircle
    hAngleConjugateWord_mem_generated hAngleConjugateWord_eq_axisCircle
    hAngle_div_two_pi_irrational hAngleAxis_nonparallel

end OneQubitMagic
end Distillation
end QEC

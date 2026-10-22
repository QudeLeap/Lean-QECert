import QEC.Distillation.Universality.OneQubitMagic
import QEC.Distillation.Universality.GeneratedUniversality
noncomputable section

namespace QEC.Distillation.OneQubitMagic

open Semantics Semantics.Qubit
open GeneratedUniversality

private theorem sqrt_two_mul_self_complex :
    (Real.sqrt 2 : Complex) * (Real.sqrt 2 : Complex) = 2 := by
  exact_mod_cast sqrt_two_mul_self

private theorem sqrt_two_ne_zero_complex : (Real.sqrt 2 : Complex) ≠ 0 := by
  exact_mod_cast ne_of_gt sqrt_two_pos

private theorem hadamardMatrix_unitary :
    hadamardMatrix ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.conj_ofReal] <;>
    field_simp [sqrt_two_ne_zero_complex] <;>
    rw [pow_two, sqrt_two_mul_self_complex] <;> ring

private theorem phaseMatrix_unitary :
    phaseMatrix ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

private theorem phaseInverseMatrix_unitary :
    phaseInverseMatrix ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseInverseMatrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

private theorem phaseShiftMatrix_unitary (theta : Real) :
    phaseShiftMatrix theta ∈ Matrix.unitaryGroup (Fin 2) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseShiftMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  change phaseAmplitude theta * star (phaseAmplitude theta) = 1
  exact phaseAmplitude_mul_conj theta

/-- The concrete Hadamard matrix packaged as a generated-universality gate. -/
noncomputable def hadamardGate : UnitaryGate (Fin 2) :=
  ⟨hadamardMatrix, hadamardMatrix_unitary⟩

/-- The concrete Clifford phase matrix packaged as a generated-universality gate. -/
noncomputable def phaseGate : UnitaryGate (Fin 2) :=
  ⟨phaseMatrix, phaseMatrix_unitary⟩

/-- The inverse Clifford phase matrix packaged as a generated-universality gate. -/
noncomputable def phaseInverseGate : UnitaryGate (Fin 2) :=
  ⟨phaseInverseMatrix, phaseInverseMatrix_unitary⟩

/-- The concrete diagonal phase matrix packaged as a generated-universality gate. -/
noncomputable def phaseShiftGate (theta : Real) : UnitaryGate (Fin 2) :=
  ⟨phaseShiftMatrix theta, phaseShiftMatrix_unitary theta⟩

@[simp] theorem hadamardGate_matrix :
    (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) = hadamardMatrix :=
  rfl

@[simp] theorem phaseGate_matrix :
    (phaseGate : Matrix (Fin 2) (Fin 2) Complex) = phaseMatrix :=
  rfl

@[simp] theorem phaseInverseGate_matrix :
    (phaseInverseGate : Matrix (Fin 2) (Fin 2) Complex) = phaseInverseMatrix :=
  rfl

@[simp] theorem phaseShiftGate_matrix (theta : Real) :
    (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) = phaseShiftMatrix theta :=
  rfl

/-- The gate action is exactly the existing Hadamard transport action. -/
theorem hadamardGate_apply (psi : QubitSpace) :
    Matrix.toEuclideanLin (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      hadamardTransport psi :=
  rfl

/-- The gate action is exactly the existing Clifford phase transport action. -/
theorem phaseGate_apply (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseTransport psi :=
  rfl

/-- The inverse gate action is exactly the existing inverse phase operator action. -/
theorem phaseInverseGate_apply (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseInverseGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseInverseOperator psi :=
  rfl

/-- The gate action is exactly the existing diagonal phase transport action. -/
theorem phaseShiftGate_apply (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseShiftTransport theta psi :=
  rfl

@[simp] theorem hadamardGate_apply_zero (psi : QubitSpace) :
    Matrix.toEuclideanLin (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) psi 0 =
      (Real.sqrt 2 : Complex)⁻¹ * (psi 0 + psi 1) := by
  rw [hadamardGate_apply]
  exact hadamardOperator_apply_zero psi

@[simp] theorem hadamardGate_apply_one (psi : QubitSpace) :
    Matrix.toEuclideanLin (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1) := by
  rw [hadamardGate_apply]
  exact hadamardOperator_apply_one psi

@[simp] theorem phaseGate_apply_zero (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi 0 = psi 0 := by
  rw [phaseGate_apply]
  exact phaseOperator_apply_zero psi

@[simp] theorem phaseGate_apply_one (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      Complex.I * psi 1 := by
  rw [phaseGate_apply]
  exact phaseOperator_apply_one psi

@[simp] theorem phaseShiftGate_apply_zero (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi 0 =
      psi 0 := by
  rw [phaseShiftGate_apply]
  exact phaseShiftOperator_apply_zero theta psi

@[simp] theorem phaseShiftGate_apply_one (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      phaseAmplitude theta * psi 1 := by
  rw [phaseShiftGate_apply]
  exact phaseShiftOperator_apply_one theta psi

theorem hadamardGate_mul_self : hadamardGate * hadamardGate = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamardGate, hadamardMatrix]
    <;> field_simp [sqrt_two_ne_zero_complex]
    <;> rw [pow_two, sqrt_two_mul_self_complex] <;> ring

theorem hadamardGate_inverse : hadamardGate⁻¹ = hadamardGate :=
  (inv_eq_iff_mul_eq_one).2 hadamardGate_mul_self

theorem phaseGate_mul_phaseInverseGate : phaseGate * phaseInverseGate = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, phaseInverseGate, phaseMatrix, phaseInverseMatrix, Complex.I_mul_I]

theorem phaseInverseGate_mul_phaseGate : phaseInverseGate * phaseGate = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, phaseInverseGate, phaseMatrix, phaseInverseMatrix, Complex.I_mul_I]

theorem phaseGate_inverse : phaseGate⁻¹ = phaseInverseGate :=
  (inv_eq_iff_mul_eq_one).2 phaseGate_mul_phaseInverseGate

theorem phaseShiftGate_mul (theta phi : Real) :
    phaseShiftGate theta * phaseShiftGate phi = phaseShiftGate (theta + phi) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseShiftGate, phaseShiftMatrix, phaseAmplitude_add]

@[simp] theorem phaseShiftGate_zero : phaseShiftGate 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseShiftGate, phaseShiftMatrix]

theorem phaseShiftGate_mul_neg (theta : Real) :
    phaseShiftGate theta * phaseShiftGate (-theta) = 1 := by
  rw [phaseShiftGate_mul]
  simp

theorem phaseShiftGate_inverse (theta : Real) :
    (phaseShiftGate theta)⁻¹ = phaseShiftGate (-theta) :=
  (inv_eq_iff_mul_eq_one).2 (phaseShiftGate_mul_neg theta)

/-- The shared concrete Clifford-plus-phase generator set. -/
noncomputable def cliffordPhaseGenerators (theta : Real) : Set (UnitaryGate (Fin 2)) :=
  {hadamardGate, phaseGate, phaseShiftGate theta}

@[simp] theorem hadamardGate_mem_cliffordPhaseGenerators (theta : Real) :
    hadamardGate ∈ cliffordPhaseGenerators theta := by
  simp [cliffordPhaseGenerators]

@[simp] theorem phaseGate_mem_cliffordPhaseGenerators (theta : Real) :
    phaseGate ∈ cliffordPhaseGenerators theta := by
  simp [cliffordPhaseGenerators]

@[simp] theorem phaseShiftGate_mem_cliffordPhaseGenerators (theta : Real) :
    phaseShiftGate theta ∈ cliffordPhaseGenerators theta := by
  simp [cliffordPhaseGenerators]

theorem hadamardGate_mem_generated (theta : Real) :
    hadamardGate ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  Subgroup.subset_closure (hadamardGate_mem_cliffordPhaseGenerators theta)

theorem phaseGate_mem_generated (theta : Real) :
    phaseGate ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  Subgroup.subset_closure (phaseGate_mem_cliffordPhaseGenerators theta)

theorem phaseShiftGate_mem_generated (theta : Real) :
    phaseShiftGate theta ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  Subgroup.subset_closure (phaseShiftGate_mem_cliffordPhaseGenerators theta)

/-- Generated concrete gates are closed under composition. -/
theorem cliffordPhaseGenerators_compose_mem (theta : Real)
    {U V : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta))
    (hV : V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U * V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  generatedUnitarySubgroup_compose_mem (cliffordPhaseGenerators theta) hU hV

/-- Generated concrete gates are closed under inversion. -/
theorem cliffordPhaseGenerators_inverse_mem (theta : Real)
    {U : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U⁻¹ ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  (generatedUnitarySubgroup (cliffordPhaseGenerators theta)).inv_mem hU

/-- Generated concrete gates are closed under generated conjugation. -/
theorem cliffordPhaseGenerators_conjugate_mem (theta : Real)
    {U V : UnitaryGate (Fin 2)}
    (hU : U ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta))
    (hV : V ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta)) :
    U * V * U⁻¹ ∈ generatedUnitarySubgroup (cliffordPhaseGenerators theta) :=
  generatedUnitarySubgroup_conjugate_mem (cliffordPhaseGenerators theta) hU hV

end QEC.Distillation.OneQubitMagic

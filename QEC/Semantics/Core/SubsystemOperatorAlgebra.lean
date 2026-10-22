import QEC.Semantics.Core.Subsystem

/-! # Algebra of concrete subsystem identity extensions -/

namespace QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem extend_zero (S : FiniteSubsystem ι) : S.extendLocal 0 = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp [extendLocal]

private theorem extend_add (S : FiniteSubsystem ι) (A B : Operator S.selectedSystem) :
    S.extendLocal (A+B) = S.extendLocal A + S.extendLocal B := by
  apply TensorProduct.ext'
  intro x y
  simp [extendLocal, TensorProduct.add_tmul]

private theorem extend_smul (S : FiniteSubsystem ι) (c : ℂ) (A : Operator S.selectedSystem) :
    S.extendLocal (c • A) = c • S.extendLocal A := by
  apply TensorProduct.ext'
  intro x y
  simp [extendLocal, TensorProduct.smul_tmul']

private theorem extend_mul (S : FiniteSubsystem ι) (A B : Operator S.selectedSystem) :
    S.extendLocal (A*B) = S.extendLocal A * S.extendLocal B := by
  apply TensorProduct.ext'
  intro x y
  simp [extendLocal, Module.End.mul_apply]

@[simp] theorem extendLocalToRegister_zero (S : FiniteSubsystem ι) :
    S.extendLocalToRegister 0 = 0 := by
  rw [extendLocalToRegister, extend_zero]
  ext x
  simp [UnitaryTransport.conjOperator]

theorem extendLocalToRegister_add (S : FiniteSubsystem ι) (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A+B) = S.extendLocalToRegister A + S.extendLocalToRegister B := by
  rw [extendLocalToRegister, extend_add]
  ext x
  simp [extendLocalToRegister, UnitaryTransport.conjOperator]

theorem extendLocalToRegister_smul_scalar (S : FiniteSubsystem ι) (c : ℂ)
    (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (c • A) = c • S.extendLocalToRegister A := by
  rw [extendLocalToRegister, extend_smul]
  ext x
  simp [extendLocalToRegister, UnitaryTransport.conjOperator]

theorem extendLocalToRegister_mul (S : FiniteSubsystem ι) (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A*B) = S.extendLocalToRegister A * S.extendLocalToRegister B := by
  simp only [extendLocalToRegister, extend_mul, UnitaryTransport.conjOperator_mul]

@[simp] theorem extendLocalToRegister_one (S : FiniteSubsystem ι) :
    S.extendLocalToRegister 1 = 1 := by
  have h : S.extendLocal 1 = 1 := by
    apply TensorProduct.ext'
    intro x y
    simp [extendLocal]
  rw [extendLocalToRegister, h, UnitaryTransport.conjOperator_one]

theorem supported_zero (S : FiniteSubsystem ι) : S.OperatorSupportedOnRegister 0 :=
  ⟨0, S.extendLocalToRegister_zero⟩
theorem supported_one (S : FiniteSubsystem ι) : S.OperatorSupportedOnRegister 1 :=
  ⟨1, S.extendLocalToRegister_one⟩
theorem supported_add (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A+B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a+b, S.extendLocalToRegister_add a b⟩
theorem supported_smul (S : FiniteSubsystem ι) (c : ℂ)
    {A : Operator (Qubit.QubitRegister ι)} (hA : S.OperatorSupportedOnRegister A) :
    S.OperatorSupportedOnRegister (c • A) := by
  obtain ⟨a,rfl⟩ := hA
  exact ⟨c • a, S.extendLocalToRegister_smul_scalar c a⟩
theorem supported_sub (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A-B) := by
  simpa [sub_eq_add_neg] using S.supported_add hA (S.supported_smul (-1) hB)
theorem supported_mul (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A*B) := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  exact ⟨a*b, S.extendLocalToRegister_mul a b⟩
theorem supported_sum (S : FiniteSubsystem ι) {κ : Type*} (s : Finset κ)
    (A : κ → Operator (Qubit.QubitRegister ι))
    (h : ∀ k ∈ s, S.OperatorSupportedOnRegister (A k)) :
    S.OperatorSupportedOnRegister (∑ k ∈ s, A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.supported_zero
  | @insert k s hk ih =>
    simpa [Finset.sum_insert hk] using S.supported_add (h k (by simp))
      (ih (fun j hj => h j (by simp [hj])))

end
end QEC.Semantics.FiniteSubsystem

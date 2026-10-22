import QEC.Semantics.ErrorCorrection.QuditSubsystem

/-!
# Matrix elements of actual tensor-local operators

The concrete selected/complement factorization gives the local matrix
formula, vanishing off complementary labels, and selected-only diagonals.
-/

noncomputable section

namespace QEC.Semantics.QuditSubsystem

open scoped BigOperators TensorProduct

universe u

variable {J : Type u} [Fintype J] [DecidableEq J] {q : J → Nat}

theorem extendLocal_basis_inner (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) =
    inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1)
        (E (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1)) *
      inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2)
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2) := by
  rw [← inner_conj_symm, extendLocalToRegister, UnitaryTransport.inner_conjOperator]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_symm]
  rw [S.registerFactorization_apply_basis, S.registerFactorization_apply_basis,
    S.extendLocal_apply_tmul, TensorProduct.inner_tmul]
  simp only [map_mul, inner_conj_symm]

theorem extendLocal_basis_inner_zero (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) (h : ∃ j, j ∉ S.selected ∧ x j ≠ y j) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) = 0 := by
  classical
  obtain ⟨j, hj, hxy⟩ := h
  have hcomp : (S.splitLabel x).2 ≠ (S.splitLabel y).2 := by
    intro heq
    exact hxy (congrFun heq ⟨j, hj⟩)
  rw [extendLocal_basis_inner]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, hcomp]

theorem extendLocal_basis_diagonal_eq (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) (h : ∀ j, j ∈ S.selected → x j = y j) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex x)) =
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex y)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) := by
  classical
  have hsel : (S.splitLabel x).1 = (S.splitLabel y).1 := by
    funext j
    exact h j j.property
  rw [extendLocal_basis_inner, extendLocal_basis_inner, hsel]
  simp

end QEC.Semantics.QuditSubsystem

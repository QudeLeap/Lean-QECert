import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Derivation.Basic

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Entrywise derivations of finite matrices

This module packages the entrywise action of a derivation on a matrix and
proves its product and inverse rules.  These symbolic identities are the
bounded algebraic certificate used to transport logarithmic trace formulas
through Smith-normal-form changes of basis.

There is no residue, ramification, duality, genus, or Riemann--Roch statement
in this module.
-/

namespace QEC.Coding.AlgebraicGeometry

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Apply a derivation to every entry of a matrix. -/
def entrywiseMatrixDerivation {m n : Type*} (D : Derivation k K K)
    (A : Matrix m n K) : Matrix m n K :=
  Matrix.of fun i j => D (A i j)

@[simp]
theorem entrywiseMatrixDerivation_apply {m n : Type*}
    (D : Derivation k K K) (A : Matrix m n K) (i : m) (j : n) :
    entrywiseMatrixDerivation D A i j = D (A i j) :=
  rfl

@[simp]
theorem entrywiseMatrixDerivation_add {m n : Type*}
    (D : Derivation k K K) (A B : Matrix m n K) :
    entrywiseMatrixDerivation D (A + B) =
      entrywiseMatrixDerivation D A + entrywiseMatrixDerivation D B := by
  ext i j
  simp only [entrywiseMatrixDerivation_apply, Matrix.add_apply, map_add]

/-- Entrywise differentiation obeys the matrix Leibniz rule. -/
theorem entrywiseMatrixDerivation_mul {m n p : Type*} [Fintype n]
    (D : Derivation k K K) (A : Matrix m n K) (B : Matrix n p K) :
    entrywiseMatrixDerivation D (A * B) =
      entrywiseMatrixDerivation D A * B +
        A * entrywiseMatrixDerivation D B := by
  ext i j
  simp only [entrywiseMatrixDerivation_apply, Matrix.mul_apply, map_sum,
    D.leibniz, smul_eq_mul, Matrix.add_apply]
  rw [Finset.sum_add_distrib]
  have hcomm :
      (∑ x, B x j * D (A i x)) = ∑ x, D (A i x) * B x j := by
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_comm]
  rw [hcomm, add_comm]

@[simp]
theorem entrywiseMatrixDerivation_one {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k K K) :
    entrywiseMatrixDerivation D (1 : Matrix n n K) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [entrywiseMatrixDerivation_apply, Matrix.one_apply_eq,
      D.map_one_eq_zero, Matrix.zero_apply]
  · simp only [entrywiseMatrixDerivation_apply, Matrix.one_apply, hij,
      if_false, map_zero, Matrix.zero_apply]

/-- If two square matrices are mutual inverses, differentiating either
inverse relation gives the usual inverse rule entrywise. -/
theorem entrywiseMatrixDerivation_inverse {n : Type*} [Fintype n]
    [DecidableEq n] (D : Derivation k K K) (A U : Matrix n n K)
    (hAU : A * U = 1) (hUA : U * A = 1) :
    entrywiseMatrixDerivation D U =
      -(U * entrywiseMatrixDerivation D A * U) := by
  have hzero :
      entrywiseMatrixDerivation D A * U +
          A * entrywiseMatrixDerivation D U = 0 := by
    calc
      _ = entrywiseMatrixDerivation D (A * U) :=
        (entrywiseMatrixDerivation_mul D A U).symm
      _ = entrywiseMatrixDerivation D 1 := by rw [hAU]
      _ = 0 := entrywiseMatrixDerivation_one D
  have hright :
      A * entrywiseMatrixDerivation D U =
        -(entrywiseMatrixDerivation D A * U) :=
    eq_neg_of_add_eq_zero_right hzero
  calc
    entrywiseMatrixDerivation D U = 1 * entrywiseMatrixDerivation D U :=
      (one_mul _).symm
    _ = (U * A) * entrywiseMatrixDerivation D U := by rw [hUA]
    _ = U * (A * entrywiseMatrixDerivation D U) := by rw [Matrix.mul_assoc]
    _ = U * (-(entrywiseMatrixDerivation D A * U)) := by rw [hright]
    _ = -(U * entrywiseMatrixDerivation D A * U) := by
      rw [mul_neg, Matrix.mul_assoc]

/-- The trace of the logarithmic derivative of a three-factor matrix product
splits into the three factor contributions.  Only the inverse-side identities
actually used by the cyclic trace calculation are assumed. -/
theorem entrywiseMatrixDerivation_trace_logarithmic_mul_three
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k K K)
    (P Pinv A Ainv Q Qinv : Matrix n n K)
    (hPinvP : Pinv * P = 1)
    (hAinvA : Ainv * A = 1) (hAAinv : A * Ainv = 1)
    (hQQinv : Q * Qinv = 1) :
    Matrix.trace
        (Qinv * Ainv * Pinv *
          entrywiseMatrixDerivation D (P * A * Q)) =
      Matrix.trace (Pinv * entrywiseMatrixDerivation D P) +
        Matrix.trace (Ainv * entrywiseMatrixDerivation D A) +
          Matrix.trace (Qinv * entrywiseMatrixDerivation D Q) := by
  let DP := entrywiseMatrixDerivation D P
  let DA := entrywiseMatrixDerivation D A
  let DQ := entrywiseMatrixDerivation D Q
  have htermP :
      Matrix.trace (Qinv * Ainv * Pinv * (DP * A * Q)) =
        Matrix.trace (Pinv * DP) := by
    calc
      Matrix.trace (Qinv * Ainv * Pinv * (DP * A * Q)) =
          Matrix.trace ((Qinv * Ainv * Pinv * DP * A) * Q) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * (Qinv * Ainv * Pinv * DP * A)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Ainv * Pinv * DP) * A) := by
        congr 1
        calc
          Q * (Qinv * Ainv * Pinv * DP * A) =
              (Q * Qinv) * (Ainv * Pinv * DP * A) := by
                simp only [Matrix.mul_assoc]
          _ = Ainv * Pinv * DP * A := by rw [hQQinv, one_mul]
      _ = Matrix.trace (A * (Ainv * Pinv * DP)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Pinv * DP) := by
        congr 1
        calc
          A * (Ainv * Pinv * DP) =
              (A * Ainv) * (Pinv * DP) := by
                simp only [Matrix.mul_assoc]
          _ = Pinv * DP := by rw [hAAinv, one_mul]
  have htermA :
      Matrix.trace (Qinv * Ainv * Pinv * (P * DA * Q)) =
        Matrix.trace (Ainv * DA) := by
    calc
      Matrix.trace (Qinv * Ainv * Pinv * (P * DA * Q)) =
          Matrix.trace ((Qinv * Ainv * Pinv * P * DA) * Q) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * (Qinv * Ainv * Pinv * P * DA)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Ainv * DA) := by
        congr 1
        calc
          Q * (Qinv * Ainv * Pinv * P * DA) =
              (Q * Qinv) * (Ainv * Pinv * P * DA) := by
                simp only [Matrix.mul_assoc]
          _ = Ainv * Pinv * P * DA := by rw [hQQinv, one_mul]
          _ = Ainv * (Pinv * P) * DA := by rw [Matrix.mul_assoc Ainv Pinv P]
          _ = Ainv * DA := by rw [hPinvP, mul_one]
  have htermQ :
      Matrix.trace (Qinv * Ainv * Pinv * (P * A * DQ)) =
        Matrix.trace (Qinv * DQ) := by
    congr 1
    calc
      Qinv * Ainv * Pinv * (P * A * DQ) =
          Qinv * Ainv * ((Pinv * P) * (A * DQ)) := by
            simp only [Matrix.mul_assoc]
      _ = Qinv * Ainv * (A * DQ) := by rw [hPinvP, one_mul]
      _ = Qinv * ((Ainv * A) * DQ) := by
        simp only [Matrix.mul_assoc]
      _ = Qinv * DQ := by rw [hAinvA, one_mul]
  calc
    Matrix.trace
        (Qinv * Ainv * Pinv *
          entrywiseMatrixDerivation D (P * A * Q)) =
        Matrix.trace (Qinv * Ainv * Pinv * (DP * A * Q)) +
          Matrix.trace (Qinv * Ainv * Pinv * (P * DA * Q)) +
            Matrix.trace (Qinv * Ainv * Pinv * (P * A * DQ)) := by
      dsimp only [DP, DA, DQ]
      rw [entrywiseMatrixDerivation_mul D (P * A) Q,
        entrywiseMatrixDerivation_mul D P A]
      simp only [mul_add, add_mul, Matrix.trace_add]
    _ = _ := by rw [htermP, htermA, htermQ]

end QEC.Coding.AlgebraicGeometry

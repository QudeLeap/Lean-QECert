import QEC.Coding.AlgebraicGeometry.Trace.MatrixDerivation
import QEC.Coding.AlgebraicGeometry.Differentials.RatFuncDerivation

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Polynomial matrices and the rational derivation

This module identifies entrywise formal differentiation of polynomial matrices
with entrywise application of the rational-function derivation after mapping
coefficients into the fraction field.  In particular, the logarithmic trace
term of two polynomial matrices is itself the image of an actual polynomial.

There is no Smith-normal-form, residue, ramification, duality, genus, or
Riemann--Roch statement in this module.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

variable {k : Type*} [Field k]

/-- Apply formal polynomial differentiation to every matrix entry. -/
noncomputable def entrywisePolynomialDerivative {m n : Type*}
    (A : Matrix m n k[X]) : Matrix m n k[X] :=
  Matrix.of fun i j => (A i j).derivative

@[simp]
theorem entrywisePolynomialDerivative_apply {m n : Type*}
    (A : Matrix m n k[X]) (i : m) (j : n) :
    entrywisePolynomialDerivative A i j = (A i j).derivative :=
  rfl

/-- The rational derivation with value one at `X` restricts to formal
polynomial differentiation. -/
theorem rationalDerivation_one_algebraMap_polynomial (p : k[X]) :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
        (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative := by
  let D := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  have hX : D RatFunc.X = 1 := by
    exact RatFuncDerivation.rationalDerivation_apply_X (k := k) (1 : RatFunc k)
  calc
    D (algebraMap k[X] (RatFunc k) p) =
        D (Polynomial.aeval RatFunc.X p) := by
          rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval RatFunc.X p.derivative • D RatFunc.X := by
      rw [Derivation.map_aeval]
    _ = Polynomial.aeval RatFunc.X p.derivative := by
      rw [hX, smul_eq_mul, mul_one]
    _ = algebraMap k[X] (RatFunc k) p.derivative :=
      RatFunc.aeval_X_left_eq_algebraMap p.derivative

/-- Mapping a polynomial matrix into the rational function field commutes
with entrywise differentiation. -/
theorem entrywiseMatrixDerivation_map_polynomial {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n k[X]) :
    entrywiseMatrixDerivation
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1)
        ((algebraMap k[X] (RatFunc k)).mapMatrix A) =
      (algebraMap k[X] (RatFunc k)).mapMatrix
        (entrywisePolynomialDerivative A) := by
  ext i j
  simp only [entrywiseMatrixDerivation_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, entrywisePolynomialDerivative_apply]
  exact rationalDerivation_one_algebraMap_polynomial (A i j)

/-- A polynomial change-of-basis logarithmic trace term remains polynomial
after mapping to the rational function field. -/
theorem trace_map_mul_entrywiseMatrixDerivation_polynomial
    {n : Type*} [Fintype n] [DecidableEq n]
    (Pinv P : Matrix n n k[X]) :
    Matrix.trace
        ((algebraMap k[X] (RatFunc k)).mapMatrix Pinv *
          entrywiseMatrixDerivation
            (RatFuncDerivation.rationalDerivation
              (k := k) (M := RatFunc k) 1)
            ((algebraMap k[X] (RatFunc k)).mapMatrix P)) =
      algebraMap k[X] (RatFunc k)
        (Matrix.trace (Pinv * entrywisePolynomialDerivative P)) := by
  rw [entrywiseMatrixDerivation_map_polynomial]
  rw [← (algebraMap k[X] (RatFunc k)).mapMatrix.map_mul]
  exact
    (AddMonoidHom.map_trace
      (algebraMap k[X] (RatFunc k)).toAddMonoidHom
      (Pinv * entrywisePolynomialDerivative P)).symm

end QEC.Coding.AlgebraicGeometry

import QEC.Coding.AlgebraicGeometry.Trace.PolynomialMatrixDerivation
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicPolynomialLogarithmicResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Finite residues of diagonal polynomial matrix logarithmic derivatives

This module lifts the scalar polynomial logarithmic-residue calculation to a
finite diagonal matrix.  The trace of an arbitrary polynomial weight matrix
times the diagonal logarithmic derivative is the sum of the diagonal weighted
scalar terms, and its normalized residue is the corresponding finite sum of
principal-ideal multiplicities.

There is no Smith-normal-form construction, quotient-trace identification,
global residue theorem, duality, genus, or Riemann--Roch statement here.
-/

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry

variable {k : Type*} [Field k]

/-- The diagonal rational matrix with entries inverse to the images of the
given polynomials. -/
noncomputable def rationalDiagonalMatrixInverse
    {n : Type*} [DecidableEq n] (a : n → k[X]) :
    Matrix n n (RatFunc k) :=
  Matrix.diagonal fun i => (algebraMap k[X] (RatFunc k) (a i))⁻¹

private theorem entrywisePolynomialDerivative_diagonal
    {n : Type*} [DecidableEq n] (a : n → k[X]) :
    entrywisePolynomialDerivative (Matrix.diagonal a) =
      Matrix.diagonal fun i => (a i).derivative := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [entrywisePolynomialDerivative_apply, Matrix.diagonal_apply_eq]
  · simp only [entrywisePolynomialDerivative_apply,
      Matrix.diagonal_apply_ne _ hij, Polynomial.derivative_zero]

/-- The weighted diagonal matrix logarithmic trace is the finite sum of its
diagonal scalar logarithmic terms. -/
theorem trace_map_mul_rationalDiagonalInverse_derivative
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n k[X]) (a : n → k[X]) :
    Matrix.trace
        (((algebraMap k[X] (RatFunc k)).mapMatrix R *
            rationalDiagonalMatrixInverse a) *
          entrywiseMatrixDerivation
            (RatFuncDerivation.rationalDerivation
              (k := k) (M := RatFunc k) 1)
            ((algebraMap k[X] (RatFunc k)).mapMatrix
              (Matrix.diagonal a))) =
      ∑ i, algebraMap k[X] (RatFunc k) (R i i) *
        (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
          algebraMap k[X] (RatFunc k) (a i).derivative := by
  classical
  rw [entrywiseMatrixDerivation_map_polynomial,
    entrywisePolynomialDerivative_diagonal]
  unfold rationalDiagonalMatrixInverse
  simp only [RingHom.mapMatrix_apply]
  rw [
    Matrix.diagonal_map (map_zero (algebraMap k[X] (RatFunc k)))]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal,
    Matrix.map_apply]

namespace Differential

open FunctionFieldDifferential

variable [Finite k]

/-- The sum of the diagonal weighted polynomial logarithmic differentials,
as an actual simple-pole differential at a finite rational place. -/
noncomputable def rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  ∑ i, rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
    p (R i i) (a i) (ha i)

/-- The ambient differential represented by the diagonal logarithmic trace
has the expected matrix-trace coefficient. -/
theorem coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    ((rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p R a ha :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      Matrix.trace
          (((algebraMap k[X] (RatFunc k)).mapMatrix R *
              rationalDiagonalMatrixInverse a) *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix
                (Matrix.diagonal a))) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  unfold rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
  change
    (simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)).subtype
      (∑ i, rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
        p (R i i) (a i) (ha i)) = _
  rw [map_sum]
  calc
    (∑ i, (simplePoleDifferentialLattice
        (GlobalPlace.rationalAdic p)).subtype
          (rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
            p (R i i) (a i) (ha i))) =
        ∑ i, (algebraMap k[X] (RatFunc k) (R i i) *
            (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
            algebraMap k[X] (RatFunc k) (a i).derivative) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
        p (R i i) (a i) (ha i)
    _ = (∑ i, algebraMap k[X] (RatFunc k) (R i i) *
          (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
          algebraMap k[X] (RatFunc k) (a i).derivative) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
      rw [Finset.sum_smul]
    _ = _ := by
      rw [trace_map_mul_rationalDiagonalInverse_derivative]

/-- The normalized residue of the diagonal matrix logarithmic differential
is the finite sum of reduced diagonal coefficients weighted by the exact
principal-ideal multiplicities. -/
theorem simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p R a ha) =
      ∑ i, (GlobalPlace.rationalAdic p).residue
          (GlobalPlace.rationalAdicPolynomialToValuationRing p (R i i)) *
        (multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) :
          (GlobalPlace.rationalAdic p).residueField) := by
  unfold rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential
    p (R i i) (a i) (ha i)

end Differential

end QEC.Coding.AlgebraicGeometry

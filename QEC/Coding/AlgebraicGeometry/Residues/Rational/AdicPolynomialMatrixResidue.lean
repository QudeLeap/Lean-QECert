import QEC.Coding.AlgebraicGeometry.Trace.PolynomialMatrixDerivation
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicPolynomialDifferential

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Finite residues of polynomial matrix logarithmic traces

This module composes polynomial-matrix differentiation with finite-place
regularity.  The logarithmic trace term built from two polynomial matrices is
an actual polynomial multiple of `dX`, hence its normalized residue at every
finite rational place is zero.

There is no Smith-normal-form decomposition, ramification formula, global
residue theorem, duality, genus, or Riemann--Roch statement here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc
open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

/-- The polynomial whose fraction-field image is the logarithmic trace term
of a polynomial matrix and a polynomial inverse matrix. -/
noncomputable def polynomialMatrixLogarithmicTrace
    {n : Type*} [Fintype n] [DecidableEq n]
    (Pinv P : Matrix n n k[X]) : k[X] :=
  Matrix.trace (Pinv * entrywisePolynomialDerivative P)

/-- The polynomial matrix logarithmic trace, regarded as an actual
simple-pole differential at a finite rational place. -/
noncomputable def polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    Differential.simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p) :=
  Differential.rationalAdicPolynomialDifferentialAtSimplePole p
    (polynomialMatrixLogarithmicTrace Pinv P)

/-- The ambient coefficient of the polynomial matrix logarithmic trace is
the expected fraction-field matrix trace. -/
theorem coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    ((polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p Pinv P :
      Differential.simplePoleDifferentialLattice
        (GlobalPlace.rationalAdic p)) : Differential k (RatFunc k)) =
      Matrix.trace
          ((algebraMap k[X] (RatFunc k)).mapMatrix Pinv *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix P)) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  unfold polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
  unfold Differential.rationalAdicPolynomialDifferentialAtSimplePole
  rw [Differential.coe_rationalAdicPolynomialDifferential]
  change
    algebraMap k[X] (RatFunc k)
        (polynomialMatrixLogarithmicTrace Pinv P) •
      functionFieldDifferentialGenerator (k := k) (F := RatFunc k) = _
  unfold polynomialMatrixLogarithmicTrace
  rw [trace_map_mul_entrywiseMatrixDerivation_polynomial]

/-- Polynomial matrix logarithmic trace terms have zero normalized residue at
every finite rational place. -/
theorem simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (Pinv P : Matrix n n k[X]) :
    Differential.simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p Pinv P) = 0 := by
  exact Differential.simplePoleResidue_rationalAdicPolynomialDifferential
    p (polynomialMatrixLogarithmicTrace Pinv P)

end QEC.Coding.AlgebraicGeometry

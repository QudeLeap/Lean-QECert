import QEC.Coding.AlgebraicGeometry.Residues.Local.Residue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Polynomial differentials at finite rational places

Polynomial multiples of the rational differential generator are regular at
every finite rational place.  This module packages that regularity in the
actual local differential lattice and derives vanishing of the normalized
simple-pole residue.

There is no matrix, Smith-normal-form, global residue, duality, genus, or
Riemann--Roch statement in this module.
-/

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry
namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

/-- The actual rational differential generator is regular at every finite
normalized rational place. -/
theorem functionFieldDifferentialGenerator_mem_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    functionFieldDifferentialGenerator (k := k) (F := RatFunc k) ∈
      localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  let x : (GlobalPlace.rationalAdic p).valuationRing :=
    GlobalPlace.rationalAdicPolynomialToValuationRing p Polynomial.X
  have hx := differential_mem_localDifferentialLattice
    (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p) x
  have hxValue : (x : RatFunc k) = RatFunc.X := by
    simp only [x, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  have hX :
      functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  rw [hxValue, differential_eq_functionFieldDerivation_smul_generator,
    hX] at hx
  simpa using hx

/-- A polynomial multiple of `dX`, as an actual member of the regular local
differential lattice at a finite rational place. -/
noncomputable def rationalAdicPolynomialDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    localDifferentialLattice (GlobalPlace.rationalAdic p) :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p b •
    ⟨functionFieldDifferentialGenerator (k := k) (F := RatFunc k),
      functionFieldDifferentialGenerator_mem_rationalAdic p⟩

/-- The regular local polynomial differential has the expected ambient
coefficient and differential generator. -/
@[simp]
theorem coe_rationalAdicPolynomialDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicPolynomialDifferential p b :
      localDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      algebraMap k[X] (RatFunc k) b •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  change
    ((GlobalPlace.rationalAdicPolynomialToValuationRing p b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]

/-- The same regular polynomial differential, viewed in the simple-pole
lattice. -/
noncomputable def rationalAdicPolynomialDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  ⟨rationalAdicPolynomialDifferential p b,
    localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
      (rationalAdicPolynomialDifferential p b).property⟩

/-- Polynomial differentials have zero normalized residue at every finite
rational place. -/
theorem simplePoleResidue_rationalAdicPolynomialDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicPolynomialDifferentialAtSimplePole p b) = 0 := by
  exact simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
    (rationalAdicPolynomialDifferentialAtSimplePole p b)
    (rationalAdicPolynomialDifferential p b).property

end Differential
end QEC.Coding.AlgebraicGeometry

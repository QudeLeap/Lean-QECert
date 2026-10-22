import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.Residues.Local.LogarithmicResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicPolynomialDifferential

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Weighted polynomial logarithmic residues at finite rational places

This module packages a polynomial multiple of `da / a` in the actual
simple-pole lattice at a finite rational place.  Its normalized residue is the
reduction of the polynomial coefficient times the exact ideal multiplicity of
`a` at that place.

There is no Smith-normal-form decomposition, quotient-trace comparison,
global residue theorem, duality, genus, or Riemann--Roch statement here.
-/

open scoped Polynomial RatFunc WithZero

namespace QEC.Coding.AlgebraicGeometry

namespace GlobalPlace

variable {k : Type*} [Field k] [Finite k]

/-- The order of a nonzero polynomial at a finite rational place is the
multiplicity of the corresponding principal ideal at the height-one prime. -/
theorem rationalAdic_order_algebraMap_polynomial
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (a : k[X]) (ha : a ≠ 0) :
    (rationalAdic p).order (algebraMap k[X] (RatFunc k) a) =
      (multiplicity p.asIdeal (Ideal.span ({a} : Set k[X])) : ℤ) := by
  unfold order rationalAdic
  rw [p.valuation_of_algebraMap,
    p.intValuation_eq_exp_neg_multiplicity ha, WithZero.log_exp]
  simp only [neg_neg]

end GlobalPlace

namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

omit [Finite k] in
private theorem functionFieldDerivation_apply_polynomial (a : k[X]) :
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) a) =
      algebraMap k[X] (RatFunc k) a.derivative := by
  have hX :
      functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  calc
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) a) =
        functionFieldDerivation (k := k) (F := RatFunc k)
          (Polynomial.aeval RatFunc.X a) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval RatFunc.X a.derivative •
          functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X := by
            rw [Derivation.map_aeval]
    _ = Polynomial.aeval RatFunc.X a.derivative := by
          rw [hX, smul_eq_mul, mul_one]
    _ = algebraMap k[X] (RatFunc k) a.derivative :=
      RatFunc.aeval_X_left_eq_algebraMap a.derivative

/-- A polynomial coefficient times the logarithmic differential of a
nonzero polynomial, as an actual simple-pole differential at a finite
rational place. -/
noncomputable def rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p r •
    logarithmicDifferentialAtSimplePole
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
      (algebraMap k[X] (RatFunc k) a)
      (RatFunc.algebraMap_ne_zero ha)

/-- The weighted local logarithmic differential has its expected ambient
rational-function coefficient. -/
theorem coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    ((rationalAdicWeightedPolynomialLogDifferentialAtSimplePole p r a ha :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      (algebraMap k[X] (RatFunc k) r *
          (algebraMap k[X] (RatFunc k) a)⁻¹ *
          algebraMap k[X] (RatFunc k) a.derivative) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  change
    ((GlobalPlace.rationalAdicPolynomialToValuationRing p r :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) •
        logarithmicDifferential (k := k) (F := RatFunc k)
          (algebraMap k[X] (RatFunc k) a) = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    functionFieldDerivation_apply_polynomial]
  simp only [smul_smul, smul_eq_mul]
  ring

/-- The normalized residue of the weighted logarithmic differential is the
reduced coefficient times the exact principal-ideal multiplicity. -/
theorem simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicWeightedPolynomialLogDifferentialAtSimplePole p r a ha) =
      (GlobalPlace.rationalAdic p).residue
          (GlobalPlace.rationalAdicPolynomialToValuationRing p r) *
        (multiplicity p.asIdeal (Ideal.span ({a} : Set k[X])) :
          (GlobalPlace.rationalAdic p).residueField) := by
  unfold rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
  rw [simplePoleResidue_smul,
    simplePoleResidue_logarithmicDifferential,
    GlobalPlace.rationalAdic_order_algebraMap_polynomial p a ha]
  simp only [Int.cast_natCast]

end Differential

end QEC.Coding.AlgebraicGeometry

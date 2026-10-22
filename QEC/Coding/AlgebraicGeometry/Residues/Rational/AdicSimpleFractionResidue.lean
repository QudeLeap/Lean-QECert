/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Residues.Global.LogarithmicResidue
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.EulerTrace

/-!
# Finite-place residues of rational simple fractions

This module computes the traced normalized residue of `(b / q) dX` at the
finite rational place associated to the monic irreducible polynomial `q`.
The local representative is constructed from the regular function `b / q'`
times the logarithmic differential `dq / q`; Euler's trace identity then
computes its constant-field trace.

No infinity-place formula, global residue sum, extension-field trace
transport, duality, genus, or Riemann--Roch theorem is asserted here.
-/

open scoped Polynomial RatFunc WithZero

namespace QEC.Coding.AlgebraicGeometry
namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

private theorem rationalAdicPolynomial_derivative_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdicPolynomial p).derivative ≠ 0 := by
  exact (Polynomial.separable_iff_derivative_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p)).mp
      (PerfectField.separable_of_irreducible
        (GlobalPlace.rationalAdicPolynomial_irreducible p))

private theorem rationalAdicPolynomial_derivative_not_mem
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdicPolynomial p).derivative ∉ p.asIdeal := by
  rw [GlobalPlace.rationalAdic_asIdeal_eq_span p,
    Ideal.mem_span_singleton, Polynomial.dvd_derivative_iff]
  exact rationalAdicPolynomial_derivative_ne_zero p

private theorem rationalAdicPolynomialDerivative_isUnit
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    IsUnit (GlobalPlace.rationalAdicPolynomialToValuationRing p
      (GlobalPlace.rationalAdicPolynomial p).derivative) := by
  apply (Valuation.valuationSubring.integers
    (GlobalPlace.rationalAdic p).valuation).isUnit_iff_valuation_eq_one.mpr
  change (GlobalPlace.rationalAdic p).valuation
      ((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial p).derivative :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) = 1
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr
    (rationalAdicPolynomial_derivative_not_mem p)

private noncomputable def rationalAdicRegularQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    (GlobalPlace.rationalAdic p).valuationRing :=
  GlobalPlace.rationalAdicPolynomialToValuationRing p b *
    ↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹)

private theorem coe_rationalAdicRegularQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicRegularQuotient p b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) =
      algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p).derivative := by
  unfold rationalAdicRegularQuotient
  rw [show
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p b *
        ↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k)) =
        ((GlobalPlace.rationalAdicPolynomialToValuationRing p b :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) *
          (((↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹) :
            (GlobalPlace.rationalAdic p).valuationRing)) : RatFunc k) by rfl]
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  change algebraMap k[X] (RatFunc k) b *
      algebraMap (GlobalPlace.rationalAdic p).valuationRing (RatFunc k)
        (↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) = _
  rw [map_units_inv (algebraMap
      (GlobalPlace.rationalAdic p).valuationRing (RatFunc k))
      (rationalAdicPolynomialDerivative_isUnit p).unit,
    (rationalAdicPolynomialDerivative_isUnit p).unit_spec]
  change algebraMap k[X] (RatFunc k) b *
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial p).derivative :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k))⁻¹ = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  rw [div_eq_mul_inv]

private theorem rationalAdicPolynomial_map_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p) ≠ 0 :=
  RatFunc.algebraMap_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p).ne_zero

omit [Finite k] in
private theorem functionFieldDerivation_apply_polynomial (b : k[X]) :
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) b) =
      algebraMap k[X] (RatFunc k) b.derivative := by
  have hX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  calc
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) b) =
        functionFieldDerivation (k := k) (F := RatFunc k)
          (Polynomial.aeval RatFunc.X b) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval RatFunc.X b.derivative •
          functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X := by
            rw [Derivation.map_aeval]
    _ = Polynomial.aeval RatFunc.X b.derivative := by
          rw [hX, smul_eq_mul, mul_one]
    _ = algebraMap k[X] (RatFunc k) b.derivative :=
      RatFunc.aeval_X_left_eq_algebraMap b.derivative

/-- The actual local simple-pole representative of `(b / q) dX` at the
finite rational place cut out by `q`. -/
noncomputable def rationalAdicSimpleFractionAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  rationalAdicRegularQuotient p b •
    logarithmicDifferentialAtSimplePole (k := k) (F := RatFunc k)
      (GlobalPlace.rationalAdic p)
      (algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p))
      (rationalAdicPolynomial_map_ne_zero p)

/-- The constructed local representative is the rational simple-fraction
differential `(b / q) dX`. -/
theorem coe_rationalAdicSimpleFractionAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicSimpleFractionAtSimplePole p b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p)) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  change (rationalAdicRegularQuotient p b : RatFunc k) •
      logarithmicDifferential (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p)) = _
  rw [coe_rationalAdicRegularQuotient, logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    functionFieldDerivation_apply_polynomial]
  simp only [smul_smul]
  field_simp [rationalAdicPolynomial_map_ne_zero p,
    rationalAdicPolynomial_derivative_ne_zero p]

private theorem rationalAdic_order_polynomial
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdic p).order
        (algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p)) = 1 := by
  unfold GlobalPlace.order GlobalPlace.rationalAdic
  rw [p.valuation_of_algebraMap,
    p.intValuation_singleton
      (GlobalPlace.rationalAdicPolynomial_irreducible p).ne_zero
      (GlobalPlace.rationalAdic_asIdeal_eq_span p)]
  simp

private theorem rationalAdicResidue_regularQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    [Fact (Irreducible (GlobalPlace.rationalAdicPolynomial p))] :
    (GlobalPlace.rationalAdic p).residue (rationalAdicRegularQuotient p b) =
      GlobalPlace.rationalAdicResidueEquiv p
        (Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
          Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
            (GlobalPlace.rationalAdicPolynomial p).derivative) := by
  calc
    (GlobalPlace.rationalAdic p).residue (rationalAdicRegularQuotient p b) =
        (GlobalPlace.rationalAdic p).residue
            (GlobalPlace.rationalAdicPolynomialToValuationRing p b) *
          ((GlobalPlace.rationalAdic p).residue
            (GlobalPlace.rationalAdicPolynomialToValuationRing p
              (GlobalPlace.rationalAdicPolynomial p).derivative))⁻¹ := by
      unfold rationalAdicRegularQuotient
      rw [map_mul, map_units_inv,
        (rationalAdicPolynomialDerivative_isUnit p).unit_spec]
    _ = GlobalPlace.rationalAdicResidueEquiv p
          (AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial p) b) *
        (GlobalPlace.rationalAdicResidueEquiv p
          (AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial p)
            (GlobalPlace.rationalAdicPolynomial p).derivative))⁻¹ := by
      rw [GlobalPlace.rationalAdicResidueEquiv_mk,
        GlobalPlace.rationalAdicResidueEquiv_mk]
    _ = GlobalPlace.rationalAdicResidueEquiv p
        (Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
          Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
            (GlobalPlace.rationalAdicPolynomial p).derivative) := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.aeval_eq, map_div₀]
      rw [div_eq_mul_inv]

private theorem simplePoleResidue_rationalAdicSimpleFraction
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    [Fact (Irreducible (GlobalPlace.rationalAdicPolynomial p))] :
    simplePoleResidue (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b) =
      GlobalPlace.rationalAdicResidueEquiv p
        (Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
          Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
            (GlobalPlace.rationalAdicPolynomial p).derivative) := by
  unfold rationalAdicSimpleFractionAtSimplePole
  rw [simplePoleResidue_smul,
    simplePoleResidue_logarithmicDifferential,
    rationalAdic_order_polynomial]
  simp only [Int.cast_one, mul_one]
  exact rationalAdicResidue_regularQuotient p b

private theorem rationalAdicResidueEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (a : k) :
    letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
      GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
    GlobalPlace.rationalAdicResidueEquiv p
        (algebraMap k (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p)) a) =
      algebraMap k (GlobalPlace.rationalAdic p).residueField a := by
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  change (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing p (Polynomial.C a)) =
    (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.constantsToValuationRing (GlobalPlace.rationalAdic p) a)
  apply congrArg (GlobalPlace.rationalAdic p).residue
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]

/-- The traced normalized residue of the finite rational simple fraction
`(b / q) dX` is the next-to-leading coefficient of `b`. -/
theorem simplePoleTraceResidue_rationalAdicSimpleFraction
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial p).degree) :
    simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b :
          Differential k (RatFunc k))
        (rationalAdicSimpleFractionAtSimplePole p b).property =
      b.coeff ((GlobalPlace.rationalAdicPolynomial p).natDegree - 1) := by
  letI : Fact (Irreducible (GlobalPlace.rationalAdicPolynomial p)) :=
    ⟨GlobalPlace.rationalAdicPolynomial_irreducible p⟩
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  letI : FiniteDimensional k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueField_finiteDimensional (GlobalPlace.rationalAdic p)
  let e := GlobalPlace.rationalAdicResidueEquiv p
  have he : RingHom.comp
      (algebraMap k (GlobalPlace.rationalAdic p).residueField)
      (RingEquiv.refl k) =
      RingHom.comp (e : AdjoinRoot (GlobalPlace.rationalAdicPolynomial p) →+*
        (GlobalPlace.rationalAdic p).residueField)
        (algebraMap k (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p))) := by
    ext a
    simp only [RingHom.comp_apply, e]
    exact (rationalAdicResidueEquiv_algebraMap p a).symm
  let x : AdjoinRoot (GlobalPlace.rationalAdicPolynomial p) :=
    Polynomial.aeval
        (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
      Polynomial.aeval
        (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
        (GlobalPlace.rationalAdicPolynomial p).derivative
  change Algebra.trace k (GlobalPlace.rationalAdic p).residueField
      (simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b)) = _
  rw [simplePoleResidue_rationalAdicSimpleFraction]
  calc
    Algebra.trace k (GlobalPlace.rationalAdic p).residueField (e x) =
        Algebra.trace k (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p)) x := by
      exact (Algebra.trace_eq_of_equiv_equiv (RingEquiv.refl k) e he x).symm
    _ = b.coeff ((GlobalPlace.rationalAdicPolynomial p).natDegree - 1) :=
      RatFuncEulerTrace.trace_aeval_div_derivative
        (GlobalPlace.rationalAdicPolynomial p) b
        (GlobalPlace.rationalAdicPolynomial_monic p) hb

end Differential
end QEC.Coding.AlgebraicGeometry

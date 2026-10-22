import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicSimpleFractionResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.InfinitySimpleFractionResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Orders of the rational differential generator

This module computes the intrinsic local order of the actual differential
`dX` on the rational function field.  It is regular and nonvanishing at every
finite normalized place, so its order there is zero.  At the normalized place
at infinity its order is `-2`.

The proof uses the normalized logarithmic residue of a local parameter to pin
its differential order to `-1`; it does not assume a Laurent expansion or a
canonical-divisor formula.  No global residue theorem, genus, duality, or
Riemann--Roch identity is stated here.
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

private theorem rationalAdic_order_derivative
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdic p).order
        (algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p).derivative) = 0 := by
  have hvaluation :
      (GlobalPlace.rationalAdic p).valuation
          (algebraMap k[X] (RatFunc k)
            (GlobalPlace.rationalAdicPolynomial p).derivative) = 1 := by
    change (p.valuation (RatFunc k))
        (algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p).derivative) = 1
    exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr
      (rationalAdicPolynomial_derivative_not_mem p)
  unfold GlobalPlace.order
  rw [hvaluation]
  simp

private theorem rationalInfinity_order_inverseX :
    (GlobalPlace.rationalInfinity k).order (RatFunc.X : RatFunc k)⁻¹ = 1 := by
  rw [GlobalPlace.order_inv,
    RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      k RatFunc.X RatFunc.X_ne_zero,
    RatFunc.intDegree_X]
  norm_num

private theorem logarithmicDifferential_ne_zero_of_order_eq_one
    (P : GlobalPlace k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (horder : P.order f = 1) :
    logarithmicDifferential (k := k) (F := RatFunc k) f ≠ 0 := by
  intro hzero
  have hresidue := simplePoleResidue_logarithmicDifferential
    (k := k) (F := RatFunc k) P f hf
  have hsubtype :
      logarithmicDifferentialAtSimplePole (k := k) (F := RatFunc k) P f hf =
        0 := by
    apply Subtype.ext
    exact hzero
  rw [hsubtype, map_zero, horder] at hresidue
  norm_num at hresidue

private theorem differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (P : GlobalPlace k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (horder : P.order f = 1) :
    differentialOrder (k := k) (F := RatFunc k) P
        (logarithmicDifferential (k := k) (F := RatFunc k) f)
        (logarithmicDifferential_ne_zero_of_order_eq_one P f hf horder) = -1 := by
  let omega := logarithmicDifferential (k := k) (F := RatFunc k) f
  let homega : omega ≠ 0 :=
    logarithmicDifferential_ne_zero_of_order_eq_one P f hf horder
  have hsimple : omega ∈ simplePoleDifferentialLattice P :=
    logarithmicDifferential_isGlobalSimplePole
      (k := k) (F := RatFunc k) f hf P
  have hresidue :
      simplePoleResidue (k := k) (F := RatFunc k) P
          (logarithmicDifferentialAtSimplePole
            (k := k) (F := RatFunc k) P f hf) = 1 := by
    simpa only [horder, Int.cast_one] using
      (simplePoleResidue_logarithmicDifferential
        (k := k) (F := RatFunc k) P f hf)
  have hnotRegular : omega ∉ localDifferentialLattice P := by
    intro hregular
    have hzero := simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := RatFunc k) P
      (logarithmicDifferentialAtSimplePole
        (k := k) (F := RatFunc k) P f hf) hregular
    rw [hresidue] at hzero
    exact one_ne_zero hzero
  have hge : -1 ≤ differentialOrder (k := k) (F := RatFunc k) P omega homega :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) P omega homega).mp hsimple
  have hnge : ¬ 0 ≤ differentialOrder (k := k) (F := RatFunc k) P omega homega := by
    intro hnonnegative
    apply hnotRegular
    exact (mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := RatFunc k) P omega homega).mpr hnonnegative
  apply le_antisymm
  · exact Int.le_sub_one_iff.mpr (lt_of_not_ge hnge)
  · exact hge

/-- The actual differential generator `dX` has order zero at every finite
normalized rational place. -/
theorem differentialOrder_generator_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)) = 0 := by
  let q : RatFunc k := algebraMap k[X] (RatFunc k)
    (GlobalPlace.rationalAdicPolynomial p)
  let q' : RatFunc k := algebraMap k[X] (RatFunc k)
    (GlobalPlace.rationalAdicPolynomial p).derivative
  let c : RatFunc k := q⁻¹ * q'
  have hq : q ≠ 0 := RatFunc.algebraMap_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p).ne_zero
  have hq' : q' ≠ 0 := RatFunc.algebraMap_ne_zero
    (rationalAdicPolynomial_derivative_ne_zero p)
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero hq) hq'
  have hqOrder : (GlobalPlace.rationalAdic p).order q = 1 :=
    rationalAdic_order_polynomial p
  have hq'Order : (GlobalPlace.rationalAdic p).order q' = 0 :=
    rationalAdic_order_derivative p
  have hcOrder : (GlobalPlace.rationalAdic p).order c = -1 := by
    dsimp only [c]
    rw [GlobalPlace.order_mul (GlobalPlace.rationalAdic p)
      (inv_ne_zero hq) hq', GlobalPlace.order_inv, hqOrder, hq'Order]
    omega
  have hlogEq : logarithmicDifferential (k := k) (F := RatFunc k) q =
      c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    rw [logarithmicDifferential,
      differential_eq_functionFieldDerivation_smul_generator,
      show functionFieldDerivation (k := k) (F := RatFunc k) q = q' by
        exact functionFieldDerivation_apply_polynomial
          (GlobalPlace.rationalAdicPolynomial p)]
    simp only [smul_smul, smul_eq_mul, c]
  have hlogOrder := differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (GlobalPlace.rationalAdic p) q hq hqOrder
  have hscaledOrder :
      differentialOrder (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
          (smul_ne_zero hc
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k))) = -1 := by
    simpa only [hlogEq] using hlogOrder
  rw [differentialOrder_smul (k := k) (F := RatFunc k)
    (GlobalPlace.rationalAdic p) c hc
    (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
    (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)),
    hcOrder] at hscaledOrder
  omega

/-- The actual differential generator `dX` has order `-2` at the normalized
rational place at infinity. -/
theorem differentialOrder_generator_rationalInfinity :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)) = -2 := by
  let y : RatFunc k := (RatFunc.X : RatFunc k)⁻¹
  let c : RatFunc k := -(RatFunc.X : RatFunc k)⁻¹
  have hy : y ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  have hc : c ≠ 0 := neg_ne_zero.mpr hy
  have hyOrder : (GlobalPlace.rationalInfinity k).order y = 1 :=
    rationalInfinity_order_inverseX
  have hminusOneOrder :
      (GlobalPlace.rationalInfinity k).order (-1 : RatFunc k) = 0 := by
    simpa using (GlobalPlace.rationalInfinity k).order_algebraMap
      (-1 : k) (by simp)
  have hcOrder : (GlobalPlace.rationalInfinity k).order c = 1 := by
    rw [show c = (-1 : RatFunc k) * y by simp [c, y]]
    rw [GlobalPlace.order_mul (GlobalPlace.rationalInfinity k)
      (by simp) hy, hminusOneOrder, hyOrder]
    norm_num
  have hlogEq : logarithmicDifferential (k := k) (F := RatFunc k) y =
      c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    have hDX :
        functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
      simpa using
        (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
    rw [logarithmicDifferential,
      differential_eq_functionFieldDerivation_smul_generator,
      Derivation.leibniz_inv, hDX]
    simp only [smul_smul, smul_eq_mul, y, c]
    field_simp [RatFunc.X_ne_zero]
  have hlogOrder := differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (GlobalPlace.rationalInfinity k) y hy hyOrder
  have hscaledOrder :
      differentialOrder (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
          (smul_ne_zero hc
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k))) = -1 := by
    simpa only [hlogEq] using hlogOrder
  rw [differentialOrder_smul (k := k) (F := RatFunc k)
    (GlobalPlace.rationalInfinity k) c hc
    (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
    (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)),
    hcOrder] at hscaledOrder
  omega

/-- Scaling `dX` by a nonzero rational function gives exactly the function's
order at a finite rational place. -/
theorem differentialOrder_smul_generator_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (f : RatFunc k) (hf : f ≠ 0) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
      (GlobalPlace.rationalAdic p).order f := by
  calc
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
        (GlobalPlace.rationalAdic p).order f +
          differentialOrder (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k)) :=
      differentialOrder_smul (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p) f hf
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))
    _ = (GlobalPlace.rationalAdic p).order f := by
      rw [differentialOrder_generator_rationalAdic, add_zero]

/-- Scaling `dX` by a nonzero rational function gives the function order minus
two at the normalized rational place at infinity. -/
theorem differentialOrder_smul_generator_rationalInfinity
    (f : RatFunc k) (hf : f ≠ 0) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
      (GlobalPlace.rationalInfinity k).order f - 2 := by
  calc
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
        (GlobalPlace.rationalInfinity k).order f +
          differentialOrder (k := k) (F := RatFunc k)
            (GlobalPlace.rationalInfinity k)
            (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k)) :=
      differentialOrder_smul (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k) f hf
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))
    _ = (GlobalPlace.rationalInfinity k).order f - 2 := by
      rw [differentialOrder_generator_rationalInfinity]
      ring

end Differential
end QEC.Coding.AlgebraicGeometry

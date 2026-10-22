/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Residues.Global.LogarithmicResidue
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.Residues.Rational.InfinityResidue

/-!
# Infinity residue of a proper rational simple fraction

This module computes the traced normalized residue at infinity of
`(b / q) dX`, where `q` is monic and `degree b < degree q`.  The proof uses
the reciprocal coordinate `X⁻¹`: the differential is the logarithmic
differential of that coordinate multiplied by the infinity-regular scalar
`-X b / q`.  Monic leading-term cancellation computes its reduction.

No global residue sum, extension-field trace transport, duality, genus, or
Riemann--Roch theorem is asserted here.
-/

open scoped Polynomial RatFunc WithZero

namespace QEC.Coding.AlgebraicGeometry
namespace Differential

open FunctionFieldDifferential

variable {k : Type*} [Field k] [Finite k]

private theorem rationalInfinitySimpleFractionCoefficient_mem
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) ∈
      (GlobalPlace.rationalInfinity k).valuationRing := by
  classical
  by_cases hb0 : b = 0
  · simp [hb0]
  have hq0 : q ≠ 0 := hq.ne_zero
  have hb_map : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    RatFunc.algebraMap_ne_zero hb0
  have hq_map : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq0
  have hquotient :
      algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q ≠ 0 :=
    div_ne_zero hb_map hq_map
  have hscalar :
      -(RatFunc.X *
          (algebraMap k[X] (RatFunc k) b /
            algebraMap k[X] (RatFunc k) q)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero RatFunc.X_ne_zero hquotient)
  apply (GlobalPlace.mem_valuationRing_iff
    (GlobalPlace.rationalInfinity k) _).mpr
  change RatFunc.inftyValuation k
      (-(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q))) ≤ 1
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero (F := k) hscalar,
    ← WithZero.exp_zero]
  apply WithZero.exp_le_exp.mpr
  rw [RatFunc.intDegree_neg,
    RatFunc.intDegree_mul RatFunc.X_ne_zero hquotient,
    RatFunc.intDegree_X,
    RatFunc.intDegree_div hb_map hq_map,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  have hdegree : b.natDegree < q.natDegree :=
    (Polynomial.natDegree_lt_iff_degree_lt hb0).mpr (by
      simpa only [Polynomial.degree_eq_natDegree hq0] using hb)
  omega

private noncomputable def rationalInfinitySimpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    (GlobalPlace.rationalInfinity k).valuationRing :=
  ⟨-(RatFunc.X *
      (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) q)),
    rationalInfinitySimpleFractionCoefficient_mem q b hq hb⟩

private theorem coe_rationalInfinitySimpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    ((rationalInfinitySimpleFractionCoefficient q b hq hb :
      (GlobalPlace.rationalInfinity k).valuationRing) : RatFunc k) =
      -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) :=
  rfl

omit [Finite k] in
private theorem rationalInfinitySimpleFractionRemainder_degree_lt
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    let c := -b.coeff (q.natDegree - 1)
    let r := -(Polynomial.X * b) - q * Polynomial.C c
    r.degree < q.degree := by
  dsimp only
  by_cases hb0 : b = 0
  · subst b
    simpa using hb
  have hq0 : q ≠ 0 := hq.ne_zero
  have hdegree : b.natDegree < q.natDegree :=
    (Polynomial.natDegree_lt_iff_degree_lt hb0).mpr (by
      simpa only [Polynomial.degree_eq_natDegree hq0] using hb)
  have hsucc_le : b.natDegree + 1 ≤ q.natDegree := Nat.succ_le_of_lt hdegree
  rcases hsucc_le.eq_or_lt with hboundary | hstrict
  · have hindex : q.natDegree - 1 = b.natDegree := by omega
    have hc : -b.coeff (q.natDegree - 1) = -(b.leadingCoeff) := by
      rw [hindex, Polynomial.coeff_natDegree]
    have hp0 : -(Polynomial.X * b) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero Polynomial.X_ne_zero hb0)
    have hdegree_p : (-(Polynomial.X * b)).degree = q.degree := by
      rw [Polynomial.degree_neg, Polynomial.degree_eq_natDegree
        (mul_ne_zero Polynomial.X_ne_zero hb0),
        Polynomial.natDegree_X_mul hb0,
        Polynomial.degree_eq_natDegree hq0, hboundary]
    have hdegree_scaled :
        (q * Polynomial.C (-b.coeff (q.natDegree - 1))).degree = q.degree := by
      rw [Polynomial.degree_mul_C]
      rw [hc]
      exact neg_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hb0)
    have hleading :
        (-(Polynomial.X * b)).leadingCoeff =
          (q * Polynomial.C (-b.coeff (q.natDegree - 1))).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_X, one_mul, Polynomial.leadingCoeff_mul,
        hq.leadingCoeff, one_mul, Polynomial.leadingCoeff_C, hc]
    have hdrop := Polynomial.degree_sub_lt
      (hdegree_p.trans hdegree_scaled.symm) hp0 hleading
    simpa only [hdegree_p] using hdrop
  · have hindex : b.natDegree < q.natDegree - 1 := by omega
    have hcoeff : b.coeff (q.natDegree - 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hindex
    simp only [hcoeff, neg_zero, Polynomial.C_0, mul_zero, sub_zero,
      Polynomial.degree_neg]
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero Polynomial.X_ne_zero hb0),
      Polynomial.natDegree_X_mul hb0, Polynomial.degree_eq_natDegree hq0]
    exact WithBot.coe_lt_coe.mpr hstrict

private theorem rationalInfinity_order_inverseX :
    (GlobalPlace.rationalInfinity k).order (RatFunc.X : RatFunc k)⁻¹ = 1 := by
  rw [GlobalPlace.order_inv,
    RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
      k RatFunc.X RatFunc.X_ne_zero,
    RatFunc.intDegree_X]
  norm_num

/-- The actual local simple-pole representative of `(b / q) dX` at the
rational-function infinity place. -/
noncomputable def rationalInfinitySimpleFractionAtSimplePole
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleDifferentialLattice (GlobalPlace.rationalInfinity k) :=
  rationalInfinitySimpleFractionCoefficient q b hq hb •
    logarithmicDifferentialAtSimplePole (k := k) (F := RatFunc k)
      (GlobalPlace.rationalInfinity k) (RatFunc.X : RatFunc k)⁻¹
      (inv_ne_zero RatFunc.X_ne_zero)

/-- The infinity local representative has underlying differential
`(b / q) dX`. -/
theorem coe_rationalInfinitySimpleFractionAtSimplePole
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    ((rationalInfinitySimpleFractionAtSimplePole q b hq hb :
      simplePoleDifferentialLattice (GlobalPlace.rationalInfinity k)) :
        Differential k (RatFunc k)) =
        (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) q) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  have hDX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  change
    ((rationalInfinitySimpleFractionCoefficient q b hq hb :
      (GlobalPlace.rationalInfinity k).valuationRing) : RatFunc k) •
      logarithmicDifferential (k := k) (F := RatFunc k)
        (RatFunc.X : RatFunc k)⁻¹ = _
  rw [coe_rationalInfinitySimpleFractionCoefficient,
    logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    Derivation.leibniz_inv, hDX]
  simp only [smul_smul, smul_eq_mul]
  field_simp [RatFunc.X_ne_zero, RatFunc.algebraMap_ne_zero hq.ne_zero]

private theorem rationalInfinityResidue_simpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    let c := -b.coeff (q.natDegree - 1)
    (GlobalPlace.rationalInfinity k).residue
        (rationalInfinitySimpleFractionCoefficient q b hq hb) =
      GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k) c := by
  classical
  dsimp only
  let P := GlobalPlace.rationalInfinity k
  let c : k := -b.coeff (q.natDegree - 1)
  let r : k[X] := -(Polynomial.X * b) - q * Polynomial.C c
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq_map : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq0
  have hr_degree : r.degree < q.degree := by
    exact rationalInfinitySimpleFractionRemainder_degree_lt q b hq hb
  have hdiff :
      ((rationalInfinitySimpleFractionCoefficient q b hq hb :
        P.valuationRing) : RatFunc k) - algebraMap k (RatFunc k) c =
        algebraMap k[X] (RatFunc k) r /
          algebraMap k[X] (RatFunc k) q := by
    rw [coe_rationalInfinitySimpleFractionCoefficient]
    change -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) -
        algebraMap k[X] (RatFunc k) (Polynomial.C c) =
      algebraMap k[X] (RatFunc k)
          (-(Polynomial.X * b) - q * Polynomial.C c) /
        algebraMap k[X] (RatFunc k) q
    simp only [map_sub, map_neg, map_mul, RatFunc.algebraMap_X]
    field_simp [hq_map]
  let w : P.valuationRing :=
    rationalInfinitySimpleFractionCoefficient q b hq hb -
      GlobalPlace.constantsToValuationRing P c
  have hw : w ∈ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change P.valuation
      (((rationalInfinitySimpleFractionCoefficient q b hq hb :
        P.valuationRing) : RatFunc k) - algebraMap k (RatFunc k) c) < 1
    rw [hdiff]
    by_cases hr : r = 0
    · simp [hr]
    · have hr_map : algebraMap k[X] (RatFunc k) r ≠ 0 :=
        RatFunc.algebraMap_ne_zero hr
      have hquotient :
          algebraMap k[X] (RatFunc k) r /
              algebraMap k[X] (RatFunc k) q ≠ 0 :=
        div_ne_zero hr_map hq_map
      change RatFunc.inftyValuation k
        (algebraMap k[X] (RatFunc k) r /
          algebraMap k[X] (RatFunc k) q) < 1
      rw [RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation_of_nonzero (F := k) hquotient,
        ← WithZero.exp_zero]
      apply WithZero.exp_lt_exp.mpr
      rw [RatFunc.intDegree_div hr_map hq_map,
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
      have hr_natDegree : r.natDegree < q.natDegree :=
        (Polynomial.natDegree_lt_iff_degree_lt hr).mpr (by
          simpa only [Polynomial.degree_eq_natDegree hq0] using hr_degree)
      omega
  change P.residue (rationalInfinitySimpleFractionCoefficient q b hq hb) =
    P.residue (GlobalPlace.constantsToValuationRing P c)
  rw [← sub_eq_zero, ← map_sub]
  exact (P.residue_eq_zero_iff w).mpr hw

private theorem simplePoleResidue_rationalInfinitySimpleFraction
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb) =
      GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity k)
        (-b.coeff (q.natDegree - 1)) := by
  unfold rationalInfinitySimpleFractionAtSimplePole
  rw [simplePoleResidue_smul,
    simplePoleResidue_logarithmicDifferential,
    rationalInfinity_order_inverseX]
  simp only [Int.cast_one, mul_one]
  exact rationalInfinityResidue_simpleFractionCoefficient q b hq hb

/-- The traced normalized residue at infinity of `(b / q) dX` is the
negative next-to-leading coefficient of `b`. -/
theorem simplePoleTraceResidue_rationalInfinitySimpleFraction
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb :
          Differential k (RatFunc k))
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb).property =
      -b.coeff (q.natDegree - 1) := by
  let P := GlobalPlace.rationalInfinity k
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    GlobalPlace.residueField_finiteDimensional P
  change Algebra.trace k P.residueField
      (simplePoleResidue (k := k) (F := RatFunc k) P
        (rationalInfinitySimpleFractionAtSimplePole q b hq hb)) = _
  rw [simplePoleResidue_rationalInfinitySimpleFraction]
  change Algebra.trace k P.residueField
      (algebraMap k P.residueField (-b.coeff (q.natDegree - 1))) = _
  rw [Algebra.trace_algebraMap,
    ← GlobalPlace.residueDegree_eq_finrank P,
    GlobalPlace.rationalInfinity_residueDegree_eq_one]
  simp

end Differential
end QEC.Coding.AlgebraicGeometry

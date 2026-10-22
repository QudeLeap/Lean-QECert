/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Divisors.RationalBaseInfinityCancellation
import QEC.Coding.AlgebraicGeometry.Places.RationalPlace
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-!
# The residue field at rational-function infinity

Every rational function regular at infinity reduces to a constant.  The
constant is zero when the numerator degree is smaller than the denominator
degree, and otherwise is their leading-coefficient ratio.  This proves that
the actual constant-reduction map onto the residue field at infinity is
surjective, hence that the normalized infinity place has residue degree one.

No Laurent-series model, global residue theorem, extension-field transport,
duality, genus, or Riemann--Roch theorem is asserted here.
-/

open scoped Polynomial RatFunc WithZero

namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace

variable {k : Type*} [Field k] [Finite k]

private theorem rationalInfinity_valuation_lt_one_of_intDegree_neg
    (f : RatFunc k) (hf : f ≠ 0) (hdegree : f.intDegree < 0) :
    (rationalInfinity k).valuation f < 1 := by
  classical
  change RatFunc.inftyValuation k f < 1
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero (F := k) hf,
    ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr hdegree

private theorem rationalInfinity_residue_eq_constant
    (z : (rationalInfinity k).valuationRing) :
    ∃ c : k,
      (rationalInfinity k).residue z =
        constantsToResidue (rationalInfinity k) c := by
  let P := rationalInfinity k
  let f : RatFunc k := z
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    have hz : z = 0 := Subtype.ext hf
    subst z
    simp [constantsToResidue]
  have horder : 0 ≤ P.order f :=
    (P.regularAt_iff_order_nonnegative hf).mp z.property
  rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_denomDegree_sub_numDegree
    k f hf] at horder
  have hdegree_le : f.num.natDegree ≤ f.denom.natDegree := by omega
  rcases hdegree_le.eq_or_lt with hdegree_eq | hdegree_lt
  · let c : k := f.num.leadingCoeff / f.denom.leadingCoeff
    have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
    have hdenom : f.denom ≠ 0 := RatFunc.denom_ne_zero f
    have hnum_lc : f.num.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hnum
    have hdenom_lc : f.denom.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hdenom
    have hc : c ≠ 0 := div_ne_zero hnum_lc hdenom_lc
    let r : k[X] := f.num - f.denom * Polynomial.C c
    have hdegree_polynomial : f.num.degree = f.denom.degree := by
      rw [Polynomial.degree_eq_natDegree hnum,
        Polynomial.degree_eq_natDegree hdenom, hdegree_eq]
    have hscaled_degree :
        (f.denom * Polynomial.C c).degree = f.num.degree := by
      rw [Polynomial.degree_mul_C hc, hdegree_polynomial]
    have hscaled_leadingCoeff :
        f.num.leadingCoeff =
          (f.denom * Polynomial.C c).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      rw [show c = f.num.leadingCoeff / f.denom.leadingCoeff from rfl]
      rw [mul_comm, div_mul_cancel₀ _ hdenom_lc]
    have hr_degree : r.degree < f.denom.degree := by
      have hdrop := Polynomial.degree_sub_lt hscaled_degree.symm hnum
        hscaled_leadingCoeff
      simpa only [r, hdegree_polynomial] using hdrop
    have hdiff :
        f - algebraMap k (RatFunc k) c =
          algebraMap k[X] (RatFunc k) r /
            algebraMap k[X] (RatFunc k) f.denom := by
      nth_rw 1 [← RatFunc.num_div_denom f]
      change algebraMap k[X] (RatFunc k) f.num /
          algebraMap k[X] (RatFunc k) f.denom -
            algebraMap k[X] (RatFunc k) (Polynomial.C c) = _
      rw [div_sub' (RatFunc.algebraMap_ne_zero hdenom), ← map_mul, ← map_sub]
    let w : P.valuationRing := z - constantsToValuationRing P c
    have hw : w ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      rw [Valuation.mem_maximalIdeal_iff]
      change P.valuation (f - algebraMap k (RatFunc k) c) < 1
      rw [hdiff]
      by_cases hr : r = 0
      · simp [hr]
      · have hr_map : algebraMap k[X] (RatFunc k) r ≠ 0 :=
          RatFunc.algebraMap_ne_zero hr
        have hdenom_map : algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
          RatFunc.algebraMap_ne_zero hdenom
        have hquotient :
            algebraMap k[X] (RatFunc k) r /
                algebraMap k[X] (RatFunc k) f.denom ≠ 0 :=
          div_ne_zero hr_map hdenom_map
        apply rationalInfinity_valuation_lt_one_of_intDegree_neg
          (algebraMap k[X] (RatFunc k) r /
            algebraMap k[X] (RatFunc k) f.denom) hquotient
        rw [RatFunc.intDegree_div hr_map hdenom_map,
          RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
        have hr_natDegree : r.natDegree < f.denom.natDegree :=
          (Polynomial.natDegree_lt_iff_degree_lt hr).mpr (by
            simpa only [Polynomial.degree_eq_natDegree hdenom] using hr_degree)
        omega
    refine ⟨c, ?_⟩
    change P.residue z = P.residue (constantsToValuationRing P c)
    rw [← sub_eq_zero, ← map_sub]
    exact (P.residue_eq_zero_iff w).mpr hw
  · refine ⟨0, ?_⟩
    have hdegree_neg : f.intDegree < 0 := by
      rw [RatFunc.intDegree]
      omega
    have hzmax : z ∈ IsLocalRing.maximalIdeal P.valuationRing := by
      rw [Valuation.mem_maximalIdeal_iff]
      exact rationalInfinity_valuation_lt_one_of_intDegree_neg f hf hdegree_neg
    rw [(P.residue_eq_zero_iff z).mpr hzmax]
    simp [constantsToResidue]

/-- Every residue class at the rational-function infinity place is the
reduction of a constant. -/
theorem rationalInfinity_constantsToResidue_surjective :
    Function.Surjective (constantsToResidue (rationalInfinity k)) := by
  intro y
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := rationalInfinity_residue_eq_constant z
  exact ⟨c, hc.symm⟩

/-- The normalized rational-function infinity place has residue degree one. -/
theorem rationalInfinity_residueDegree_eq_one :
    residueDegree (k := k) (F := RatFunc k) (rationalInfinity k) = 1 := by
  let P := rationalInfinity k
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional P
  rw [residueDegree_eq_finrank]
  apply Module.finrank_of_bijective_algebraMap
  constructor
  · exact (algebraMap k P.residueField).injective
  · simpa only [P, residueAlgebra, RingHom.algebraMap_toAlgebra] using
      (rationalInfinity_constantsToResidue_surjective (k := k))

end GlobalPlace
end QEC.Coding.AlgebraicGeometry

import QEC.Coding.AlgebraicGeometry.Towers.ResidualPolynomial

import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral auxiliary coordinates above rational places

At any rational place where the preceding coordinate is regular, the
Garcia--Stichtenoth auxiliary coordinate is integral.  Reduction modulo an
arbitrary upper prime is one of the sixteen concrete `F256` roots of the
residual Artin--Schreier polynomial.  No upper prime is selected here and no
place count, divisor, genus, or asymptotic statement is packaged.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem aeval_stepAuxiliaryPolynomial
    {E : Type*} [Field E] [Algebra F256 E] (a : F256) (y : E) :
    Polynomial.aeval y (stepAuxiliaryPolynomial a) =
      y ^ 16 + (y - algebraMap F256 E (a ^ 17)) := by
  rw [stepAuxiliaryPolynomial, map_add, map_pow, aeval_X, map_sub, aeval_C]
  rw [Polynomial.aeval_X]

/-- The integral closure attached to a rational base place in one concrete
step extension. -/
abbrev SplitIntegralClosure
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  integralClosure Q.place.valuationRing (StepField P x hx)

instance splitFieldValuationRingScalarTower
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsScalarTower Q.place.valuationRing K (StepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance splitIntegralClosureIsTorsionFree
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.IsTorsionFree Q.place.valuationRing
      (SplitIntegralClosure Q P x hx) := by
  letI : Module.IsTorsionFree Q.place.valuationRing (StepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      Q.place.valuationRing K (StepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    Q.place.valuationRing (StepField P x hx)

noncomputable instance splitIntegralClosureFinite
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.Finite Q.place.valuationRing
      (SplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite Q.place.valuationRing K
    (StepField P x hx) (SplitIntegralClosure Q P x hx)

noncomputable instance splitIntegralClosureIsFractionRing
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsFractionRing (SplitIntegralClosure Q P x hx) (StepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K (StepField P x hx)

noncomputable instance splitIntegralClosureIsDedekindDomain
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsDedekindDomain (SplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain Q.place.valuationRing K
    (StepField P x hx)

private noncomputable def splitBaseCoordinate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing :=
  ⟨x, (GlobalPlace.mem_valuationRing_iff Q.place x).mpr hregular⟩

private theorem coe_splitBaseCoordinate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (splitBaseCoordinate Q x hregular : K) = x :=
  rfl

private theorem algebraMap_splitBaseCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    algebraMap Q.place.valuationRing (StepField P x hx)
        (splitBaseCoordinate Q x hregular) =
      stepFieldEmbedding P x hx x :=
  rfl

private noncomputable def splitAuxiliaryIntegralPolynomial
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing[X] :=
  X ^ 16 + (X - C ((splitBaseCoordinate Q x hregular) ^ 17))

private theorem splitAuxiliaryIntegralPolynomial_monic
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (splitAuxiliaryIntegralPolynomial Q x hregular).Monic := by
  rw [splitAuxiliaryIntegralPolynomial]
  apply Monic.add_of_left (monic_X_pow 16)
  calc
    ((X : Q.place.valuationRing[X]) -
        C ((splitBaseCoordinate Q x hregular) ^ 17)).degree ≤
        max (X : Q.place.valuationRing[X]).degree
          (C ((splitBaseCoordinate Q x hregular) ^ 17)).degree :=
      degree_sub_le _ _
    _ ≤ (1 : WithBot ℕ) :=
      max_le (by simp) (degree_C_le.trans (by norm_num))
    _ < ((X : Q.place.valuationRing[X]) ^ 16).degree := by
      rw [degree_X_pow]
      norm_num

/-- The auxiliary coordinate, as an actual element of the integral closure at
the supplied rational base place. -/
noncomputable def splitIntegralAuxiliaryCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    SplitIntegralClosure Q P x hx := by
  refine ⟨stepAuxiliaryCoordinate P x hx, ?_⟩
  refine ⟨splitAuxiliaryIntegralPolynomial Q x hregular,
    splitAuxiliaryIntegralPolynomial_monic Q x hregular, ?_⟩
  rw [splitAuxiliaryIntegralPolynomial]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_sub, eval₂_C]
  change stepAuxiliaryCoordinate P x hx ^ 16 +
      (stepAuxiliaryCoordinate P x hx -
        algebraMap Q.place.valuationRing (StepField P x hx)
          ((splitBaseCoordinate Q x hregular) ^ 17)) = 0
  rw [map_pow, algebraMap_splitBaseCoordinate]
  linear_combination stepAuxiliaryCoordinate_artinSchreier P x hx

@[simp]
theorem coe_splitIntegralAuxiliaryCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    (splitIntegralAuxiliaryCoordinate Q P x hx hregular :
        StepField P x hx) =
      stepAuxiliaryCoordinate P x hx :=
  rfl

/-- The integral auxiliary coordinate satisfies the source recursion over the
base valuation ring. -/
theorem splitIntegralAuxiliaryCoordinate_equation
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    splitIntegralAuxiliaryCoordinate Q P x hx hregular ^ 16 +
        splitIntegralAuxiliaryCoordinate Q P x hx hregular =
      algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
        ((splitBaseCoordinate Q x hregular) ^ 17) := by
  apply Subtype.ext
  change stepAuxiliaryCoordinate P x hx ^ 16 +
      stepAuxiliaryCoordinate P x hx =
        algebraMap Q.place.valuationRing (StepField P x hx)
          ((splitBaseCoordinate Q x hregular) ^ 17)
  rw [map_pow, algebraMap_splitBaseCoordinate]
  exact stepAuxiliaryCoordinate_artinSchreier P x hx

private theorem quotient_base_eq_constant
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (R : Ideal (SplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    (y : Q.place.valuationRing) :
    Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx) y) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y))) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have hresidue : Q.place.residue y =
      Q.place.constantsToResidue (Q.evaluate y) := by
    calc
      Q.place.residue y =
          Q.constantsEquiv (Q.constantsEquiv.symm (Q.place.residue y)) := by
        rw [Q.constantsEquiv.apply_symm_apply]
      _ = Q.place.constantsToResidue (Q.evaluate y) := by
        rw [Q.constantsEquiv_apply]
        rfl
  have hbase : y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
      IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [← GlobalPlace.residue_eq_zero_iff, map_sub]
    change Q.place.residue y - Q.place.constantsToResidue (Q.evaluate y) = 0
    rw [hresidue, sub_self]
  rw [← map_sub]
  change y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
    Ideal.under Q.place.valuationRing R
  rw [← (inferInstance : R.LiesOver
    (IsLocalRing.maximalIdeal Q.place.valuationRing)).over]
  exact hbase

/-- Modulo every upper prime, the integral auxiliary coordinate equals one of
the sixteen concrete constant roots of the residual polynomial. -/
theorem exists_splitUpperIdeal_auxiliary_residue_root
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (R : Ideal (SplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)] :
    ∃ b ∈ f256ArtinSchreierRoots (Q.evaluateRegular x hregular),
      splitIntegralAuxiliaryCoordinate Q P x hx hregular -
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place b) ∈ R := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let E := S ⧸ R
  let xO : O := splitBaseCoordinate Q x hregular
  let zS : S := splitIntegralAuxiliaryCoordinate Q P x hx hregular
  letI : Field E := Ideal.Quotient.field R
  let constantsToE : F256 →+* E :=
    (Ideal.Quotient.mk R).comp
      ((algebraMap O S).comp (GlobalPlace.constantsToValuationRing Q.place))
  letI : Algebra F256 E := constantsToE.toAlgebra
  have hbase := quotient_base_eq_constant Q P x hx R xO
  have hbase' :
      Ideal.Quotient.mk R (algebraMap O S xO) =
        algebraMap F256 E (Q.evaluate xO) := by
    change Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SplitIntegralClosure Q P x hx) xO) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (Q.evaluate xO)))
    exact hbase
  have hbase17 :
      Ideal.Quotient.mk R (algebraMap O S (xO ^ 17)) =
        algebraMap F256 E ((Q.evaluate xO) ^ 17) := by
    change Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SplitIntegralClosure Q P x hx) (xO ^ 17)) =
      algebraMap F256 E ((Q.evaluate xO) ^ 17)
    rw [map_pow, map_pow, hbase', map_pow]
  have hequation := congrArg (Ideal.Quotient.mk R)
    (splitIntegralAuxiliaryCoordinate_equation Q P x hx hregular)
  have hroot : Polynomial.aeval (Ideal.Quotient.mk R zS)
      (stepAuxiliaryPolynomial (Q.evaluate xO)) = 0 := by
    rw [aeval_stepAuxiliaryPolynomial]
    change (Ideal.Quotient.mk R zS) ^ 16 +
      ((Ideal.Quotient.mk R zS) -
        algebraMap F256 E ((Q.evaluate xO) ^ 17)) = 0
    change Ideal.Quotient.mk R
        (zS ^ 16 + zS) =
      Ideal.Quotient.mk R (algebraMap O S (xO ^ 17)) at hequation
    have hequation' :
        (Ideal.Quotient.mk R zS) ^ 16 + Ideal.Quotient.mk R zS =
          algebraMap F256 E ((Q.evaluate xO) ^ 17) := by
      calc
        (Ideal.Quotient.mk R zS) ^ 16 + Ideal.Quotient.mk R zS =
            Ideal.Quotient.mk R (zS ^ 16) + Ideal.Quotient.mk R zS := by
          rw [← (Ideal.Quotient.mk R).map_pow]
        _ = Ideal.Quotient.mk R (zS ^ 16 + zS) :=
          ((Ideal.Quotient.mk R).map_add _ _).symm
        _ = Ideal.Quotient.mk R (algebraMap O S (xO ^ 17)) := hequation
        _ = algebraMap F256 E ((Q.evaluate xO) ^ 17) := hbase17
    linear_combination hequation'
  obtain ⟨b, hb, hz⟩ :=
    exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
      (Q.evaluate xO) (Ideal.Quotient.mk R zS) hroot
  refine ⟨b, ?_, ?_⟩
  · simpa only [xO, splitBaseCoordinate, RationalPlace.evaluateRegular] using hb
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk R zS - algebraMap F256 E b = 0
    rw [hz, sub_self]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

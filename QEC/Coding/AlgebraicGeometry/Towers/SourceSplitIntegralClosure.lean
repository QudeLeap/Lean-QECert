import QEC.Coding.AlgebraicGeometry.Towers.SourceSplitAlgebra

import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral source coordinates above selected rational places

At a rational place whose source coordinate reduces to one of the 240
selected constants, the denominator in the literal Garcia--Stichtenoth
recursion is a unit.  Consequently the recursion right-hand side is regular,
the successor coordinate is integral, and its residue at every upper prime is
one of the sixteen constructed `F256` roots.  No upper prime, place count,
divisor, genus, or asymptotic conclusion is packaged here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

private theorem aeval_sourceStepResidualPolynomial
    {E : Type*} [Field E] [Algebra F256 E]
    (a : GaloisBaseSplitPoint) (y : E) :
    Polynomial.aeval y (sourceStepResidualPolynomial a) =
      y ^ 16 + (y - algebraMap F256 E (sourceStepRhs (a : F256))) := by
  rw [sourceStepResidualPolynomial, map_add, map_pow,
    Polynomial.aeval_X, map_sub, Polynomial.aeval_C]
  rw [Polynomial.aeval_X]

/-- The integral closure attached to a selected rational base place in one
literal source-recursion step. -/
abbrev SourceSplitIntegralClosure
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :=
  integralClosure Q.place.valuationRing (SourceStepField P x hx)

instance sourceSplitFieldValuationRingScalarTower
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsScalarTower Q.place.valuationRing K (SourceStepField P x hx) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance sourceSplitIntegralClosureIsTorsionFree
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.IsTorsionFree Q.place.valuationRing
      (SourceSplitIntegralClosure Q P x hx) := by
  letI : Module.IsTorsionFree Q.place.valuationRing
      (SourceStepField P x hx) :=
    Module.IsTorsionFree.trans_faithfulSMul
      Q.place.valuationRing K (SourceStepField P x hx)
  exact IsIntegralClosure.isTorsionFree
    Q.place.valuationRing (SourceStepField P x hx)

noncomputable instance sourceSplitIntegralClosureFinite
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    Module.Finite Q.place.valuationRing
      (SourceSplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite Q.place.valuationRing K
    (SourceStepField P x hx) (SourceSplitIntegralClosure Q P x hx)

noncomputable instance sourceSplitIntegralClosureIsFractionRing
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsFractionRing (SourceSplitIntegralClosure Q P x hx)
      (SourceStepField P x hx) :=
  integralClosure.isFractionRing_of_finite_extension K (SourceStepField P x hx)

noncomputable instance sourceSplitIntegralClosureIsDedekindDomain
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) :
    IsDedekindDomain (SourceSplitIntegralClosure Q P x hx) := by
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain Q.place.valuationRing K
    (SourceStepField P x hx)

private noncomputable def sourceSplitBaseCoordinate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing :=
  ⟨x, (GlobalPlace.mem_valuationRing_iff Q.place x).mpr hregular⟩

private noncomputable def sourceSplitBaseDenominator
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.place.valuationRing :=
  sourceSplitBaseCoordinate Q x hregular ^ 15 + 1

private theorem sourceSplitBaseDenominator_evaluate
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Q.evaluate (sourceSplitBaseDenominator Q x hregular) =
      Q.evaluateRegular x hregular ^ 15 + 1 := by
  simp only [sourceSplitBaseDenominator, map_add, map_pow, map_one]
  rfl

private theorem sourceSplitBaseDenominator_evaluate_ne_zero
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.evaluate (sourceSplitBaseDenominator Q x hregular) ≠ 0 := by
  rw [sourceSplitBaseDenominator_evaluate]
  intro hzero
  apply hsplit
  rw [galoisBaseWValue_eq]
  calc
    Q.evaluateRegular x hregular ^ 16 + Q.evaluateRegular x hregular =
        Q.evaluateRegular x hregular *
          (Q.evaluateRegular x hregular ^ 15 + 1) := by ring
    _ = 0 := by rw [hzero, mul_zero]

private theorem sourceSplitBaseDenominator_inv_mem
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    ((sourceSplitBaseDenominator Q x hregular : K)⁻¹) ∈
      Q.place.valuationRing := by
  let d := sourceSplitBaseDenominator Q x hregular
  have hunit : IsUnit d := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmaximal
    exact sourceSplitBaseDenominator_evaluate_ne_zero Q x hregular hsplit
      ((Q.evaluate_eq_zero_iff d).2 hmaximal)
  change ((d : K)⁻¹) ∈ Q.place.valuationRing
  rw [← hunit.unit_spec]
  change (Q.place.valuationRing.subtype
    (↑hunit.unit : Q.place.valuationRing))⁻¹ ∈ Q.place.valuationRing
  rw [← map_units_inv Q.place.valuationRing.subtype hunit.unit]
  exact (↑(hunit.unit⁻¹) : Q.place.valuationRing).property

/-- The source recursion right-hand side is regular at every selected
rational base place. -/
theorem sourceStepRhs_regularAt_of_splitValue
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    GlobalPlace.RegularAt Q.place (sourceStepRhs x) := by
  rw [GlobalPlace.regularAt_iff_mem_valuationRing, sourceStepRhs,
    div_eq_mul_inv]
  let xO := sourceSplitBaseCoordinate Q x hregular
  have hxpow : x ^ 16 ∈ Q.place.valuationRing := by
    exact (xO ^ 16).property
  exact Q.place.valuationRing.mul_mem _ _ hxpow
    (sourceSplitBaseDenominator_inv_mem Q x hregular hsplit)

private noncomputable def sourceSplitBaseRhs
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.place.valuationRing :=
  ⟨sourceStepRhs x,
    (GlobalPlace.mem_valuationRing_iff Q.place _).mpr
      (sourceStepRhs_regularAt_of_splitValue Q x hregular hsplit)⟩

/-- Rational-place evaluation commutes with the regular source recursion
right-hand side. -/
theorem sourceStepRhs_evaluateRegular
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.evaluateRegular (sourceStepRhs x)
        (sourceStepRhs_regularAt_of_splitValue Q x hregular hsplit) =
      sourceStepRhs (Q.evaluateRegular x hregular) := by
  let xO := sourceSplitBaseCoordinate Q x hregular
  let dO := sourceSplitBaseDenominator Q x hregular
  let rO := sourceSplitBaseRhs Q x hregular hsplit
  have hdenvalue : Q.evaluate xO ^ 15 + 1 ≠ 0 := by
    have hport := sourceSplitBaseDenominator_evaluate_ne_zero Q x hregular hsplit
    simp only [xO, dO, sourceSplitBaseDenominator_evaluate] at hport ⊢
    exact hport
  have hdenK : x ^ 15 + 1 ≠ 0 := by
    intro hzero
    have hdzero : dO = 0 := by
      apply Subtype.ext
      exact hzero
    exact sourceSplitBaseDenominator_evaluate_ne_zero Q x hregular hsplit
      (by
        change Q.evaluate dO = 0
        rw [hdzero, map_zero])
  have hproduct : rO * dO = xO ^ 16 := by
    apply Subtype.ext
    change sourceStepRhs x * (x ^ 15 + 1) = x ^ 16
    rw [sourceStepRhs]
    exact div_mul_cancel₀ _ hdenK
  have hevaluate := congrArg Q.evaluate hproduct
  rw [map_mul, map_pow] at hevaluate
  change Q.evaluate rO = sourceStepRhs (Q.evaluate xO)
  rw [sourceStepRhs]
  apply (eq_div_iff hdenvalue).2
  simp only [dO, sourceSplitBaseDenominator_evaluate] at hevaluate ⊢
  exact hevaluate

private noncomputable def sourceSplitIntegralPolynomial
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Q.place.valuationRing[X] :=
  X ^ 16 + (X - C (sourceSplitBaseRhs Q x hregular hsplit))

private theorem sourceSplitIntegralPolynomial_monic
    (Q : RationalPlace F256 K) (x : K)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (sourceSplitIntegralPolynomial Q x hregular hsplit).Monic := by
  rw [sourceSplitIntegralPolynomial]
  apply Monic.add_of_left (monic_X_pow 16)
  calc
    ((X : Q.place.valuationRing[X]) -
        C (sourceSplitBaseRhs Q x hregular hsplit)).degree ≤
        max (X : Q.place.valuationRing[X]).degree
          (C (sourceSplitBaseRhs Q x hregular hsplit)).degree :=
      degree_sub_le _ _
    _ ≤ (1 : WithBot ℕ) :=
      max_le (by simp) (degree_C_le.trans (by norm_num))
    _ < ((X : Q.place.valuationRing[X]) ^ 16).degree := by
      rw [degree_X_pow]
      norm_num

/-- The source recursion coordinate as an actual element of the integral
closure at the selected rational base place. -/
noncomputable def sourceSplitIntegralCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    SourceSplitIntegralClosure Q P x hx := by
  refine ⟨sourceStepCoordinate P x hx, ?_⟩
  refine ⟨sourceSplitIntegralPolynomial Q x hregular hsplit,
    sourceSplitIntegralPolynomial_monic Q x hregular hsplit, ?_⟩
  rw [sourceSplitIntegralPolynomial]
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_sub, eval₂_C]
  change sourceStepCoordinate P x hx ^ 16 +
      (sourceStepCoordinate P x hx -
        sourceStepEmbedding P x hx (sourceStepRhs x)) = 0
  linear_combination sourceStepCoordinate_equation P x hx

@[simp]
theorem coe_sourceSplitIntegralCoordinate
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (sourceSplitIntegralCoordinate Q P x hx hregular hsplit :
        SourceStepField P x hx) = sourceStepCoordinate P x hx :=
  rfl

/-- The integral source coordinate satisfies the literal recursion over the
base valuation ring. -/
theorem sourceSplitIntegralCoordinate_equation
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    sourceSplitIntegralCoordinate Q P x hx hregular hsplit ^ 16 +
        sourceSplitIntegralCoordinate Q P x hx hregular hsplit =
      algebraMap Q.place.valuationRing
        (SourceSplitIntegralClosure Q P x hx)
        (sourceSplitBaseRhs Q x hregular hsplit) := by
  apply Subtype.ext
  change sourceStepCoordinate P x hx ^ 16 +
      sourceStepCoordinate P x hx =
        sourceStepEmbedding P x hx (sourceStepRhs x)
  exact sourceStepCoordinate_equation P x hx

private theorem sourceSplitQuotient_base_eq_constant
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (R : Ideal (SourceSplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    (y : Q.place.valuationRing) :
    Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx) y) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
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
  have hbase :
      y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
        IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [← GlobalPlace.residue_eq_zero_iff, map_sub]
    change Q.place.residue y -
        Q.place.constantsToResidue (Q.evaluate y) = 0
    rw [hresidue, sub_self]
  rw [← map_sub]
  change y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
    Ideal.under Q.place.valuationRing R
  rw [← (inferInstance : R.LiesOver
    (IsLocalRing.maximalIdeal Q.place.valuationRing)).over]
  exact hbase

/-- Modulo every upper prime, the integral source coordinate is one of the
sixteen constructed constant roots. -/
theorem exists_sourceSplitUpperIdeal_coordinate_residue_root
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (R : Ideal (SourceSplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)] :
    ∃ b ∈ sourceStepArtinSchreierRoots
        (⟨Q.evaluateRegular x hregular, hsplit⟩ : GaloisBaseSplitPoint),
      sourceSplitIntegralCoordinate Q P x hx hregular hsplit -
          algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place b) ∈ R := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let E := S ⧸ R
  let a : GaloisBaseSplitPoint :=
    ⟨Q.evaluateRegular x hregular, hsplit⟩
  let yS := sourceSplitIntegralCoordinate Q P x hx hregular hsplit
  let rO := sourceSplitBaseRhs Q x hregular hsplit
  letI : Field E := Ideal.Quotient.field R
  let constantsToE : F256 →+* E :=
    (Ideal.Quotient.mk R).comp
      ((algebraMap O S).comp (GlobalPlace.constantsToValuationRing Q.place))
  letI : Algebra F256 E := constantsToE.toAlgebra
  have hbase := sourceSplitQuotient_base_eq_constant Q P x hx R rO
  have hbase' :
      Ideal.Quotient.mk R (algebraMap O S rO) =
        algebraMap F256 E (sourceStepRhs (a : F256)) := by
    change Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx) rO) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place
            (sourceStepRhs (a : F256))))
    rw [← sourceStepRhs_evaluateRegular Q x hregular hsplit]
    exact hbase
  have hequation := congrArg (Ideal.Quotient.mk R)
    (sourceSplitIntegralCoordinate_equation
      Q P x hx hregular hsplit)
  have hroot : Polynomial.aeval (Ideal.Quotient.mk R yS)
      (sourceStepResidualPolynomial a) = 0 := by
    rw [aeval_sourceStepResidualPolynomial]
    change (Ideal.Quotient.mk R yS) ^ 16 +
      ((Ideal.Quotient.mk R yS) -
        algebraMap F256 E (sourceStepRhs (a : F256))) = 0
    change Ideal.Quotient.mk R (yS ^ 16 + yS) =
      Ideal.Quotient.mk R (algebraMap O S rO) at hequation
    have hequation' :
        (Ideal.Quotient.mk R yS) ^ 16 + Ideal.Quotient.mk R yS =
          algebraMap F256 E (sourceStepRhs (a : F256)) := by
      calc
        (Ideal.Quotient.mk R yS) ^ 16 + Ideal.Quotient.mk R yS =
            Ideal.Quotient.mk R (yS ^ 16) + Ideal.Quotient.mk R yS := by
          rw [← (Ideal.Quotient.mk R).map_pow]
        _ = Ideal.Quotient.mk R (yS ^ 16 + yS) :=
          ((Ideal.Quotient.mk R).map_add _ _).symm
        _ = Ideal.Quotient.mk R (algebraMap O S rO) := hequation
        _ = algebraMap F256 E (sourceStepRhs (a : F256)) := hbase'
    linear_combination hequation'
  obtain ⟨b, hb, hy⟩ :=
    exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
      a (Ideal.Quotient.mk R yS) hroot
  refine ⟨b, ?_, ?_⟩
  · exact hb
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk R yS - algebraMap F256 E b = 0
    rw [hy, sub_self]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

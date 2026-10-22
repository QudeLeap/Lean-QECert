import QEC.Coding.AlgebraicGeometry.Towers.BasePlaces
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicPolynomialLogarithmicResidue

import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The zero base place in the F256 Garcia--Stichtenoth tower

This file constructs the actual finite rational-function place cut out by
`X`.  It is the base of the common-zero path used later to build the
ramification divisors in the Garcia--Stichtenoth tower.  No upper place,
ramification divisor, genus, or canonical-divisor conclusion is stored here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private noncomputable def zeroBaseHeightOne :
    IsDedekindDomain.HeightOneSpectrum F256[X] := by
  have hprime : Prime (Polynomial.X : F256[X]) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp Polynomial.irreducible_X
  have hspanPrime :
      (Ideal.span ({Polynomial.X} : Set F256[X])).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr hprime
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr Polynomial.X_ne_zero)
      hspanPrime)

private theorem zeroBaseHeightOne_asIdeal :
    zeroBaseHeightOne.asIdeal =
      Ideal.span ({Polynomial.X} : Set F256[X]) := by
  rfl

private theorem zeroBaseRationalAdicPolynomial :
    GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne =
      (Polynomial.X : F256[X]) := by
  apply Polynomial.eq_of_monic_of_associated
    (GlobalPlace.rationalAdicPolynomial_monic zeroBaseHeightOne)
    Polynomial.monic_X
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← GlobalPlace.rationalAdic_asIdeal_eq_span]
  exact zeroBaseHeightOne_asIdeal

private theorem zeroBaseAdjoinRootIdeal_eq :
    Ideal.span
        ({GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne} : Set F256[X]) =
      Ideal.span ({Polynomial.X - Polynomial.C 0} : Set F256[X]) := by
  rw [zeroBaseRationalAdicPolynomial]
  simp

private noncomputable def zeroBaseAdjoinRootEquiv :
    AdjoinRoot (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne) ≃ₐ[F256]
      F256 :=
  (Ideal.quotientEquivAlgOfEq F256 zeroBaseAdjoinRootIdeal_eq).trans
    (Polynomial.quotientSpanXSubCAlgEquiv 0)

private theorem zeroBaseAdjoinRootEquiv_symm_apply (c : F256) :
    zeroBaseAdjoinRootEquiv.symm c =
      algebraMap F256
        (AdjoinRoot (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)) c := by
  apply zeroBaseAdjoinRootEquiv.injective
  rw [zeroBaseAdjoinRootEquiv.apply_symm_apply,
    zeroBaseAdjoinRootEquiv.commutes]
  simp

private noncomputable def zeroBaseResidueEquiv :
    F256 ≃+* GlobalPlace.residueField
      (GlobalPlace.rationalAdic zeroBaseHeightOne) :=
  zeroBaseAdjoinRootEquiv.symm.toRingEquiv.trans
    (GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne)

private theorem zeroBaseRationalAdicResidueEquiv_algebraMap (c : F256) :
    GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne
        (algebraMap F256
          (AdjoinRoot (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)) c) =
      GlobalPlace.constantsToResidue
        (GlobalPlace.rationalAdic zeroBaseHeightOne) c := by
  change (GlobalPlace.rationalAdic zeroBaseHeightOne).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        zeroBaseHeightOne (Polynomial.C c)) =
    (GlobalPlace.rationalAdic zeroBaseHeightOne).residue
      (GlobalPlace.constantsToValuationRing
        (GlobalPlace.rationalAdic zeroBaseHeightOne) c)
  apply congrArg (GlobalPlace.rationalAdic zeroBaseHeightOne).residue
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]

private theorem zeroBaseResidueEquiv_apply (c : F256) :
    zeroBaseResidueEquiv c =
      GlobalPlace.constantsToResidue
        (GlobalPlace.rationalAdic zeroBaseHeightOne) c := by
  change GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne
      (zeroBaseAdjoinRootEquiv.symm c) = _
  rw [zeroBaseAdjoinRootEquiv_symm_apply]
  exact zeroBaseRationalAdicResidueEquiv_algebraMap c

/-- The actual rational place of `F256(X)` cut out by `X`. -/
noncomputable def zeroBaseRationalPlace :
    RationalPlace F256 (RatFunc F256) where
  place := GlobalPlace.rationalAdic zeroBaseHeightOne
  constantsEquiv := zeroBaseResidueEquiv
  constantsEquiv_apply := zeroBaseResidueEquiv_apply

/-- The coordinate `X` is regular at the zero base place. -/
theorem zeroBaseRationalPlace_X_regular :
    GlobalPlace.RegularAt zeroBaseRationalPlace.place RatFunc.X := by
  change GlobalPlace.RegularAt
    (GlobalPlace.rationalAdic zeroBaseHeightOne) RatFunc.X
  rw [GlobalPlace.regularAt_iff_mem_valuationRing]
  simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    RatFunc.algebraMap_X] using
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        zeroBaseHeightOne Polynomial.X).property

/-- Residue evaluation at the zero base place sends `X` to zero. -/
theorem zeroBaseRationalPlace_evaluate_X :
    zeroBaseRationalPlace.evaluateRegular RatFunc.X
        zeroBaseRationalPlace_X_regular = 0 := by
  have hxmem : RatFunc.X ∈
      (GlobalPlace.rationalAdic zeroBaseHeightOne).valuationRing := by
    simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X] using
        (GlobalPlace.rationalAdicPolynomialToValuationRing
          zeroBaseHeightOne Polynomial.X).property
  change zeroBaseResidueEquiv.symm
      ((GlobalPlace.rationalAdic zeroBaseHeightOne).residue
        ⟨RatFunc.X, hxmem⟩) = 0
  apply zeroBaseResidueEquiv.injective
  rw [zeroBaseResidueEquiv.apply_symm_apply, map_zero]
  let xO := GlobalPlace.rationalAdicPolynomialToValuationRing
    zeroBaseHeightOne Polynomial.X
  have hinput :
      (⟨RatFunc.X, hxmem⟩ :
        (GlobalPlace.rationalAdic zeroBaseHeightOne).valuationRing) = xO := by
    apply Subtype.ext
    simp only [xO, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  rw [hinput]
  have hmk :
      AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)
          Polynomial.X = 0 := by
    rw [AdjoinRoot.mk_eq_zero, zeroBaseRationalAdicPolynomial]
  calc
    (GlobalPlace.rationalAdic zeroBaseHeightOne).residue xO =
        GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne
          (AdjoinRoot.mk
            (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)
            Polynomial.X) := by
          exact (GlobalPlace.rationalAdicResidueEquiv_mk
            zeroBaseHeightOne Polynomial.X).symm
    _ = 0 := by rw [hmk, map_zero]

/-- The base coordinate has a simple zero at the zero base place. -/
theorem zeroBaseRationalPlace_order_X :
    zeroBaseRationalPlace.place.order RatFunc.X = 1 := by
  change (GlobalPlace.rationalAdic zeroBaseHeightOne).order RatFunc.X = 1
  rw [← RatFunc.algebraMap_X,
    GlobalPlace.rationalAdic_order_algebraMap_polynomial
      zeroBaseHeightOne Polynomial.X Polynomial.X_ne_zero,
    zeroBaseHeightOne_asIdeal, multiplicity_self]
  norm_num

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

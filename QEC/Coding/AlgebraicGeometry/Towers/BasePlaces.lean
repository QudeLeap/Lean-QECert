import QEC.Coding.AlgebraicGeometry.Towers.FixedFieldArtinSchreier
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicResidue

import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The selected finite base places for the F256 Garcia--Stichtenoth tower

The selected base coordinates are the 255 nonzero constants.  Each coordinate
defines the actual finite rational-function place cut out by `X - a`; its
residue equivalence is constructed from polynomial evaluation and the genuine
adic localization.  No upper place, tower count, divisor, or genus conclusion
is stored here.
-/

open Polynomial

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The literal nonzero initial coordinates of the selected split paths. -/
abbrev BasePoint := F256ˣ

/-- There are exactly 255 nonzero initial coordinates. -/
theorem basePoint_card : Fintype.card BasePoint = 255 := by
  rw [Fintype.card_units, f256_card]

private noncomputable def basePolynomial (a : BasePoint) : F256[X] :=
  X - C (a : F256)

private theorem basePolynomial_monic (a : BasePoint) :
    (basePolynomial a).Monic := by
  exact monic_X_sub_C (a : F256)

private theorem basePolynomial_irreducible (a : BasePoint) :
    Irreducible (basePolynomial a) := by
  exact irreducible_X_sub_C (a : F256)

private noncomputable def baseHeightOne (a : BasePoint) :
    IsDedekindDomain.HeightOneSpectrum F256[X] := by
  have hprime : Prime (basePolynomial a) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (basePolynomial_irreducible a)
  have hspanPrime : (Ideal.span ({basePolynomial a} : Set F256[X])).IsPrime :=
    (Ideal.span_singleton_prime (basePolynomial_irreducible a).ne_zero).mpr hprime
  exact IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime
      (Ideal.span_singleton_eq_bot.not.mpr
        (basePolynomial_irreducible a).ne_zero)
      hspanPrime)

private theorem baseHeightOne_asIdeal (a : BasePoint) :
    (baseHeightOne a).asIdeal =
      Ideal.span ({X - C (a : F256)} : Set F256[X]) := by
  rfl

/-- The actual height-one point underlying the selected rational base place.
This exposes the already-constructed finite centre for later restriction and
decomposition arguments; it stores no splitting conclusion. -/
noncomputable def baseHeightOnePoint (a : BasePoint) :
    IsDedekindDomain.HeightOneSpectrum F256[X] :=
  baseHeightOne a

@[simp]
theorem baseHeightOnePoint_asIdeal (a : BasePoint) :
    (baseHeightOnePoint a).asIdeal =
      Ideal.span ({X - C (a : F256)} : Set F256[X]) := by
  exact baseHeightOne_asIdeal a

private theorem baseRationalAdicPolynomial (a : BasePoint) :
    GlobalPlace.rationalAdicPolynomial (baseHeightOne a) =
      X - C (a : F256) := by
  apply Polynomial.eq_of_monic_of_associated
    (GlobalPlace.rationalAdicPolynomial_monic (baseHeightOne a))
    (monic_X_sub_C (a : F256))
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [← GlobalPlace.rationalAdic_asIdeal_eq_span]
  exact baseHeightOne_asIdeal a

private theorem baseAdjoinRootIdeal_eq (a : BasePoint) :
    Ideal.span
        ({GlobalPlace.rationalAdicPolynomial (baseHeightOne a)} : Set F256[X]) =
      Ideal.span ({X - C (a : F256)} : Set F256[X]) := by
  rw [baseRationalAdicPolynomial]

private noncomputable def baseAdjoinRootEquiv (a : BasePoint) :
    AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a)) ≃ₐ[F256]
      F256 :=
  (Ideal.quotientEquivAlgOfEq F256 (baseAdjoinRootIdeal_eq a)).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (a : F256))

private theorem baseAdjoinRootEquiv_symm_apply
    (a : BasePoint) (c : F256) :
    (baseAdjoinRootEquiv a).symm c =
      algebraMap F256
        (AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a))) c := by
  apply (baseAdjoinRootEquiv a).injective
  rw [(baseAdjoinRootEquiv a).apply_symm_apply,
    (baseAdjoinRootEquiv a).commutes]
  simp

private noncomputable def baseResidueEquiv (a : BasePoint) :
    F256 ≃+* GlobalPlace.residueField
      (GlobalPlace.rationalAdic (baseHeightOne a)) :=
  (baseAdjoinRootEquiv a).symm.toRingEquiv.trans
    (GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a))

private theorem rationalAdicResidueEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum F256[X]) (c : F256) :
    GlobalPlace.rationalAdicResidueEquiv p
        (algebraMap F256
          (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p)) c) =
      GlobalPlace.constantsToResidue (GlobalPlace.rationalAdic p) c := by
  change (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing p (Polynomial.C c)) =
    (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.constantsToValuationRing (GlobalPlace.rationalAdic p) c)
  apply congrArg (GlobalPlace.rationalAdic p).residue
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]

private theorem baseResidueEquiv_apply (a : BasePoint) (c : F256) :
    baseResidueEquiv a c =
      GlobalPlace.constantsToResidue
        (GlobalPlace.rationalAdic (baseHeightOne a)) c := by
  change GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a)
      ((baseAdjoinRootEquiv a).symm c) = _
  rw [baseAdjoinRootEquiv_symm_apply]
  exact rationalAdicResidueEquiv_algebraMap (baseHeightOne a) c

/-- The actual rational place of `F256(X)` at the nonzero coordinate `a`. -/
noncomputable def baseRationalPlace (a : BasePoint) :
    RationalPlace F256 (RatFunc F256) where
  place := GlobalPlace.rationalAdic (baseHeightOne a)
  constantsEquiv := baseResidueEquiv a
  constantsEquiv_apply := baseResidueEquiv_apply a

/-- The place carried by `baseRationalPlace` is the adic place at its exposed
height-one centre. -/
theorem baseRationalPlace_place_eq_rationalAdic (a : BasePoint) :
    (baseRationalPlace a).place =
      GlobalPlace.rationalAdic (baseHeightOnePoint a) := by
  rfl

/-- The rational coordinate `X` is regular at every selected base place. -/
theorem baseRationalPlace_X_regular (a : BasePoint) :
    GlobalPlace.RegularAt (baseRationalPlace a).place RatFunc.X := by
  change GlobalPlace.RegularAt
    (GlobalPlace.rationalAdic (baseHeightOne a)) RatFunc.X
  rw [GlobalPlace.regularAt_iff_mem_valuationRing]
  simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    RatFunc.algebraMap_X] using
      (GlobalPlace.rationalAdicPolynomialToValuationRing
        (baseHeightOne a) Polynomial.X).property

/-- Residue evaluation at the selected base place sends `X` to its literal
nonzero coordinate. -/
theorem baseRationalPlace_evaluate_X (a : BasePoint) :
    (baseRationalPlace a).evaluateRegular RatFunc.X
        (baseRationalPlace_X_regular a) = (a : F256) := by
  have hxmem : RatFunc.X ∈
      (GlobalPlace.rationalAdic (baseHeightOne a)).valuationRing := by
    simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X] using
        (GlobalPlace.rationalAdicPolynomialToValuationRing
          (baseHeightOne a) Polynomial.X).property
  change (baseResidueEquiv a).symm
      ((GlobalPlace.rationalAdic (baseHeightOne a)).residue
        ⟨RatFunc.X, hxmem⟩) = (a : F256)
  apply (baseResidueEquiv a).injective
  rw [(baseResidueEquiv a).apply_symm_apply]
  rw [baseResidueEquiv_apply]
  let xO := GlobalPlace.rationalAdicPolynomialToValuationRing
    (baseHeightOne a) Polynomial.X
  have hinput :
      (⟨RatFunc.X, hxmem⟩ :
        (GlobalPlace.rationalAdic (baseHeightOne a)).valuationRing) = xO := by
    apply Subtype.ext
    simp only [xO, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  rw [hinput]
  have hmk :
      AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial (baseHeightOne a))
          Polynomial.X =
        algebraMap F256
          (AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a)))
          (a : F256) := by
    rw [baseRationalAdicPolynomial, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq]
    rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root
      (Polynomial.X - Polynomial.C (a : F256))]
    simp
  calc
    (GlobalPlace.rationalAdic (baseHeightOne a)).residue xO =
        GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a)
          (AdjoinRoot.mk
            (GlobalPlace.rationalAdicPolynomial (baseHeightOne a))
            Polynomial.X) := by
          exact (GlobalPlace.rationalAdicResidueEquiv_mk
            (baseHeightOne a) Polynomial.X).symm
    _ = GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a)
          (algebraMap F256
            (AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a)))
            (a : F256)) := by rw [hmk]
    _ = GlobalPlace.constantsToResidue
          (GlobalPlace.rationalAdic (baseHeightOne a)) (a : F256) :=
      rationalAdicResidueEquiv_algebraMap (baseHeightOne a) (a : F256)

private theorem basePolynomialIdealMultiplicity_eq_rootMultiplicity
    (a : BasePoint) (p : F256[X]) (hp : p ≠ 0) :
    multiplicity (Ideal.span ({X - C (a : F256)} : Set F256[X]))
        (Ideal.span ({p} : Set F256[X])) =
      p.rootMultiplicity (a : F256) := by
  letI : DecidableEq F256 := Classical.decEq F256
  rw [Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
  have hq : Irreducible (X - C (a : F256) : F256[X]) :=
    irreducible_X_sub_C (a : F256)
  have hqprime : Prime (X - C (a : F256) : F256[X]) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
  have hspanprime : Prime
      (Ideal.span ({X - C (a : F256)} : Set F256[X])) := by
    rw [Ideal.prime_span_singleton_iff]
    exact hqprime
  have hpSpan : Ideal.span ({p} : Set F256[X]) ≠ 0 :=
    Submodule.span_singleton_eq_bot.mp.mt hp
  have hfiniteElement : FiniteMultiplicity
      (X - C (a : F256) : F256[X]) p :=
    Polynomial.finiteMultiplicity_X_sub_C (a : F256) hp
  have hfiniteIdeal : FiniteMultiplicity
      (Ideal.span ({X - C (a : F256)} : Set F256[X]))
      (Ideal.span ({p} : Set F256[X])) :=
    FiniteMultiplicity.of_prime_left hspanprime hpSpan
  apply Nat.cast_injective (R := ℕ∞)
  rw [← hfiniteIdeal.emultiplicity_eq_multiplicity,
    ← hfiniteElement.emultiplicity_eq_multiplicity,
    Ideal.emultiplicity_eq_emultiplicity_span]

/-- At the rational place `X=a`, the order of a nonzero polynomial is its
root multiplicity at the literal point `a`. -/
theorem baseRationalPlace_order_algebraMap_polynomial
    (a : BasePoint) (p : F256[X]) (hp : p ≠ 0) :
    (baseRationalPlace a).place.order
        (algebraMap F256[X] (RatFunc F256) p) =
      (p.rootMultiplicity (a : F256) : ℤ) := by
  change (GlobalPlace.rationalAdic (baseHeightOne a)).order
      (algebraMap F256[X] (RatFunc F256) p) = _
  unfold GlobalPlace.order GlobalPlace.rationalAdic
  rw [(baseHeightOne a).valuation_of_algebraMap,
    (baseHeightOne a).intValuation_eq_exp_neg_multiplicity hp,
    WithZero.log_exp]
  simp only [neg_neg]
  rw [baseHeightOne_asIdeal,
    basePolynomialIdealMultiplicity_eq_rootMultiplicity a p hp]

/-- Distinct nonzero constants give distinct selected base places. -/
theorem baseRationalPlace_injective :
    Function.Injective (fun a : BasePoint => (baseRationalPlace a).place) := by
  intro a b hab
  change GlobalPlace.rationalAdic (baseHeightOne a) =
    GlobalPlace.rationalAdic (baseHeightOne b) at hab
  have hoption : (some (baseHeightOne a) :
      Option (IsDedekindDomain.HeightOneSpectrum F256[X])) =
      some (baseHeightOne b) := by
    exact (GlobalPlace.rationalPlaceEquiv (k := F256)).injective (by
      simpa only [GlobalPlace.rationalPlaceEquiv_apply_some] using hab)
  have hheight : baseHeightOne a = baseHeightOne b := Option.some.inj hoption
  have hpoly : (X - C (a : F256) : F256[X]) = X - C (b : F256) := by
    calc
      X - C (a : F256) =
          GlobalPlace.rationalAdicPolynomial (baseHeightOne a) :=
        (baseRationalAdicPolynomial a).symm
      _ = GlobalPlace.rationalAdicPolynomial (baseHeightOne b) := by rw [hheight]
      _ = X - C (b : F256) := baseRationalAdicPolynomial b
  apply Units.ext
  have hcoeff := congrArg (fun p : F256[X] => p.coeff 0) hpoly
  simpa using hcoeff

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

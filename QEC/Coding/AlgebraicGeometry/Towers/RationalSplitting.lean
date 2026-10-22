import QEC.Coding.AlgebraicGeometry.Towers.SplittingIdeals

import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Rational places in a split Garcia--Stichtenoth fibre

The sixteen upper primes constructed in the preceding layer are turned into
height-one points and normalized global places.  Their inertia degree one
identifies each actual residue field with `F256`; the equivalence is chosen
from the canonical constant-reduction map itself, so the resulting objects
are genuine `RationalPlace`s rather than abstract field isomorphisms.

Recursive coordinate values, level counts, divisors, and genus formulas are
formed later.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

/-- The height-one point represented by one of the sixteen split upper
primes. -/
noncomputable def splitUpperHeightOne
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    IsDedekindDomain.HeightOneSpectrum (SplitIntegralClosure Q P x hx) := by
  let R := (splitUpperPrime Q P x hx c).1
  letI : R.IsPrime := inferInstance
  letI : R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing) :=
    inferInstance
  letI : IsDiscreteValuationRing Q.place.valuationRing :=
    Q.place.valuationRing_isDiscreteValuationRing
  exact
    { asIdeal := R
      isPrime := inferInstance
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field Q.place.valuationRing) R }

@[simp]
theorem splitUpperHeightOne_asIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperHeightOne Q P x hx c).asIdeal =
      (splitUpperPrime Q P x hx c).1 :=
  rfl

/-- Distinct translations give distinct height-one points. -/
theorem splitUpperHeightOne_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperHeightOne Q P x hx) := by
  intro c d hcd
  apply splitUpperPrime_injective Q P x hx hregular
  apply Subtype.ext
  exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hcd

/-- The normalized global place attached to a split upper prime. -/
noncomputable def splitAbovePlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace F256 (StepField P x hx) where
  valuation := (splitUpperHeightOne Q P x hx c).valuation
    (StepField P x hx)
  normalized := (splitUpperHeightOne Q P x hx c).valuation_surjective
    (StepField P x hx)

/-- Distinct split height-one points induce distinct normalized global
places. -/
theorem splitAbovePlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitAbovePlace Q P x hx) := by
  intro c d hcd
  apply splitUpperHeightOne_injective Q P x hx hregular
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext y
  let C := splitUpperHeightOne Q P x hx c
  let D := splitUpperHeightOne Q P x hx d
  have hvaluation : C.valuation (StepField P x hx) =
      D.valuation (StepField P x hx) :=
    congrArg GlobalPlace.valuation hcd
  change y ∈ C.asIdeal ↔ y ∈ D.asIdeal
  rw [← C.valuation_lt_one_iff_mem (K := StepField P x hx),
    hvaluation, D.valuation_lt_one_iff_mem]

private theorem splitUpperPrime_inertiaDeg_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDeg'
        (splitUpperPrime Q P x hx c).1 = 1 := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (splitUpperPrime Q P x hx c).1
  let G := L ≃ₐ[K] L
  letI : IsDiscreteValuationRing O :=
    Q.place.valuationRing_isDiscreteValuationRing
  letI : MulSemiringAction G S :=
    IsIntegralClosure.MulSemiringAction O K L S
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S K L
  letI : R.IsPrime := inferInstance
  letI : R.LiesOver m := inferInstance
  calc
    m.inertiaDeg' R = m.inertiaDegIn S := by
      letI : m.IsMaximal := by dsimp [m]; infer_instance
      letI : R.IsMaximal := by dsimp [R]; infer_instance
      rw [Ideal.inertiaDeg'_eq_inertiaDeg]
      exact (Ideal.inertiaDegIn_eq_inertiaDeg m R G).symm
    _ = 1 := split_inertiaDegIn_eq_one Q P x hx hregular

private noncomputable def splitUpperQuotientConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+*
      (SplitIntegralClosure Q P x hx ⧸
        (splitUpperPrime Q P x hx c).1) := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (splitUpperPrime Q P x hx c).1
  letI : m.IsMaximal := by
    dsimp [m]
    infer_instance
  letI : R.IsMaximal := by
    dsimp [R]
    infer_instance
  letI : R.LiesOver m := inferInstance
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  letI : Field (S ⧸ R) := Ideal.Quotient.field R
  letI : Algebra (O ⧸ m) (S ⧸ R) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def R m).le
  have hfinrank : Module.finrank (O ⧸ m) (S ⧸ R) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap]
    exact splitUpperPrime_inertiaDeg_eq_one Q P x hx hregular c
  let e : (O ⧸ m) ≃+* (S ⧸ R) :=
    RingEquiv.ofBijective (algebraMap (O ⧸ m) (S ⧸ R))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank)
  exact Q.constantsEquiv.trans e

private noncomputable def splitUpperQuotientResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (SplitIntegralClosure Q P x hx ⧸
        (splitUpperPrime Q P x hx c).1) ≃+*
      GlobalPlace.residueField (splitAbovePlace Q P x hx c) := by
  let S := SplitIntegralClosure Q P x hx
  let L := StepField P x hx
  let H := splitUpperHeightOne Q P x hx c
  letI : H.asIdeal.IsMaximal := inferInstance
  let e₁ : (S ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime L) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime L)
  let e₂ : H.valuationSubringAtPrime L ≃+*
      (H.valuation L).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)

private noncomputable def splitUpperAbstractResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (splitAbovePlace Q P x hx c) :=
  (splitUpperQuotientConstantsEquiv Q P x hx hregular c).trans
    (splitUpperQuotientResidueEquiv Q P x hx c)

private theorem splitUpperConstantsToResidue_bijective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (splitAbovePlace Q P x hx c)) := by
  let e := splitUpperAbstractResidueEquiv Q P x hx hregular c
  letI : Finite (GlobalPlace.residueField (splitAbovePlace Q P x hx c)) :=
    Finite.of_equiv F256 e.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨(GlobalPlace.constantsToResidue
    (splitAbovePlace Q P x hx c)).injective, ?_⟩
  exact Nat.card_congr e.toEquiv

private noncomputable def splitUpperConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (splitAbovePlace Q P x hx c) :=
  RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (splitAbovePlace Q P x hx c))
    (splitUpperConstantsToResidue_bijective Q P x hx hregular c)

/-- Each of the sixteen split upper places is rational over `F256`, with the
actual constant-reduction map as its residue-field equivalence. -/
noncomputable def splitUpperRationalPlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    RationalPlace F256 (StepField P x hx) where
  place := splitAbovePlace Q P x hx c
  constantsEquiv := splitUpperConstantsEquiv Q P x hx hregular c
  constantsEquiv_apply _ := rfl

@[simp]
theorem splitUpperRationalPlace_place
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (c : LinearMap.ker f256ArtinSchreier) :
    (splitUpperRationalPlace Q P x hx hregular c).place =
      splitAbovePlace Q P x hx c :=
  rfl

/-- The sixteen rational upper places remain pairwise distinct. -/
theorem splitUpperRationalPlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x) :
    Function.Injective (splitUpperRationalPlace Q P x hx hregular) := by
  intro c d hcd
  apply splitAbovePlace_injective Q P x hx hregular
  exact congrArg RationalPlace.place hcd

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

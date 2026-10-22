import QEC.Coding.AlgebraicGeometry.Towers.SourceSplittingIdeals

import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Rational places in a selected source recursion fibre

The sixteen upper primes constructed in the preceding layer are turned into
height-one points and normalized global places.  Their inertia degree one
identifies each actual residue field with `F256`; the equivalence is chosen
from the canonical constant-reduction map itself, so the resulting objects
are genuine `RationalPlace`s rather than abstract field isomorphisms.

Recursive coordinate values and level counts are formed later.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

/-- The height-one point represented by one of the sixteen selected source
upper primes. -/
noncomputable def sourceSplitUpperHeightOne
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    IsDedekindDomain.HeightOneSpectrum (SourceSplitIntegralClosure Q P x hx) := by
  let R := (sourceSplitUpperPrime Q P x hx c).1
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
theorem sourceSplitUpperHeightOne_asIdeal
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (sourceSplitUpperHeightOne Q P x hx c).asIdeal =
      (sourceSplitUpperPrime Q P x hx c).1 :=
  rfl

/-- Distinct translations give distinct selected source height-one points. -/
theorem sourceSplitUpperHeightOne_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective (sourceSplitUpperHeightOne Q P x hx) := by
  intro c d hcd
  apply sourceSplitUpperPrime_injective Q P x hx hregular hsplit
  apply Subtype.ext
  exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hcd

/-- The normalized global place attached to a selected source upper prime. -/
noncomputable def sourceSplitAbovePlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    GlobalPlace F256 (SourceStepField P x hx) where
  valuation := (sourceSplitUpperHeightOne Q P x hx c).valuation
    (SourceStepField P x hx)
  normalized := (sourceSplitUpperHeightOne Q P x hx c).valuation_surjective
    (SourceStepField P x hx)

/-- Distinct selected source height-one points induce distinct normalized
global places. -/
theorem sourceSplitAbovePlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective (sourceSplitAbovePlace Q P x hx) := by
  intro c d hcd
  apply sourceSplitUpperHeightOne_injective Q P x hx hregular hsplit
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext y
  let C := sourceSplitUpperHeightOne Q P x hx c
  let D := sourceSplitUpperHeightOne Q P x hx d
  have hvaluation : C.valuation (SourceStepField P x hx) =
      D.valuation (SourceStepField P x hx) :=
    congrArg GlobalPlace.valuation hcd
  change y ∈ C.asIdeal ↔ y ∈ D.asIdeal
  rw [← C.valuation_lt_one_iff_mem (K := SourceStepField P x hx),
    hvaluation, D.valuation_lt_one_iff_mem]

private theorem sourceSplitUpperPrime_inertiaDeg_eq_one
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (IsLocalRing.maximalIdeal Q.place.valuationRing).inertiaDeg'
        (sourceSplitUpperPrime Q P x hx c).1 = 1 := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (sourceSplitUpperPrime Q P x hx c).1
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
    _ = 1 := sourceSplit_inertiaDegIn_eq_one
      Q P x hx hregular hsplit

private noncomputable def sourceSplitUpperQuotientConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+*
      (SourceSplitIntegralClosure Q P x hx ⧸
        (sourceSplitUpperPrime Q P x hx c).1) := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let m : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal S := (sourceSplitUpperPrime Q P x hx c).1
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
    exact sourceSplitUpperPrime_inertiaDeg_eq_one
      Q P x hx hregular hsplit c
  let e : (O ⧸ m) ≃+* (S ⧸ R) :=
    RingEquiv.ofBijective (algebraMap (O ⧸ m) (S ⧸ R))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank)
  exact Q.constantsEquiv.trans e

private noncomputable def sourceSplitUpperQuotientResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1) (c : LinearMap.ker f256ArtinSchreier) :
    (SourceSplitIntegralClosure Q P x hx ⧸
        (sourceSplitUpperPrime Q P x hx c).1) ≃+*
      GlobalPlace.residueField (sourceSplitAbovePlace Q P x hx c) := by
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  letI : H.asIdeal.IsMaximal := inferInstance
  let e₁ : (S ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime L) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime L)
  let e₂ : H.valuationSubringAtPrime L ≃+*
      (H.valuation L).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)

private noncomputable def sourceSplitUpperAbstractResidueEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (sourceSplitAbovePlace Q P x hx c) :=
  (sourceSplitUpperQuotientConstantsEquiv
      Q P x hx hregular hsplit c).trans
    (sourceSplitUpperQuotientResidueEquiv Q P x hx c)

private theorem sourceSplitUpperConstantsToResidue_bijective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (sourceSplitAbovePlace Q P x hx c)) := by
  let e := sourceSplitUpperAbstractResidueEquiv
    Q P x hx hregular hsplit c
  letI : Finite (GlobalPlace.residueField
      (sourceSplitAbovePlace Q P x hx c)) :=
    Finite.of_equiv F256 e.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨(GlobalPlace.constantsToResidue
    (sourceSplitAbovePlace Q P x hx c)).injective, ?_⟩
  exact Nat.card_congr e.toEquiv

private noncomputable def sourceSplitUpperConstantsEquiv
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    F256 ≃+* GlobalPlace.residueField (sourceSplitAbovePlace Q P x hx c) :=
  RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (sourceSplitAbovePlace Q P x hx c))
    (sourceSplitUpperConstantsToResidue_bijective
      Q P x hx hregular hsplit c)

/-- Each of the sixteen selected source upper places is rational over `F256`,
with the actual constant-reduction map as its residue-field equivalence. -/
noncomputable def sourceSplitUpperRationalPlace
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    RationalPlace F256 (SourceStepField P x hx) where
  place := sourceSplitAbovePlace Q P x hx c
  constantsEquiv := sourceSplitUpperConstantsEquiv
    Q P x hx hregular hsplit c
  constantsEquiv_apply _ := rfl

@[simp]
theorem sourceSplitUpperRationalPlace_place
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    (sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).place =
      sourceSplitAbovePlace Q P x hx c :=
  rfl

/-- The sixteen selected source rational upper places remain pairwise
distinct. -/
theorem sourceSplitUpperRationalPlace_injective
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    Function.Injective
      (sourceSplitUpperRationalPlace Q P x hx hregular hsplit) := by
  intro c d hcd
  apply sourceSplitAbovePlace_injective Q P x hx hregular hsplit
  exact congrArg RationalPlace.place hcd

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

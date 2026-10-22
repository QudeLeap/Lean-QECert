import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisFunctionField
import QEC.Coding.AlgebraicGeometry.Towers.SourceNormalClosureSplitting

import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Rational places in the split source normal-closure fibre

The preceding layer proves that the literal `z = 1` prime splits completely
in every actual Garcia--Stichtenoth normal closure.  This file turns every
prime in that fibre into a normalized global place, proves that its residue
field is the fixed constant field `F256`, and enumerates the resulting
rational places by the actual extension degree.

The enumeration is constructed from the proved prime fibre.  No place family,
cardinality, rationality statement, or asymptotic conclusion is supplied as
input data.  Genus and divisor calculations remain downstream.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)

private noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)

private noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  ((algebraMap GaloisBaseField (SourceGaloisClosureField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra

private noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  (galoisSelectedBaseValuationRingAlgebra m).toSMul

private noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceGaloisClosureField m) _ _
    (galoisSelectedBaseValuationRingAlgebra m)

private noncomputable local instance galoisSelectedBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField
      (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance
    galoisSelectedIntegralClosureFractionTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance
    galoisSelectedIntegralClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureField m) := by
    apply Module.IsTorsionFree.comap
      (R := SourceSeedBaseValuationRing)
      (S := SourceGaloisClosureField m)
      (M := SourceGaloisClosureField m)
      (algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m))
    · intro r hr
      have hinjective : Function.Injective
          (algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m)) :=
        (algebraMap GaloisBaseField (SourceGaloisClosureField m)).injective.comp
          (ValuationSubring.subtype_injective
            sourceSeedFixedBaseOnePlace.valuationRing)
      exact IsRegular.of_ne_zero fun hzero =>
        hr.ne_zero (hinjective (by simpa only [map_zero] using hzero))
    · intro r x
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (SourceGaloisClosureField m)

private noncomputable local instance galoisSelectedIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
      (SourceGaloisClosureIntegralClosure m)

private noncomputable local instance
    galoisSelectedIntegralClosureIsFractionRing (m : ℕ) :
    IsFractionRing (SourceGaloisClosureIntegralClosure m)
      (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension
    GaloisBaseField (SourceGaloisClosureField m)

private noncomputable local instance galoisSelectedIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)

private noncomputable def sourceSeedBaseOneValuationRingEquiv :
    SourceSeedBaseValuationRing ≃+*
      (baseRationalPlace (1 : BasePoint)).place.valuationRing where
  toFun x := ⟨galoisBaseFieldEquivRatFunc.symm x, by
    rw [GlobalPlace.mem_valuationRing_iff]
    exact (GlobalPlace.mem_valuationRing_iff
      sourceSeedFixedBaseOnePlace x).mp x.property⟩
  invFun x := ⟨galoisBaseFieldEquivRatFunc x, by
    rw [GlobalPlace.mem_valuationRing_iff]
    change (baseRationalPlace (1 : BasePoint)).place.valuation
      (galoisBaseFieldEquivRatFunc.symm
        (galoisBaseFieldEquivRatFunc x)) ≤ 1
    rw [galoisBaseFieldEquivRatFunc.symm_apply_apply]
    exact (GlobalPlace.mem_valuationRing_iff
      (baseRationalPlace (1 : BasePoint)).place x).mp x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact galoisBaseFieldEquivRatFunc.apply_symm_apply x
  right_inv x := by
    apply Subtype.ext
    exact galoisBaseFieldEquivRatFunc.symm_apply_apply x
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul _ _ _
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add _ _ _

private instance sourceSeedBaseOneValuationRingEquiv_isLocalHom :
    IsLocalHom sourceSeedBaseOneValuationRingEquiv.toRingHom :=
  ⟨fun x hx => by
    simpa using hx.map sourceSeedBaseOneValuationRingEquiv.symm.toRingHom⟩

private noncomputable def sourceSeedBaseOneResidueEquiv :
    GlobalPlace.residueField sourceSeedFixedBaseOnePlace ≃+*
      GlobalPlace.residueField (baseRationalPlace (1 : BasePoint)).place :=
  IsLocalRing.ResidueField.mapEquiv sourceSeedBaseOneValuationRingEquiv

private theorem sourceSeedBaseOneResidueEquiv_residue
    (z : SourceSeedBaseValuationRing) :
    sourceSeedBaseOneResidueEquiv
        (GlobalPlace.residue sourceSeedFixedBaseOnePlace z) =
      GlobalPlace.residue (baseRationalPlace (1 : BasePoint)).place
        (sourceSeedBaseOneValuationRingEquiv z) := by
  unfold sourceSeedBaseOneResidueEquiv
  exact IsLocalRing.ResidueField.map_residue
    sourceSeedBaseOneValuationRingEquiv.toRingHom z

private theorem sourceSeedBaseOneResidueEquiv_constants (a : F256) :
    sourceSeedBaseOneResidueEquiv
        (GlobalPlace.constantsToResidue sourceSeedFixedBaseOnePlace a) =
      GlobalPlace.constantsToResidue
        (baseRationalPlace (1 : BasePoint)).place a := by
  rw [show GlobalPlace.constantsToResidue sourceSeedFixedBaseOnePlace a =
      GlobalPlace.residue sourceSeedFixedBaseOnePlace
        (GlobalPlace.constantsToValuationRing
          sourceSeedFixedBaseOnePlace a) from rfl,
    sourceSeedBaseOneResidueEquiv_residue]
  apply congrArg
    (GlobalPlace.residue (baseRationalPlace (1 : BasePoint)).place)
  apply Subtype.ext
  exact galoisBaseFieldEquivRatFunc.symm.commutes a

private noncomputable def sourceSeedFixedBaseOneRationalPlace :
    RationalPlace F256 GaloisBaseField where
  place := sourceSeedFixedBaseOnePlace
  constantsEquiv :=
    (baseRationalPlace (1 : BasePoint)).constantsEquiv.trans
      sourceSeedBaseOneResidueEquiv.symm
  constantsEquiv_apply a := by
    change sourceSeedBaseOneResidueEquiv.symm
        ((baseRationalPlace (1 : BasePoint)).constantsEquiv a) =
      GlobalPlace.constantsToResidue sourceSeedFixedBaseOnePlace a
    apply sourceSeedBaseOneResidueEquiv.injective
    rw [sourceSeedBaseOneResidueEquiv.apply_symm_apply,
      (baseRationalPlace (1 : BasePoint)).constantsEquiv_apply,
      sourceSeedBaseOneResidueEquiv_constants]

/-- The height-one point represented by a prime in the completely split
normal-closure fibre. -/
noncomputable def sourceGaloisClosureUpperHeightOne (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    IsDedekindDomain.HeightOneSpectrum (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) := P.2.2
  exact
    { asIdeal := P.1
      isPrime := P.2.1
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field SourceSeedBaseValuationRing) P.1 }

@[simp]
theorem sourceGaloisClosureUpperHeightOne_asIdeal (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (sourceGaloisClosureUpperHeightOne m P).asIdeal = P.1 :=
  rfl

/-- The normalized global place attached to one prime in the split fibre. -/
noncomputable def sourceGaloisClosurePlaceOfPrime (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    GlobalPlace F256 (SourceGaloisClosureField m) where
  valuation := (sourceGaloisClosureUpperHeightOne m P).valuation
    (SourceGaloisClosureField m)
  normalized := (sourceGaloisClosureUpperHeightOne m P).valuation_surjective
    (SourceGaloisClosureField m)

private noncomputable def sourceGaloisClosureQuotientConstantsEquiv (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    F256 ≃+* HasQuotient.Quotient (SourceGaloisClosureIntegralClosure m)
      (P : Ideal (SourceGaloisClosureIntegralClosure m)) := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal C := P.1
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : p.IsMaximal := by
    dsimp [p]
    infer_instance
  letI : R.IsMaximal := by
    dsimp [R]
    exact P.2.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver
        (IsDiscreteValuationRing.not_a_field O) P.2)
  letI : R.LiesOver p := P.2.2
  letI : _root_.Field (O ⧸ p) := Ideal.Quotient.field p
  letI : _root_.Field (C ⧸ R) := Ideal.Quotient.field R
  let quotientAlgebra : Algebra (O ⧸ p) (C ⧸ R) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def R p).le
  letI : Algebra (O ⧸ p) (C ⧸ R) := quotientAlgebra
  letI : SMul (O ⧸ p) (C ⧸ R) := quotientAlgebra.toSMul
  letI : Module (O ⧸ p) (C ⧸ R) :=
    @Algebra.toModule (O ⧸ p) (C ⧸ R) _ _ quotientAlgebra
  letI : Module.Free (O ⧸ p) (C ⧸ R) :=
    Module.Free.of_divisionRing (O ⧸ p) (C ⧸ R)
  have hfinrank : Module.finrank (O ⧸ p) (C ⧸ R) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap]
    exact sourceGaloisClosure_inertiaDeg_eq_one m P
  let e : (O ⧸ p) ≃+* (C ⧸ R) :=
    RingEquiv.ofBijective (algebraMap (O ⧸ p) (C ⧸ R))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank)
  exact sourceSeedFixedBaseOneRationalPlace.constantsEquiv.trans e

private noncomputable def sourceGaloisClosureQuotientResidueEquiv (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    HasQuotient.Quotient (SourceGaloisClosureIntegralClosure m)
        (P : Ideal (SourceGaloisClosureIntegralClosure m)) ≃+*
      GlobalPlace.residueField (sourceGaloisClosurePlaceOfPrime m P) := by
  let C := SourceGaloisClosureIntegralClosure m
  let E := SourceGaloisClosureField m
  let H := sourceGaloisClosureUpperHeightOne m P
  letI : IsFractionRing C E :=
    galoisSelectedIntegralClosureIsFractionRing m
  letI : H.asIdeal.IsMaximal := inferInstance
  letI : Algebra C (H.valuationSubringAtPrime E) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraSubtypeMemValuationSubringValuationSubringAtPrime H
  letI : IsLocalization H.asIdeal.primeCompl
      (H.valuationSubringAtPrime E) :=
    IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime H
  let e₁ : (C ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime E) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime E)
  let e₂ : H.valuationSubringAtPrime E ≃+*
      (H.valuation E).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)

private noncomputable def sourceGaloisClosureAbstractResidueEquiv (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    F256 ≃+* GlobalPlace.residueField (sourceGaloisClosurePlaceOfPrime m P) :=
  (sourceGaloisClosureQuotientConstantsEquiv m P).trans
    (sourceGaloisClosureQuotientResidueEquiv m P)

private theorem sourceGaloisClosureConstantsToResidue_bijective (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (sourceGaloisClosurePlaceOfPrime m P)) := by
  let e := sourceGaloisClosureAbstractResidueEquiv m P
  letI : Finite
      (GlobalPlace.residueField (sourceGaloisClosurePlaceOfPrime m P)) :=
    Finite.of_equiv F256 e.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨(GlobalPlace.constantsToResidue
    (sourceGaloisClosurePlaceOfPrime m P)).injective, ?_⟩
  exact Nat.card_congr e.toEquiv

/-- Every prime in the completely split fibre gives an actual rational place
of the normal closure over `F256`. -/
noncomputable def sourceGaloisClosureRationalPlaceOfPrime (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    RationalPlace F256 (SourceGaloisClosureField m) where
  place := sourceGaloisClosurePlaceOfPrime m P
  constantsEquiv := RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (sourceGaloisClosurePlaceOfPrime m P))
    (sourceGaloisClosureConstantsToResidue_bijective m P)
  constantsEquiv_apply _ := rfl

private theorem sourceGaloisClosurePlaceOfPrime_injective (m : ℕ) :
    Function.Injective (sourceGaloisClosurePlaceOfPrime m) := by
  intro P Q hPQ
  apply Subtype.ext
  ext x
  let HP := sourceGaloisClosureUpperHeightOne m P
  let HQ := sourceGaloisClosureUpperHeightOne m Q
  have hvaluation : HP.valuation (SourceGaloisClosureField m) =
      HQ.valuation (SourceGaloisClosureField m) :=
    congrArg GlobalPlace.valuation hPQ
  change x ∈ HP.asIdeal ↔ x ∈ HQ.asIdeal
  rw [← HP.valuation_lt_one_iff_mem (K := SourceGaloisClosureField m),
    hvaluation, HQ.valuation_lt_one_iff_mem]

theorem sourceGaloisClosureRationalPlaceOfPrime_injective (m : ℕ) :
    Function.Injective (sourceGaloisClosureRationalPlaceOfPrime m) := by
  intro P Q hPQ
  apply sourceGaloisClosurePlaceOfPrime_injective m
  exact congrArg RationalPlace.place hPQ

/-- The source-facing number of selected places at normal-closure level
`m`, defined as the actual extension degree over `F256(z)`. -/
def sourceGaloisClosureSelectedLength (m : ℕ) : ℕ :=
  Module.finrank GaloisBaseField (SourceGaloisClosureField m)

theorem sourceGaloisClosureSelectedLength_eq (m : ℕ) :
    sourceGaloisClosureSelectedLength m =
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) :=
  rfl

/-- Finite coordinates for the complete prime fibre above `z = 1`. -/
noncomputable def sourceGaloisClosureSelectedPrimeEquiv (m : ℕ) :
    Fin (sourceGaloisClosureSelectedLength m) ≃
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceGaloisClosureIntegralClosure m) := by
  let S := (IsLocalRing.maximalIdeal
    SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)
  letI : Fintype S :=
    (IsDedekindDomain.primesOver_finite
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing)
      (SourceGaloisClosureIntegralClosure m)).fintype
  have hcard : Fintype.card S = sourceGaloisClosureSelectedLength m := by
    calc
      Fintype.card S = Nat.card S := Fintype.card_eq_nat_card
      _ = S.ncard := Nat.card_coe_set_eq _
      _ = Module.finrank GaloisBaseField (SourceGaloisClosureField m) :=
        sourceGaloisClosure_primesOver_ncard_eq_finrank m
      _ = sourceGaloisClosureSelectedLength m := rfl
  exact (finCongr hcard.symm).trans (Fintype.equivFin S).symm

/-- The rational place at one finite coordinate in the actual split fibre. -/
noncomputable def sourceGaloisClosureSelectedRationalPlace (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    RationalPlace F256 (SourceGaloisClosureField m) :=
  sourceGaloisClosureRationalPlaceOfPrime m
    (sourceGaloisClosureSelectedPrimeEquiv m j)

theorem sourceGaloisClosureSelectedRationalPlace_injective (m : ℕ) :
    Function.Injective (sourceGaloisClosureSelectedRationalPlace m) := by
  intro i j hij
  apply (sourceGaloisClosureSelectedPrimeEquiv m).injective
  apply sourceGaloisClosureRationalPlaceOfPrime_injective m
  exact hij

/-- The finite set of actual normalized global places in the split fibre. -/
noncomputable def sourceGaloisClosureSelectedPlaces (m : ℕ) :
    Finset (GlobalPlace F256 (SourceGaloisClosureField m)) := by
  classical
  exact Finset.univ.image fun j : Fin (sourceGaloisClosureSelectedLength m) =>
    (sourceGaloisClosureSelectedRationalPlace m j).place

theorem sourceGaloisClosureSelectedPlaces_card (m : ℕ) :
    (sourceGaloisClosureSelectedPlaces m).card =
      sourceGaloisClosureSelectedLength m := by
  classical
  rw [sourceGaloisClosureSelectedPlaces,
    Finset.card_image_of_injective _]
  · simp
  · intro i j hij
    apply (sourceGaloisClosureSelectedPrimeEquiv m).injective
    apply sourceGaloisClosurePlaceOfPrime_injective m
    exact hij

theorem sourceGaloisClosureSelectedLength_lower_bound (m : ℕ) :
    240 * 16 ^ m ≤ sourceGaloisClosureSelectedLength m :=
  sourceGaloisClosureField_finrank_lower_bound m

/-- The actual completely split fibre grows without bound. -/
theorem sourceGaloisClosureSelectedLength_tendsto_atTop :
    Filter.Tendsto sourceGaloisClosureSelectedLength Filter.atTop Filter.atTop := by
  have hpow : Filter.Tendsto (fun m : ℕ => 16 ^ m)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (16 : ℕ))
  have hscaled : Filter.Tendsto (fun m : ℕ => 240 * 16 ^ m)
      Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop' (by norm_num : 0 < (240 : ℕ))
  exact Filter.tendsto_atTop_mono
    (fun m => sourceGaloisClosureSelectedLength_lower_bound m) hscaled

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

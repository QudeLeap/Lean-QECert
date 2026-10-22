import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisSelectedPlaces
import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWPrincipalDivisor
import QEC.Coding.AlgebraicGeometry.Divisors.FinitePlaceDivisor

/-!
# The selected divisor in the F256 Garcia--Stichtenoth source Galois family

The completely split `z = 1` fibre has already been enumerated by actual
rational global places.  This file forms its reduced divisor and proves that
it is the zero divisor of the literal function `w ^ 15 - 1`.  Its poles are
the already-constructed infinity fibre, with the multiplicity forced by the
relation `w ^ 15 = z`.

No different, genus, canonical differential, or asymptotic ratio is asserted
here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

open IntermediateField
open scoped BigOperators Polynomial RatFunc

noncomputable section

private abbrev E (m : ℕ) := SourceGaloisClosureField m

private noncomputable local instance closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (E m) :=
  ((algebraMap (RatFunc F256) (E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra

private noncomputable local instance closurePolynomialRatFuncScalarTower
    (m : ℕ) : IsScalarTower (Polynomial F256) (RatFunc F256) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (E m) :=
  IsGalois.to_isSeparable

private theorem sourceGaloisClosureSelectedPlaceAt_injective (m : ℕ) :
    Function.Injective (fun j : Fin (sourceGaloisClosureSelectedLength m) =>
      (sourceGaloisClosureSelectedRationalPlace m j).place) := by
  classical
  let P := fun j : Fin (sourceGaloisClosureSelectedLength m) =>
    (sourceGaloisClosureSelectedRationalPlace m j).place
  have hcard :
      (Finset.univ.image P).card =
        (Finset.univ : Finset (Fin (sourceGaloisClosureSelectedLength m))).card := by
    calc
      (Finset.univ.image P).card =
          sourceGaloisClosureSelectedLength m := by
        simpa only [sourceGaloisClosureSelectedPlaces, P] using
          sourceGaloisClosureSelectedPlaces_card m
      _ = (Finset.univ :
          Finset (Fin (sourceGaloisClosureSelectedLength m))).card := by simp
  have hinjOn : Set.InjOn P
      (↑(Finset.univ : Finset (Fin (sourceGaloisClosureSelectedLength m))) :
        Set (Fin (sourceGaloisClosureSelectedLength m))) :=
    Finset.card_image_iff.mp hcard
  intro i j hij
  exact hinjOn (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- The reduced divisor on the actual completely split `z = 1` fibre. -/
noncomputable def sourceGaloisClosureSelectedDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (E m)) :=
  GlobalPlace.finitePlaceDivisor fun j : Fin (sourceGaloisClosureSelectedLength m) =>
    (sourceGaloisClosureSelectedRationalPlace m j).place

/-- Every selected rational place has coefficient one. -/
@[simp]
theorem sourceGaloisClosureSelectedDivisor_apply (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    sourceGaloisClosureSelectedDivisor m
        (sourceGaloisClosureSelectedRationalPlace m j).place = 1 := by
  exact GlobalPlace.finitePlaceDivisor_apply _
    (sourceGaloisClosureSelectedPlaceAt_injective m) j

/-- The support of the selected divisor is exactly the enumerated split
fibre. -/
theorem sourceGaloisClosureSelectedDivisor_support (m : ℕ) :
    ↑(sourceGaloisClosureSelectedDivisor m).support =
      Set.range (fun j : Fin (sourceGaloisClosureSelectedLength m) =>
        (sourceGaloisClosureSelectedRationalPlace m j).place) := by
  exact GlobalPlace.finitePlaceDivisor_support _
    (sourceGaloisClosureSelectedPlaceAt_injective m)

/-- The selected divisor is coefficientwise nonnegative. -/
theorem sourceGaloisClosureSelectedDivisor_nonnegative (m : ℕ) :
    Divisor.Nonnegative (sourceGaloisClosureSelectedDivisor m) := by
  exact GlobalPlace.finitePlaceDivisor_nonnegative _

private theorem selectedPlace_residueDegree_eq_one (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    GlobalPlace.residueDegree
        (sourceGaloisClosureSelectedRationalPlace m j).place = 1 := by
  let Q := sourceGaloisClosureSelectedRationalPlace m j
  letI : Algebra F256 (GlobalPlace.residueField Q.place) :=
    GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional F256 (GlobalPlace.residueField Q.place) :=
    GlobalPlace.residueField_finiteDimensional Q.place
  rw [GlobalPlace.residueDegree_eq_finrank]
  apply Module.finrank_of_bijective_algebraMap
  simpa only [GlobalPlace.residueAlgebra,
    RingHom.algebraMap_toAlgebra] using Q.constantsToResidue_bijective

/-- The selected divisor has the exact enumerated length. -/
theorem sourceGaloisClosureSelectedDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisClosureSelectedDivisor m) =
      sourceGaloisClosureSelectedLength m := by
  rw [sourceGaloisClosureSelectedDivisor,
    GlobalPlace.finitePlaceDivisor_degree]
  simp_rw [selectedPlace_residueDegree_eq_one]
  simp

/-- The literal function cutting out the selected split fibre. -/
noncomputable def sourceGaloisClosureSelectedVanishingFunction (m : ℕ) : E m :=
  ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ^ 15 - 1

theorem sourceGaloisClosureSelectedVanishingFunction_eq (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m =
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ^ 15 - 1 :=
  rfl

private theorem order_pow (m n : ℕ) (P : GlobalPlace F256 (E m))
    (x : E m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [(P.valuation).map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

/-- The selected vanishing function is nonzero.  An infinity-fibre place
detects the nonzero pole of its fifteenth-power term. -/
theorem sourceGaloisClosureSelectedVanishingFunction_ne_zero (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m ≠ 0 := by
  let P : SourceGaloisWInfinityPrime m :=
    Classical.choice (sourceGaloisWInfinityPrime_nonempty m)
  let Q := sourceGaloisWInfinityPlaceOfPrime m P
  let w : E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  intro hzero
  have hpow : w ^ 15 = 1 := by
    exact sub_eq_zero.mp (by
      simpa only [sourceGaloisClosureSelectedVanishingFunction, w] using hzero)
  have horderPow := order_pow m 15 Q w
  have horderW := sourceGaloisWInfinityPlaceOfPrime_order_generator m P
  have horderOne : Q.order (1 : E m) = 0 := by
    simpa only [map_one] using
      (Q.order_algebraMap (1 : F256) one_ne_zero)
  rw [hpow, horderOne, horderW] at horderPow
  have hramification := sourceGaloisWInfinityRamificationIndex_pos m
  omega

private theorem selectedVanishingFunction_order_of_generator_order_neg
    (m : ℕ) (P : GlobalPlace F256 (E m))
    (horder : P.order
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) < 0) :
    P.order (sourceGaloisClosureSelectedVanishingFunction m) =
      15 * P.order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) := by
  let w : E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  have hw : w ≠ 0 := sourceGaloisWClosureGenerator_ne_zero m
  have hwpow : w ^ 15 ≠ 0 := pow_ne_zero 15 hw
  have horderPow : P.order (w ^ 15) < 0 := by
    rw [order_pow]
    exact mul_neg_of_pos_of_neg (by norm_num) horder
  have hvaluationPow : 1 < P.valuation (w ^ 15) := by
    change WithZero.exp (0 : ℤ) < P.valuation (w ^ 15)
    rw [← WithZero.lt_log_iff_exp_lt
      ((P.valuation).ne_zero_iff.mpr hwpow)]
    unfold GlobalPlace.order at horderPow
    omega
  have hvaluationSub : P.valuation (w ^ 15 - 1) =
      P.valuation (w ^ 15) :=
    (P.valuation).map_sub_eq_of_lt_left (by
      simpa only [map_one] using hvaluationPow)
  rw [sourceGaloisClosureSelectedVanishingFunction_eq]
  change P.order (w ^ 15 - 1) = 15 * P.order w
  calc
    P.order (w ^ 15 - 1) = P.order (w ^ 15) := by
      unfold GlobalPlace.order
      rw [hvaluationSub]
    _ = 15 * P.order w := order_pow m 15 P w

private theorem selectedVanishingFunction_order_nonnegative_of_generator_order_nonnegative
    (m : ℕ) (P : GlobalPlace F256 (E m))
    (horder : 0 ≤ P.order
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)) :
    0 ≤ P.order (sourceGaloisClosureSelectedVanishingFunction m) := by
  let w : E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  have hw : w ≠ 0 := sourceGaloisWClosureGenerator_ne_zero m
  have hwRegular : GlobalPlace.RegularAt P w :=
    (P.regularAt_iff_order_nonnegative hw).mpr horder
  have hwMem : w ∈ P.valuationRing :=
    (P.regularAt_iff_mem_valuationRing w).mp hwRegular
  have hsubMem : w ^ 15 - 1 ∈ P.valuationRing :=
    P.valuationRing.sub_mem (P.valuationRing.pow_mem hwMem 15)
      P.valuationRing.one_mem
  apply (P.regularAt_iff_order_nonnegative
    (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)).mp
  rw [sourceGaloisClosureSelectedVanishingFunction_eq]
  exact (P.regularAt_iff_mem_valuationRing (w ^ 15 - 1)).mpr hsubMem

/-- The actual all-place pole divisor of `w ^ 15 - 1`. -/
noncomputable def sourceGaloisClosureSelectedVanishingFunctionPoleDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (E m)) := by
  classical
  let f := sourceGaloisClosureSelectedVanishingFunction m
  exact if hf : f = 0 then 0
    else (-GlobalPlace.principalDivisor (k := F256) (F := E m)
      (Units.mk0 f hf)) ⊔ 0

private theorem selectedVanishingFunctionPoleDivisor_eq_smul_generatorPole
    (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m =
      15 • sourceGaloisWClosureGeneratorPoleDivisor m := by
  have hf' : sourceGaloisClosureSelectedVanishingFunction m ≠ 0 :=
    sourceGaloisClosureSelectedVanishingFunction_ne_zero m
  ext P
  unfold sourceGaloisClosureSelectedVanishingFunctionPoleDivisor
  rw [dif_neg hf']
  simp only [Finsupp.sup_apply, Finsupp.neg_apply, Finsupp.zero_apply,
    GlobalPlace.principalDivisor_apply, Units.val_mk0,
    Finsupp.smul_apply, nsmul_eq_mul,
    sourceGaloisWClosureGeneratorPoleDivisor_apply]
  by_cases horder : 0 ≤ P.order
      ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m)
  · have hforder : 0 ≤ P.order
        (sourceGaloisClosureSelectedVanishingFunction m) :=
      selectedVanishingFunction_order_nonnegative_of_generator_order_nonnegative
        m P horder
    rw [max_eq_right (by omega), max_eq_right (by omega)]
    simp
  · have horderNeg : P.order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) < 0 :=
      lt_of_not_ge horder
    have hforder := selectedVanishingFunction_order_of_generator_order_neg
      m P horderNeg
    rw [hforder, max_eq_left (by omega), max_eq_left (by omega)]
    ring

/-- The pole divisor of `w ^ 15 - 1` is the actual infinity fibre with
multiplicity `15 e_∞`. -/
theorem sourceGaloisClosureSelectedVanishingFunction_polarDivisor (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m =
      (15 * sourceGaloisWInfinityRamificationIndex m) •
        sourceGaloisWInfinityFibreDivisor m := by
  rw [selectedVanishingFunctionPoleDivisor_eq_smul_generatorPole,
    sourceGaloisWClosureGenerator_polarDivisor]
  simp only [smul_smul]

private noncomputable local instance (priority := 2000)
    selectedDivisorBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)

private noncomputable local instance (priority := 2000)
    selectedDivisorBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)

private noncomputable local instance (priority := 2000)
    selectedDivisorBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (E m) :=
  ((algebraMap GaloisBaseField (E m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra

private noncomputable local instance (priority := 2000)
    selectedDivisorBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (E m) :=
  (selectedDivisorBaseValuationRingAlgebra m).toSMul

private noncomputable local instance (priority := 2000)
    selectedDivisorBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (E m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (E m) _ _
    (selectedDivisorBaseValuationRingAlgebra m)

private noncomputable local instance selectedDivisorBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance selectedDivisorIntegralClosureFractionTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance selectedDivisorIntegralClosureTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing (E m) := by
    apply Module.IsTorsionFree.comap
      (R := SourceSeedBaseValuationRing)
      (S := E m) (M := E m)
      (algebraMap SourceSeedBaseValuationRing (E m))
    · intro r hr
      have hinjective : Function.Injective
          (algebraMap SourceSeedBaseValuationRing (E m)) :=
        (algebraMap GaloisBaseField (E m)).injective.comp
          (ValuationSubring.subtype_injective
            sourceSeedFixedBaseOnePlace.valuationRing)
      exact IsRegular.of_ne_zero fun hzero =>
        hr.ne_zero (hinjective (by simpa only [map_zero] using hzero))
    · intro r x
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (E m)

private noncomputable local instance selectedDivisorIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (E m) (SourceGaloisClosureIntegralClosure m)

private noncomputable local instance selectedDivisorIntegralClosureIsFractionRing
    (m : ℕ) :
    IsFractionRing (SourceGaloisClosureIntegralClosure m) (E m) :=
  integralClosure.isFractionRing_of_finite_extension GaloisBaseField (E m)

private noncomputable local instance selectedDivisorIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (E m)

private theorem fixedBaseOnePlace_order_generator_sub_one :
    sourceSeedFixedBaseOnePlace.order
        (AdjoinSimple.gen F256 galoisBaseZ - 1) = 1 := by
  have hX : galoisBaseFieldEquivRatFunc RatFunc.X =
      AdjoinSimple.gen F256 galoisBaseZ := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X
      galoisBaseZ galoisBaseZ_transcendental
  have hXsymm : galoisBaseFieldEquivRatFunc.symm
      (AdjoinSimple.gen F256 galoisBaseZ) = RatFunc.X := by
    rw [← hX, galoisBaseFieldEquivRatFunc.symm_apply_apply]
  rw [sourceSeedFixedBaseOnePlace, GlobalPlace.comapAlgEquiv_order,
    map_sub, map_one, hXsymm]
  have horder := baseRationalPlace_order_algebraMap_polynomial
    (1 : BasePoint) (Polynomial.X - Polynomial.C (1 : F256))
      (Polynomial.monic_X_sub_C (1 : F256)).ne_zero
  change (baseRationalPlace (1 : BasePoint)).place.order
      (algebraMap F256[X] (RatFunc F256)
        (Polynomial.X - Polynomial.C (1 : F256))) =
    ((Polynomial.X - Polynomial.C (1 : F256)).rootMultiplicity
      (1 : F256) : ℤ) at horder
  rw [Polynomial.rootMultiplicity_X_sub_C_self] at horder
  simp only [map_sub, RatFunc.algebraMap_X, map_one] at horder
  exact horder

private theorem fixedBaseOnePlace_generator_sub_one_ne_zero :
    AdjoinSimple.gen F256 galoisBaseZ - 1 ≠ 0 := by
  intro hzero
  have horder := fixedBaseOnePlace_order_generator_sub_one
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder

private theorem fixedBaseOnePlace_valuation_generator_sub_one_lt_one :
    sourceSeedFixedBaseOnePlace.valuation
        (AdjoinSimple.gen F256 galoisBaseZ - 1) < 1 := by
  let x : GaloisBaseField := AdjoinSimple.gen F256 galoisBaseZ - 1
  have hx : x ≠ 0 := fixedBaseOnePlace_generator_sub_one_ne_zero
  have hvaluationNe : sourceSeedFixedBaseOnePlace.valuation x ≠ 0 :=
    sourceSeedFixedBaseOnePlace.valuation.ne_zero_iff.mpr hx
  have hlog : WithZero.log
      (sourceSeedFixedBaseOnePlace.valuation x) = -1 := by
    have horder := fixedBaseOnePlace_order_generator_sub_one
    unfold GlobalPlace.order at horder
    simpa only [x] using (show
      WithZero.log (sourceSeedFixedBaseOnePlace.valuation
        (AdjoinSimple.gen F256 galoisBaseZ - 1)) = -1 by omega)
  calc
    sourceSeedFixedBaseOnePlace.valuation x =
        WithZero.exp (WithZero.log
          (sourceSeedFixedBaseOnePlace.valuation x)) :=
      (WithZero.exp_log hvaluationNe).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]
    _ < WithZero.exp (0 : ℤ) := WithZero.exp_lt_exp.mpr (by omega)
    _ = 1 := by simp

private noncomputable def selectedBaseVanishingElement :
    SourceSeedBaseValuationRing :=
  ⟨AdjoinSimple.gen F256 galoisBaseZ - 1,
    (sourceSeedFixedBaseOnePlace.mem_valuationRing_iff _).mpr
      (le_of_lt fixedBaseOnePlace_valuation_generator_sub_one_lt_one)⟩

private theorem selectedBaseVanishingElement_mem_maximalIdeal :
    selectedBaseVanishingElement ∈
      IsLocalRing.maximalIdeal SourceSeedBaseValuationRing := by
  rw [Valuation.mem_maximalIdeal_iff]
  exact fixedBaseOnePlace_valuation_generator_sub_one_lt_one

private noncomputable def selectedVanishingIntegralElement (m : ℕ) :
    SourceGaloisClosureIntegralClosure m :=
  algebraMap SourceSeedBaseValuationRing
    (SourceGaloisClosureIntegralClosure m) selectedBaseVanishingElement

private theorem selectedVanishingIntegralElement_mem_upperPrime (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    selectedVanishingIntegralElement m ∈ P.1 := by
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) := P.2.2
  change algebraMap SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) selectedBaseVanishingElement ∈ P.1
  exact (Ideal.mem_of_liesOver (P := P.1)
    (p := IsLocalRing.maximalIdeal SourceSeedBaseValuationRing)
    selectedBaseVanishingElement).mp
      selectedBaseVanishingElement_mem_maximalIdeal

private theorem selectedVanishingIntegralElement_coe (m : ℕ) :
    ((selectedVanishingIntegralElement m : SourceGaloisClosureIntegralClosure m) :
        E m) = sourceGaloisClosureSelectedVanishingFunction m := by
  calc
    ((selectedVanishingIntegralElement m : SourceGaloisClosureIntegralClosure m) :
        E m) =
        algebraMap SourceSeedBaseValuationRing (E m)
          selectedBaseVanishingElement := by
      exact (IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        (SourceGaloisClosureIntegralClosure m) (E m)
        selectedBaseVanishingElement).symm
    _ = algebraMap GaloisBaseField (E m)
        (AdjoinSimple.gen F256 galoisBaseZ - 1) := rfl
    _ = algebraMap GaloisBaseField (E m)
          (AdjoinSimple.gen F256 galoisBaseZ) - 1 := by
      simpa only [map_one] using
        (algebraMap GaloisBaseField (E m)).map_sub
          (AdjoinSimple.gen F256 galoisBaseZ) 1
    _ = ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : E m) ^ 15 - 1 := by
      rw [sourceGaloisWClosureGenerator_pow_fifteen]
    _ = sourceGaloisClosureSelectedVanishingFunction m :=
      (sourceGaloisClosureSelectedVanishingFunction_eq m).symm

private theorem selectedPlace_valuation_vanishingFunction_lt_one
    (m : ℕ) (j : Fin (sourceGaloisClosureSelectedLength m)) :
    (sourceGaloisClosureSelectedRationalPlace m j).place.valuation
        (sourceGaloisClosureSelectedVanishingFunction m) < 1 := by
  let P := sourceGaloisClosureSelectedPrimeEquiv m j
  let H := sourceGaloisClosureUpperHeightOne m P
  have hmem : selectedVanishingIntegralElement m ∈ H.asIdeal := by
    simpa only [H, sourceGaloisClosureUpperHeightOne_asIdeal] using
      selectedVanishingIntegralElement_mem_upperPrime m P
  have hvaluation :=
    (H.valuation_lt_one_iff_mem
      (K := E m) (selectedVanishingIntegralElement m)).mpr hmem
  change H.valuation (E m)
      (sourceGaloisClosureSelectedVanishingFunction m) < 1
  rw [← selectedVanishingIntegralElement_coe]
  exact hvaluation

private theorem selectedPlace_order_vanishingFunction_at_least_one
    (m : ℕ) (j : Fin (sourceGaloisClosureSelectedLength m)) :
    1 ≤ (sourceGaloisClosureSelectedRationalPlace m j).place.order
      (sourceGaloisClosureSelectedVanishingFunction m) := by
  have hvaluation := selectedPlace_valuation_vanishingFunction_lt_one m j
  have hvaluationNe :
      (sourceGaloisClosureSelectedRationalPlace m j).place.valuation
          (sourceGaloisClosureSelectedVanishingFunction m) ≠ 0 :=
    (sourceGaloisClosureSelectedRationalPlace m j).place.valuation.ne_zero_iff.mpr
      (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)
  have hlog : WithZero.log
      ((sourceGaloisClosureSelectedRationalPlace m j).place.valuation
        (sourceGaloisClosureSelectedVanishingFunction m)) < 0 := by
    rw [← WithZero.exp_log hvaluationNe, ← WithZero.exp_zero] at hvaluation
    exact WithZero.exp_lt_exp.mp hvaluation
  unfold GlobalPlace.order
  omega

private noncomputable def selectedVanishingFunctionZeroDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (E m)) :=
  GlobalPlace.principalDivisor (k := F256) (F := E m)
      (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
        (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)) +
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m

private theorem selectedVanishingFunctionZeroDivisor_apply (m : ℕ)
    (P : GlobalPlace F256 (E m)) :
    selectedVanishingFunctionZeroDivisor m P =
      max (P.order (sourceGaloisClosureSelectedVanishingFunction m)) 0 := by
  have hf := sourceGaloisClosureSelectedVanishingFunction_ne_zero m
  unfold selectedVanishingFunctionZeroDivisor
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor
  simp only [Finsupp.add_apply, GlobalPlace.principalDivisor_apply,
    Units.val_mk0, dif_neg hf, Finsupp.sup_apply,
    Finsupp.neg_apply, Finsupp.zero_apply]
  omega

private theorem selectedVanishingFunctionZeroDivisor_nonnegative (m : ℕ) :
    Divisor.Nonnegative (selectedVanishingFunctionZeroDivisor m) := by
  intro P
  rw [selectedVanishingFunctionZeroDivisor_apply]
  exact le_max_right _ _

private theorem selectedVanishingFunctionPoleDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m) =
      sourceGaloisClosureSelectedLength m := by
  rw [sourceGaloisClosureSelectedVanishingFunction_polarDivisor]
  calc
    Divisor.degree GlobalPlace.residueDegree
        ((15 * sourceGaloisWInfinityRamificationIndex m) •
          sourceGaloisWInfinityFibreDivisor m) =
        (15 * sourceGaloisWInfinityRamificationIndex m : ℕ) *
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisWInfinityFibreDivisor m) := by
      simpa only [Divisor.degree, nsmul_eq_mul] using
        (Divisor.degreeHom GlobalPlace.residueDegree).map_nsmul
          (15 * sourceGaloisWInfinityRamificationIndex m)
          (sourceGaloisWInfinityFibreDivisor m)
    _ = (15 : ℤ) * (sourceGaloisWRelativeDegree m : ℤ) := by
      rw [Nat.cast_mul, mul_assoc,
        sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree]
      norm_num
    _ = sourceGaloisClosureSelectedLength m := by
      exact_mod_cast sourceGaloisWRelativeDegree_mul_fifteen m

private theorem selectedVanishingFunctionZeroDivisor_degree (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree
        (selectedVanishingFunctionZeroDivisor m) =
      sourceGaloisClosureSelectedLength m := by
  calc
    Divisor.degree GlobalPlace.residueDegree
        (selectedVanishingFunctionZeroDivisor m) =
        Divisor.degree GlobalPlace.residueDegree
            (GlobalPlace.principalDivisor (k := F256) (F := E m)
              (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
                (sourceGaloisClosureSelectedVanishingFunction_ne_zero m))) +
          Divisor.degree GlobalPlace.residueDegree
            (sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m) := by
      rw [selectedVanishingFunctionZeroDivisor, Divisor.degree_add]
    _ = 0 + sourceGaloisClosureSelectedLength m := by
      rw [GlobalPlace.principalDivisor_degree_zero,
        selectedVanishingFunctionPoleDivisor_degree]
    _ = sourceGaloisClosureSelectedLength m := zero_add _

private theorem selectedDivisor_le_vanishingFunctionZeroDivisor (m : ℕ) :
    sourceGaloisClosureSelectedDivisor m ≤
      selectedVanishingFunctionZeroDivisor m := by
  intro P
  classical
  by_cases hP : ∃ j : Fin (sourceGaloisClosureSelectedLength m),
      (sourceGaloisClosureSelectedRationalPlace m j).place = P
  · obtain ⟨j, rfl⟩ := hP
    rw [sourceGaloisClosureSelectedDivisor_apply,
      selectedVanishingFunctionZeroDivisor_apply]
    exact (selectedPlace_order_vanishingFunction_at_least_one m j).trans
      (le_max_left _ _)
  · have hzero : sourceGaloisClosureSelectedDivisor m P = 0 := by
      unfold sourceGaloisClosureSelectedDivisor
      apply GlobalPlace.finitePlaceDivisor_apply_eq_zero_of_not_mem
      simpa only [Set.mem_range] using hP
    rw [hzero]
    exact selectedVanishingFunctionZeroDivisor_nonnegative m P

private theorem residueDegree_pos (m : ℕ) (P : GlobalPlace F256 (E m)) :
    0 < GlobalPlace.residueDegree P := by
  letI : Algebra F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueAlgebra P
  letI : FiniteDimensional F256 (GlobalPlace.residueField P) :=
    GlobalPlace.residueField_finiteDimensional P
  rw [GlobalPlace.residueDegree_eq_finrank P]
  exact Module.finrank_pos

private theorem divisor_eq_of_le_of_degree_eq (m : ℕ)
    {D R : Divisor (GlobalPlace F256 (E m))} (hDR : D ≤ R)
    (hdegree : Divisor.degree GlobalPlace.residueDegree D =
      Divisor.degree GlobalPlace.residueDegree R) :
    D = R := by
  classical
  let H : Divisor (GlobalPlace F256 (E m)) := R - D
  have hHNonnegative : Divisor.Nonnegative H := by
    intro P
    dsimp only [H]
    exact sub_nonneg.mpr (hDR P)
  have hHDegree : Divisor.degree GlobalPlace.residueDegree H = 0 := by
    dsimp only [H]
    rw [Divisor.degree_sub, hdegree, sub_self]
  have hsum :
      (∑ P ∈ H.support,
        H P * (GlobalPlace.residueDegree P : ℤ)) = 0 := by
    exact hHDegree
  have htermNonnegative :
      ∀ P ∈ H.support,
        0 ≤ H P * (GlobalPlace.residueDegree P : ℤ) := by
    intro P _
    exact mul_nonneg (hHNonnegative P) (Int.natCast_nonneg _)
  have hHzero : H = 0 := by
    apply Finsupp.ext
    intro P
    by_cases hP : P ∈ H.support
    · have hterm :=
        (Finset.sum_eq_zero_iff_of_nonneg htermNonnegative).mp hsum P hP
      have hdegreeP : (GlobalPlace.residueDegree P : ℤ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (residueDegree_pos m P))
      exact (mul_eq_zero.mp hterm).resolve_right hdegreeP
    · exact Finsupp.notMem_support_iff.mp hP
  apply Finsupp.ext
  intro P
  have hcoefficient := DFunLike.congr_fun hHzero P
  change R P - D P = 0 at hcoefficient
  omega

private theorem selectedVanishingFunctionZeroDivisor_eq_selectedDivisor
    (m : ℕ) :
    selectedVanishingFunctionZeroDivisor m =
      sourceGaloisClosureSelectedDivisor m := by
  apply Eq.symm
  apply divisor_eq_of_le_of_degree_eq m
    (selectedDivisor_le_vanishingFunctionZeroDivisor m)
  rw [sourceGaloisClosureSelectedDivisor_degree,
    selectedVanishingFunctionZeroDivisor_degree]

/-- Every selected rational place is a simple zero of `w ^ 15 - 1`. -/
theorem sourceGaloisClosureSelectedRationalPlace_order_vanishingFunction (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    (sourceGaloisClosureSelectedRationalPlace m j).place.order
        (sourceGaloisClosureSelectedVanishingFunction m) = 1 := by
  have hcoefficient := congrArg
    (fun D : Divisor (GlobalPlace F256 (E m)) =>
      D (sourceGaloisClosureSelectedRationalPlace m j).place)
    (selectedVanishingFunctionZeroDivisor_eq_selectedDivisor m)
  change selectedVanishingFunctionZeroDivisor m
      (sourceGaloisClosureSelectedRationalPlace m j).place =
    sourceGaloisClosureSelectedDivisor m
      (sourceGaloisClosureSelectedRationalPlace m j).place at hcoefficient
  rw [selectedVanishingFunctionZeroDivisor_apply,
    sourceGaloisClosureSelectedDivisor_apply] at hcoefficient
  have horder := selectedPlace_order_vanishingFunction_at_least_one m j
  rw [max_eq_left (by omega)] at hcoefficient
  exact hcoefficient

/-- The principal divisor of `w ^ 15 - 1` is its reduced selected zero fibre
minus its actual infinity pole fibre. -/
theorem sourceGaloisClosureSelectedVanishingFunction_principalDivisor (m : ℕ) :
    GlobalPlace.principalDivisor (k := F256) (F := E m)
        (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
          (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)) =
      sourceGaloisClosureSelectedDivisor m -
        (15 * sourceGaloisWInfinityRamificationIndex m) •
          sourceGaloisWInfinityFibreDivisor m := by
  calc
    GlobalPlace.principalDivisor (k := F256) (F := E m)
        (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
          (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)) =
        (GlobalPlace.principalDivisor (k := F256) (F := E m)
            (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
              (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)) +
          sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m) -
            sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m := by
      abel
    _ = sourceGaloisClosureSelectedDivisor m -
        sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m := by
      rw [← selectedVanishingFunctionZeroDivisor,
        selectedVanishingFunctionZeroDivisor_eq_selectedDivisor]
    _ = sourceGaloisClosureSelectedDivisor m -
        (15 * sourceGaloisWInfinityRamificationIndex m) •
          sourceGaloisWInfinityFibreDivisor m := by
      rw [sourceGaloisClosureSelectedVanishingFunction_polarDivisor]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

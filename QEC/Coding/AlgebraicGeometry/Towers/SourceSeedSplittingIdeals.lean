import QEC.Coding.AlgebraicGeometry.Towers.SourceSelectedBaseRestriction
import QEC.Coding.AlgebraicGeometry.Towers.StepPlaceTransport

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Complete splitting of the z=1 place in the source levels

The standard `X=1` rational place is transported to the literal fixed base
`F256(z)`.  This file takes the integral closure of that valuation ring in
each finite source level and centres every already-constructed rational `z=1`
source place on that integral closure.  Its canonical
localization is proved to equal the original valuation ring, so distinct
source places give distinct upper primes.

The general, non-Galois ramification identity then shows that these explicit
primes exhaust the fibre and that every ramification index and inertia degree
is one.  No conclusion about the normal closure, its genus, a canonical
divisor, or an asymptotic ratio is made here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- The literal `X=1` rational place transported to the fixed base
`F256(z)`. -/
noncomputable def sourceSeedFixedBaseOnePlace :
    GlobalPlace F256 GaloisBaseField :=
  GlobalPlace.comapAlgEquiv galoisBaseFieldEquivRatFunc.symm
    (baseRationalPlace (1 : BasePoint)).place

/-- The source extension has its literal degree over the fixed base `F256(z)`. -/
theorem sourceSeed_fixedBase_finrank (m : ℕ) :
    Module.finrank GaloisBaseField (SourceField m) = 240 * 16 ^ m :=
  sourceGaloisBaseField_seed_finrank m

/-- The base DVR at the transported literal point `X=1`. -/
abbrev SourceSeedBaseValuationRing : Type :=
  sourceSeedFixedBaseOnePlace.valuationRing

private noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)

private noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)

private noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceField m) :=
  ((algebraMap GaloisBaseField (SourceField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra

private noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceField m) :=
  (sourceSeedBaseValuationRingAlgebra m).toSMul

private noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceField m) _ _
    (sourceSeedBaseValuationRingAlgebra m)

/-- The integral closure of the transported `X=1` DVR in source level `m`. -/
abbrev SourceSeedIntegralClosure (m : ℕ) : Type :=
  integralClosure SourceSeedBaseValuationRing (SourceField m)

private noncomputable local instance sourceSeedBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField (SourceField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance sourceSeedIntegralClosureTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing (SourceField m) :=
    Module.IsTorsionFree.trans_faithfulSMul
      SourceSeedBaseValuationRing GaloisBaseField (SourceField m)
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (SourceField m)

private noncomputable local instance sourceSeedIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (SourceField m) (SourceSeedIntegralClosure m)

private noncomputable local instance sourceSeedIntegralClosureIsFractionRing
    (m : ℕ) :
  IsFractionRing (SourceSeedIntegralClosure m) (SourceField m) :=
  integralClosure.isFractionRing_of_finite_extension
    GaloisBaseField (SourceField m)

private noncomputable local instance sourceSeedIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceSeedIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (SourceField m)

private theorem sourceSeedEmbedding_equiv_symm (m : ℕ)
    (x : GaloisBaseField) :
    sourceSelectedRatFuncEmbedding m (galoisBaseFieldEquivRatFunc.symm x) =
      algebraMap GaloisBaseField (SourceField m) x := by
  change sourceGaloisBaseFieldEmbedding m
      (galoisBaseFieldEquivRatFunc
        (galoisBaseFieldEquivRatFunc.symm x)) = _
  rw [galoisBaseFieldEquivRatFunc.apply_symm_apply]
  rfl

private theorem sourceSeedValuation_isEquiv_comap
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedFixedBaseOnePlace.valuation.IsEquiv
      ((sourceSelectedRationalPlace m index).place.valuation.comap
        (algebraMap GaloisBaseField (SourceField m))) := by
  have hplace := sourceSelectedRestrictedBasePlace_eq_baseOne m index
  have hvaluation := congrArg GlobalPlace.valuation hplace
  have heq : sourceSeedFixedBaseOnePlace.valuation =
      (sourceSelectedRationalPlace m index).place.valuation.comap
        (algebraMap GaloisBaseField (SourceField m)) := by
    ext x
    change (baseRationalPlace (1 : BasePoint)).place.valuation
        (galoisBaseFieldEquivRatFunc.symm x) =
      (sourceSelectedRationalPlace m index).place.valuation
        (algebraMap GaloisBaseField (SourceField m) x)
    have hx := DFunLike.congr_fun hvaluation
      (galoisBaseFieldEquivRatFunc.symm x)
    change (sourceSelectedRationalPlace m index).place.valuation
        (sourceSelectedRatFuncEmbedding m
          (galoisBaseFieldEquivRatFunc.symm x)) =
      (baseRationalPlace (1 : BasePoint)).place.valuation
        (galoisBaseFieldEquivRatFunc.symm x) at hx
    rw [sourceSeedEmbedding_equiv_symm] at hx
    exact hx.symm
  rw [heq]

private noncomputable abbrev sourceSeedValuationHasExtension
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedFixedBaseOnePlace.valuation.HasExtension
      (sourceSelectedRationalPlace m index).place.valuation where
  val_isEquiv_comap := sourceSeedValuation_isEquiv_comap m index

private theorem sourceSeedIntegralClosure_le_valuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (integralClosure SourceSeedBaseValuationRing (SourceField m)).toSubring ≤
      (sourceSelectedRationalPlace m index).place.valuationRing.toSubring := by
  let P := sourceSeedFixedBaseOnePlace
  let Q := (sourceSelectedRationalPlace m index).place
  letI : P.valuation.HasExtension Q.valuation :=
    sourceSeedValuationHasExtension m index
  letI : IsIntegrallyClosedIn
      (sourceSelectedRationalPlace m index).place.valuationRing.toSubring
      (SourceField m) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn
      (R := (sourceSelectedRationalPlace m index).place.valuationRing)
      (SourceField m)).mp inferInstance
  change (integralClosure P.valuationRing (SourceField m)).toSubring ≤
    Q.valuationRing.toSubring
  rw [Subring.integralClosure_le_iff]
  intro x
  exact Valuation.HasExtension.algebraMap_mem_valuationSubring
    P.valuation Q.valuation x

private noncomputable def sourceSeedIntegralClosureToValuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    SourceSeedIntegralClosure m →+*
      (sourceSelectedRationalPlace m index).place.valuationRing := by
  let Q := (sourceSelectedRationalPlace m index).place
  exact (algebraMap (SourceSeedIntegralClosure m) (SourceField m)).codRestrict
    Q.valuationRing fun x =>
      sourceSeedIntegralClosure_le_valuationRing m index x.property

private noncomputable def sourceSeedUpperIdeal
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    Ideal (SourceSeedIntegralClosure m) :=
  (IsLocalRing.maximalIdeal
    (sourceSelectedRationalPlace m index).place.valuationRing).comap
      (sourceSeedIntegralClosureToValuationRing m index)

private theorem sourceSeedUpperIdeal_isPrime
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSeedUpperIdeal m index).IsPrime := by
  dsimp [sourceSeedUpperIdeal]
  exact (IsLocalRing.maximalIdeal
    (sourceSelectedRationalPlace m index).place.valuationRing).comap_isPrime _

private theorem sourceSeedUpperIdeal_liesOver
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSeedUpperIdeal m index).LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) := by
  let P := sourceSeedFixedBaseOnePlace
  let Q := (sourceSelectedRationalPlace m index).place
  letI : P.valuation.HasExtension Q.valuation :=
    sourceSeedValuationHasExtension m index
  constructor
  change IsLocalRing.maximalIdeal P.valuationRing =
    (IsLocalRing.maximalIdeal Q.valuationRing).comap
      (algebraMap P.valuationRing Q.valuationRing)
  exact (Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal
    P.valuation Q.valuation).symm

private theorem sourceSeedUpperIdeal_ne_bot
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperIdeal m index ≠ ⊥ := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let Q := (sourceSelectedRationalPlace m index).place
  obtain ⟨a, s, hs, hfrac⟩ :=
    IsFractionRing.div_surjective C Q.uniformizer
  have hs0 : algebraMap C (SourceField m) s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hu0 : Q.uniformizer ≠ 0 := by
    apply Q.valuation.ne_zero_iff.mp
    rw [Q.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hu_lt_one : Q.valuation Q.uniformizer < 1 := by
    rw [Q.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hs_mem : algebraMap C (SourceField m) s ∈ Q.valuationRing :=
    sourceSeedIntegralClosure_le_valuationRing m index s.property
  have hs_le_one : Q.valuation (algebraMap C (SourceField m) s) ≤ 1 :=
    (Q.valuation.mem_valuationSubring_iff _).mp hs_mem
  have hprod : algebraMap C (SourceField m) a =
      Q.uniformizer * algebraMap C (SourceField m) s := by
    calc
      algebraMap C (SourceField m) a =
          (algebraMap C (SourceField m) a / algebraMap C (SourceField m) s) *
            algebraMap C (SourceField m) s :=
        (div_mul_cancel₀ _ hs0).symm
      _ = Q.uniformizer * algebraMap C (SourceField m) s := by rw [hfrac]
  have ha0 : a ≠ 0 := by
    intro ha
    have hzero : Q.uniformizer * algebraMap C (SourceField m) s = 0 := by
      simpa [ha] using hprod.symm
    exact (mul_ne_zero hu0 hs0) hzero
  have ha_lt_one : Q.valuation (algebraMap C (SourceField m) a) < 1 := by
    calc
      Q.valuation (algebraMap C (SourceField m) a) =
          Q.valuation Q.uniformizer *
            Q.valuation (algebraMap C (SourceField m) s) := by
        rw [hprod, Q.valuation.map_mul]
      _ ≤ Q.valuation Q.uniformizer * 1 :=
        mul_le_mul_of_nonneg_left hs_le_one
          (le_of_lt (by rw [Q.valuation_uniformizer]; exact WithZero.exp_pos))
      _ = Q.valuation Q.uniformizer := mul_one _
      _ < 1 := hu_lt_one
  have ha_mem : a ∈ sourceSeedUpperIdeal m index := by
    change sourceSeedIntegralClosureToValuationRing m index a ∈
      IsLocalRing.maximalIdeal Q.valuationRing
    rw [Valuation.mem_maximalIdeal_iff]
    exact ha_lt_one
  intro hbot
  exact ha0 (Ideal.mem_bot.mp (hbot ▸ ha_mem))

private noncomputable def sourceSeedUpperHeightOne
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    IsDedekindDomain.HeightOneSpectrum (SourceSeedIntegralClosure m) :=
  ⟨sourceSeedUpperIdeal m index,
    sourceSeedUpperIdeal_isPrime m index,
    sourceSeedUpperIdeal_ne_bot m index⟩

private theorem sourceSeedUpperPrimeCompl_maps_to_unit
    (m : ℕ) (index : SourceSelectedPlaceIndex m)
    (s : (sourceSeedUpperHeightOne m index).asIdeal.primeCompl) :
    IsUnit (sourceSeedIntegralClosureToValuationRing m index s) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hs
  exact s.property hs

private noncomputable abbrev sourceSeedUpperCanonicalLocalization
    (m : ℕ) (index : SourceSelectedPlaceIndex m) : ValuationSubring (SourceField m) :=
  (sourceSeedUpperHeightOne m index).valuationSubringAtPrime (SourceField m)

private noncomputable def sourceSeedUpperLocalizationToValuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperCanonicalLocalization m index →+*
      (sourceSelectedRationalPlace m index).place.valuationRing :=
  IsLocalization.lift
    (M := (sourceSeedUpperHeightOne m index).asIdeal.primeCompl)
    (g := sourceSeedIntegralClosureToValuationRing m index)
    (sourceSeedUpperPrimeCompl_maps_to_unit m index)

private theorem sourceSeedUpperLocalizationToValuationRing_comp
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSeedUpperLocalizationToValuationRing m index).comp
        (algebraMap (SourceSeedIntegralClosure m)
          (sourceSeedUpperCanonicalLocalization m index)) =
      sourceSeedIntegralClosureToValuationRing m index := by
  simpa [sourceSeedUpperLocalizationToValuationRing] using
    (IsLocalization.lift_comp
      (sourceSeedUpperPrimeCompl_maps_to_unit m index))

private theorem sourceSeedUpperLocalization_coe_triangle
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (ValuationSubring.subtype
      (sourceSelectedRationalPlace m index).place.valuationRing).comp
        (sourceSeedUpperLocalizationToValuationRing m index) =
      ValuationSubring.subtype
        (sourceSeedUpperCanonicalLocalization m index) := by
  apply IsLocalization.ringHom_ext
    (sourceSeedUpperHeightOne m index).asIdeal.primeCompl
  ext b
  change (((sourceSeedUpperLocalizationToValuationRing m index
      (algebraMap (SourceSeedIntegralClosure m)
        (sourceSeedUpperCanonicalLocalization m index) b)) :
          (sourceSelectedRationalPlace m index).place.valuationRing) :
      SourceField m) = algebraMap (SourceSeedIntegralClosure m) (SourceField m) b
  rw [← RingHom.comp_apply,
    sourceSeedUpperLocalizationToValuationRing_comp]
  rfl

private theorem sourceSeedUpperCanonicalLocalization_le_valuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperCanonicalLocalization m index ≤
      (sourceSelectedRationalPlace m index).place.valuationRing := by
  intro x hx
  let xC : sourceSeedUpperCanonicalLocalization m index := ⟨x, hx⟩
  have htriangle := RingHom.congr_fun
    (sourceSeedUpperLocalization_coe_triangle m index) xC
  have hxField :
      ((sourceSeedUpperLocalizationToValuationRing m index xC :
        (sourceSelectedRationalPlace m index).place.valuationRing) :
          SourceField m) = x := by
    simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using
      htriangle
  rw [← hxField]
  exact (sourceSeedUpperLocalizationToValuationRing m index xC).property

private theorem sourceSeedPlaceValuation_isNontrivial
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRationalPlace m index).place.valuation.IsNontrivial := by
  let Q := (sourceSelectedRationalPlace m index).place
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨Q.uniformizer, ?_, ?_⟩
  · apply Q.valuation.ne_zero_iff.mp
    rw [Q.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [Q.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)

private theorem sourceSeedPlaceValuationRing_ne_top
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRationalPlace m index).place.valuationRing ≠ ⊤ := by
  let Q := (sourceSelectedRationalPlace m index).place
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff (v := Q.valuation)).mp htop)
    (sourceSeedPlaceValuation_isNontrivial m index)

private theorem sourceSeedUpperCanonicalLocalization_eq_valuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperCanonicalLocalization m index =
      (sourceSelectedRationalPlace m index).place.valuationRing :=
  ValuationSubring.eq_of_le_of_ne_top _
    (sourceSeedUpperCanonicalLocalization_le_valuationRing m index)
    (sourceSeedPlaceValuationRing_ne_top m index)

/-- The actual prime of the seed integral closure centred by one constructed
rational `z=1` source place. -/
noncomputable def sourceSeedUpperPrime (m : ℕ)
    (index : SourceSelectedPlaceIndex m) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m) := by
  letI : (sourceSeedUpperIdeal m index).IsPrime :=
    sourceSeedUpperIdeal_isPrime m index
  letI : (sourceSeedUpperIdeal m index).LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) :=
    sourceSeedUpperIdeal_liesOver m index
  exact Ideal.primesOver.mk _ (sourceSeedUpperIdeal m index)

private theorem globalPlace_eq_of_valuation_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    {P Q : GlobalPlace F256 E} (h : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

private theorem rationalPlace_eq_of_place_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    {P Q : RationalPlace F256 E} (h : P.place = Q.place) : P = Q := by
  cases P with
  | mk pp pe ph =>
      cases Q with
      | mk qp qe qh =>
          dsimp at h
          subst qp
          have he : pe = qe := by
            apply RingEquiv.ext
            intro a
            rw [ph, qh]
          subst qe
          rfl

/-- Distinct constructed source places have distinct centres in the seed
integral closure. -/
theorem sourceSeedUpperPrime_injective (m : ℕ) :
    Function.Injective (sourceSeedUpperPrime m) := by
  intro i j hij
  have hideal : sourceSeedUpperIdeal m i =
      sourceSeedUpperIdeal m j := congrArg Subtype.val hij
  have hheight : sourceSeedUpperHeightOne m i =
      sourceSeedUpperHeightOne m j := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact hideal
  have hvaluationRing :
      (sourceSelectedRationalPlace m i).place.valuationRing =
      (sourceSelectedRationalPlace m j).place.valuationRing := by
    rw [← sourceSeedUpperCanonicalLocalization_eq_valuationRing m i,
      ← sourceSeedUpperCanonicalLocalization_eq_valuationRing m j]
    change (sourceSeedUpperHeightOne m i).valuationSubringAtPrime (SourceField m) =
      (sourceSeedUpperHeightOne m j).valuationSubringAtPrime (SourceField m)
    rw [hheight]
  have hisEquiv :
      (sourceSelectedRationalPlace m i).place.valuation.IsEquiv
        (sourceSelectedRationalPlace m j).place.valuation := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    exact hvaluationRing
  have hvaluation :
      (sourceSelectedRationalPlace m i).place.valuation =
        (sourceSelectedRationalPlace m j).place.valuation :=
    normalizedValuation_eq_of_isEquiv
      (sourceSelectedRationalPlace m i).place.valuation
      (sourceSelectedRationalPlace m j).place.valuation
      (sourceSelectedRationalPlace m i).place.normalized
      (sourceSelectedRationalPlace m j).place.normalized hisEquiv
  apply sourceSelectedRationalPlace_injective m
  exact rationalPlace_eq_of_place_eq
    (globalPlace_eq_of_valuation_eq hvaluation)

/-- The explicit `z=1` source places exhaust the full prime fibre in the seed
integral closure. -/
theorem sourceSeed_primesOver_ncard (m : ℕ) :
    ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)).ncard = 240 * 16 ^ m := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let K := GaloisBaseField
  let L := SourceField m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O C := by
    change Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m)
    exact sourceSeedIntegralClosureTorsionFree m
  letI : NoZeroSMulDivisors O C := by
    constructor
    intro c x h
    exact smul_eq_zero.mp h
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hlower : 240 * 16 ^ m ≤ (p.primesOver C).ncard := by
    calc
      240 * 16 ^ m = Nat.card (SourceSelectedPlaceIndex m) := by
        rw [Nat.card_eq_fintype_card, sourceSelectedPlaceIndex_card]
      _ ≤ Nat.card (p.primesOver C) :=
        Nat.card_le_card_of_injective (sourceSeedUpperPrime m)
          (sourceSeedUpperPrime_injective m)
      _ = (p.primesOver C).ncard := Nat.card_coe_set_eq _
  have hupper : (p.primesOver C).ncard ≤ Module.finrank K L := by
    rw [← IsDedekindDomain.coe_primesOverFinset hp0 C,
      Set.ncard_coe_finset]
    exact Ideal.card_primesOverFinset_le_finrank C K L hp0
  apply le_antisymm
  · exact hupper.trans_eq (sourceSeed_fixedBase_finrank m)
  · exact hlower

/-- The finite source split paths are equivalent to all upper primes above the
literal base place `X=1`. -/
noncomputable def sourceSeedUpperPrimeEquiv (m : ℕ) :
    SourceSelectedPlaceIndex m ≃
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m) := by
  apply Equiv.ofBijective (sourceSeedUpperPrime m)
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨sourceSeedUpperPrime_injective m, ?_⟩
  calc
    Nat.card (SourceSelectedPlaceIndex m) = 240 * 16 ^ m := by
      rw [Nat.card_eq_fintype_card, sourceSelectedPlaceIndex_card]
    _ = ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m)).ncard :=
      (sourceSeed_primesOver_ncard m).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
          (SourceSeedIntegralClosure m)) :=
      (Nat.card_coe_set_eq _).symm

/-- A source-level function regular at every explicit place above `z = 1`
is represented by the integral closure of the corresponding base DVR. -/
theorem sourceSeedIntegralClosure_exists_of_regularAt_selected (m : ℕ)
    (x : SourceField m)
    (hx : ∀ index : SourceSelectedPlaceIndex m,
      GlobalPlace.RegularAt (sourceSelectedRationalPlace m index).place x) :
    ∃ xO : SourceSeedIntegralClosure m,
      algebraMap (SourceSeedIntegralClosure m) (SourceField m) xO = x := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let L := SourceField m
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one L x
  intro H
  have hcomap_ne : H.asIdeal.comap (algebraMap O C) ≠ ⊥ :=
    Ideal.IsIntegral.comap_ne_bot O H.ne_bot
  have hcomap_max :
      (H.asIdeal.comap (algebraMap O C)).IsMaximal :=
    (H.isPrime.comap (algebraMap O C)).isMaximal hcomap_ne
  have hover : H.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := by
    constructor
    exact (IsLocalRing.eq_maximalIdeal hcomap_max).symm
  let P : (IsLocalRing.maximalIdeal O).primesOver C := by
    letI : H.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := hover
    exact Ideal.primesOver.mk (IsLocalRing.maximalIdeal O) H.asIdeal
  let index : SourceSelectedPlaceIndex m :=
    (sourceSeedUpperPrimeEquiv m).symm P
  have hprime : sourceSeedUpperPrime m index = P :=
    (sourceSeedUpperPrimeEquiv m).apply_symm_apply P
  have hheight : sourceSeedUpperHeightOne m index = H := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    change (sourceSeedUpperPrime m index).1 = P.1
    exact congrArg Subtype.val hprime
  have hxSelected : x ∈
      (sourceSelectedRationalPlace m index).place.valuationRing :=
    (GlobalPlace.mem_valuationRing_iff
      (sourceSelectedRationalPlace m index).place x).mpr (hx index)
  have hxCanonical : x ∈ sourceSeedUpperCanonicalLocalization m index := by
    rw [sourceSeedUpperCanonicalLocalization_eq_valuationRing]
    exact hxSelected
  have hxAtH : x ∈ H.valuationSubringAtPrime L := by
    rw [← hheight]
    exact hxCanonical
  have hxValuationSubring : x ∈ (H.valuation L).valuationSubring := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hxAtH
  exact ((H.valuation L).mem_valuationSubring_iff x).mp hxValuationSubring

/-- The literal right-hand side of the next source recursion step is integral
at the fixed `z = 1` base DVR. -/
theorem sourceStepRhs_mem_sourceSeedIntegralClosure (m : ℕ) :
    ∃ xO : SourceSeedIntegralClosure m,
      algebraMap (SourceSeedIntegralClosure m) (SourceField m) xO =
        sourceStepRhs (sourceDistinguishedCoordinate m) := by
  apply sourceSeedIntegralClosure_exists_of_regularAt_selected
  intro index
  exact sourceStepRhs_regularAt_of_splitValue
    (sourceSelectedRationalPlace m index)
    (sourceDistinguishedCoordinate m)
    (sourceSelectedRationalPlace_coordinate_regular m index)
    (sourceSelectedRationalPlace_coordinate_split m index)

private theorem sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one
    (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx' P.1 *
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg' P.1 = 1 := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let K := GaloisBaseField
  let L := SourceField m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let s := IsDedekindDomain.primesOverFinset p C
  let f : Ideal C → ℕ := fun Q => p.ramificationIdx' Q * p.inertiaDeg' Q
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hPmem : P.1 ∈ s :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 C).2 P.2
  have hpositive : ∀ Q ∈ s, 0 < f Q := by
    intro Q hQ
    have hQdata := (IsDedekindDomain.mem_primesOverFinset_iff hp0 C).1 hQ
    letI : Q.IsPrime := hQdata.1
    letI : Q.LiesOver p := hQdata.2
    exact Nat.mul_pos
      (Nat.pos_of_ne_zero
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q hp0))
      (Nat.pos_of_ne_zero (Ideal.inertiaDeg_ne_zero p Q))
  have hrest : (s.erase P.1).card ≤ ∑ Q ∈ s.erase P.1, f Q := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun Q hQ =>
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (hpositive Q (Finset.mem_of_mem_erase hQ)))
  have hsum : ∑ Q ∈ s, f Q = Module.finrank K L :=
    Ideal.sum_ramification_inertia C K L hp0
  have hcard : s.card = Module.finrank K L := by
    calc
      s.card = (p.primesOver C).ncard := by
        rw [← IsDedekindDomain.coe_primesOverFinset hp0 C,
          Set.ncard_coe_finset]
      _ = 240 * 16 ^ m := sourceSeed_primesOver_ncard m
      _ = Module.finrank K L := (sourceSeed_fixedBase_finrank m).symm
  have hbound : f P.1 + (s.erase P.1).card ≤ Module.finrank K L := by
    calc
      f P.1 + (s.erase P.1).card ≤
          f P.1 + ∑ Q ∈ s.erase P.1, f Q :=
        Nat.add_le_add_left hrest _
      _ = ∑ Q ∈ s, f Q := Finset.add_sum_erase s f hPmem
      _ = Module.finrank K L := hsum
  have hcardErase : (s.erase P.1).card + 1 = Module.finrank K L := by
    calc
      (s.erase P.1).card + 1 = s.card := Finset.card_erase_add_one hPmem
      _ = Module.finrank K L := hcard
  have hfone : f P.1 = 1 := by
    have hfpos : 0 < f P.1 := hpositive P.1 hPmem
    omega
  exact hfone

/-- Every prime in the completely split seed fibre has ramification index
one. -/
theorem sourceSeed_ramificationIdx_eq_one (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).ramificationIdx'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  exact ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).inertiaDeg' P.1,
    (sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one m P).symm⟩

/-- Every prime in the completely split seed fibre has inertia degree one. -/
theorem sourceSeed_inertiaDeg_eq_one (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).inertiaDeg'
      P.1 = 1 := by
  apply Nat.eq_one_of_dvd_one
  refine ⟨(IsLocalRing.maximalIdeal
      SourceSeedBaseValuationRing).ramificationIdx' P.1, ?_⟩
  simpa only [Nat.mul_comm] using
    (sourceSeed_ramificationIdx_mul_inertiaDeg_eq_one m P).symm

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

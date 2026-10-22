import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWFibres

/-!
# Global places in the zero and infinity fibres over F256(w)

Every upper prime in the zero or infinity fibre of the actual intermediate
field `F256(w)` determines a normalized global place of the normal closure.
The order of the embedded generator at those places is the corresponding
common ramification index, with the expected sign.  No principal divisor,
different, genus, or canonical differential is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private abbrev W (m : ℕ) := SourceGaloisWClosureField m
private abbrev E (m : ℕ) := SourceGaloisClosureField m

private noncomputable local instance (priority := 3000)
    wClosureAlgebra (m : ℕ) : Algebra (W m) (E m) :=
  (W m).val.toRingHom.toAlgebra

private noncomputable local instance (priority := 3000)
    wClosureSMul (m : ℕ) : SMul (W m) (E m) :=
  (wClosureAlgebra m).toSMul

private noncomputable local instance (priority := 3000)
    wClosureModule (m : ℕ) : Module (W m) (E m) :=
  @Algebra.toModule (W m) (E m) _ _ (wClosureAlgebra m)

private noncomputable local instance (priority := 3000)
    wClosureFree (m : ℕ) : Module.Free (W m) (E m) :=
  Module.Free.of_divisionRing (W m) (E m)

private noncomputable local instance (priority := 3000)
    wBaseFree (m : ℕ) : Module.Free GaloisBaseField (W m) :=
  Module.Free.of_divisionRing GaloisBaseField (W m)

private noncomputable local instance (priority := 3000)
    wClosureFaithfulSMul (m : ℕ) : FaithfulSMul (W m) (E m) :=
  (faithfulSMul_iff_algebraMap_injective (W m) (E m)).2 (W m).val.injective

private noncomputable local instance wClosureScalarTower (m : ℕ) :
    IsScalarTower GaloisBaseField (W m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance wClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree (W m) (E m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (W m).val.injective

private noncomputable local instance wClosureFiniteDimensional (m : ℕ) :
    FiniteDimensional (W m) (E m) :=
  FiniteDimensional.right GaloisBaseField (W m) (E m)

private noncomputable local instance wClosureIsGalois (m : ℕ) :
    IsGalois (W m) (E m) :=
  IsGalois.tower_top_of_isGalois GaloisBaseField (W m) (E m)

private abbrev O (m : ℕ) (Q : GlobalPlace F256 (W m)) := Q.valuationRing

private noncomputable local instance (priority := 2000)
    oBaseModule (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Module (O m Q) (W m) :=
  @Algebra.toModule (O m Q) (W m) _ _
    (inferInstance : Algebra (O m Q) (W m))

private noncomputable local instance (priority := 2000)
    oBaseFaithfulSMul (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    FaithfulSMul (O m Q) (W m) :=
  (faithfulSMul_iff_algebraMap_injective (O m Q) (W m)).2
    (ValuationSubring.subtype_injective Q.valuationRing)

private noncomputable local instance (priority := 2000)
    oClosureAlgebra (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Algebra (O m Q) (E m) :=
  ((algebraMap (W m) (E m)).comp (algebraMap (O m Q) (W m))).toAlgebra

private noncomputable local instance (priority := 2000)
    oClosureSMul (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    SMul (O m Q) (E m) :=
  (oClosureAlgebra m Q).toSMul

private noncomputable local instance (priority := 2000)
    oClosureModule (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Module (O m Q) (E m) :=
  @Algebra.toModule (O m Q) (E m) _ _ (oClosureAlgebra m Q)

private noncomputable local instance oBaseScalarTower (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsScalarTower (O m Q) (W m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private abbrev C (m : ℕ) (Q : GlobalPlace F256 (W m)) :=
  integralClosure (O m Q) (E m)

private noncomputable local instance oIntegralClosureFractionTower (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsScalarTower (O m Q) (C m Q) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl

private noncomputable local instance oIntegralClosureTorsionFree (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : Module.IsTorsionFree (O m Q) (C m Q) := by
  letI : Module.IsTorsionFree (O m Q) (E m) :=
    Module.IsTorsionFree.trans_faithfulSMul (O m Q) (W m) (E m)
  exact IsIntegralClosure.isTorsionFree (O m Q) (E m)

private noncomputable local instance oIntegralClosureFaithfulSMul (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : FaithfulSMul (O m Q) (C m Q) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    intro a b hab
    apply ValuationSubring.subtype_injective Q.valuationRing
    apply (W m).val.injective
    exact congrArg (fun z : C m Q => (z : E m)) hab)

private noncomputable local instance oIntegralClosureFinite (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : Module.Finite (O m Q) (C m Q) := by
  letI : IsDiscreteValuationRing (O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite (O m Q) (W m) (E m) (C m Q)

private noncomputable local instance oIntegralClosureIsFractionRing (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsFractionRing (C m Q) (E m) :=
  integralClosure.isFractionRing_of_finite_extension (W m) (E m)

private noncomputable local instance oIntegralClosureIsDedekind (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsDedekindDomain (C m Q) := by
  letI : IsDiscreteValuationRing (O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain (O m Q) (W m) (E m)

/-- The height-one point represented by a prime above the zero place of
`F256(w)`. -/
noncomputable def sourceGaloisWZeroUpperHeightOne (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    IsDedekindDomain.HeightOneSpectrum (SourceGaloisWZeroIntegralClosure m) := by
  let O := (sourceGaloisWClosureZeroPlace m).valuationRing
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureZeroPlace m).valuationRing_isDiscreteValuationRing
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver (IsLocalRing.maximalIdeal O) := P.2.2
  exact
    { asIdeal := P.1
      isPrime := P.2.1
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field O) P.1 }

/-- The height-one point represented by a prime above the infinity place of
`F256(w)`. -/
noncomputable def sourceGaloisWInfinityUpperHeightOne (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    IsDedekindDomain.HeightOneSpectrum (SourceGaloisWInfinityIntegralClosure m) := by
  let O := (sourceGaloisWClosureInfinityPlace m).valuationRing
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureInfinityPlace m).valuationRing_isDiscreteValuationRing
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver (IsLocalRing.maximalIdeal O) := P.2.2
  exact
    { asIdeal := P.1
      isPrime := P.2.1
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field O) P.1 }

@[simp]
theorem sourceGaloisWZeroUpperHeightOne_asIdeal (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    (sourceGaloisWZeroUpperHeightOne m P).asIdeal = P.1 :=
  rfl

@[simp]
theorem sourceGaloisWInfinityUpperHeightOne_asIdeal (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    (sourceGaloisWInfinityUpperHeightOne m P).asIdeal = P.1 :=
  rfl

private noncomputable def sourceGaloisWPlaceOfHeightOne (m : ℕ)
    (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q)) :
    GlobalPlace F256 (E m) where
  valuation := H.valuation (E m)
  normalized := H.valuation_surjective (E m)

/-- The actual normalized global place attached to a zero-fibre prime. -/
noncomputable def sourceGaloisWZeroPlaceOfPrime (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    GlobalPlace F256 (SourceGaloisClosureField m) :=
  sourceGaloisWPlaceOfHeightOne m (sourceGaloisWClosureZeroPlace m)
    (sourceGaloisWZeroUpperHeightOne m P)

/-- The actual normalized global place attached to an infinity-fibre prime. -/
noncomputable def sourceGaloisWInfinityPlaceOfPrime (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) : GlobalPlace F256 (SourceGaloisClosureField m) :=
  sourceGaloisWPlaceOfHeightOne m (sourceGaloisWClosureInfinityPlace m)
    (sourceGaloisWInfinityUpperHeightOne m P)

/-- Distinct zero-fibre primes give distinct normalized global places. -/
theorem sourceGaloisWZeroPlaceOfPrime_injective (m : ℕ) :
    Function.Injective (sourceGaloisWZeroPlaceOfPrime m) := by
  intro P R hPR
  apply Subtype.ext
  ext x
  let HP := sourceGaloisWZeroUpperHeightOne m P
  let HR := sourceGaloisWZeroUpperHeightOne m R
  have hvaluation : HP.valuation (SourceGaloisClosureField m) =
      HR.valuation (SourceGaloisClosureField m) :=
    congrArg GlobalPlace.valuation hPR
  change x ∈ HP.asIdeal ↔ x ∈ HR.asIdeal
  rw [← HP.valuation_lt_one_iff_mem (K := SourceGaloisClosureField m), hvaluation,
    HR.valuation_lt_one_iff_mem]

/-- Distinct infinity-fibre primes give distinct normalized global places. -/
theorem sourceGaloisWInfinityPlaceOfPrime_injective (m : ℕ) :
    Function.Injective (sourceGaloisWInfinityPlaceOfPrime m) := by
  intro P R hPR
  apply Subtype.ext
  ext x
  let HP := sourceGaloisWInfinityUpperHeightOne m P
  let HR := sourceGaloisWInfinityUpperHeightOne m R
  have hvaluation : HP.valuation (SourceGaloisClosureField m) =
      HR.valuation (SourceGaloisClosureField m) :=
    congrArg GlobalPlace.valuation hPR
  change x ∈ HP.asIdeal ↔ x ∈ HR.asIdeal
  rw [← HP.valuation_lt_one_iff_mem (K := SourceGaloisClosureField m), hvaluation,
    HR.valuation_lt_one_iff_mem]

section SourceGaloisWOrderCertificate

attribute [local instance 5000]
  SubsemiringClass.toCommSemiring CommSemiring.toSemiring
  Semiring.toAddCommMonoid AddCommMonoid.toAddMonoid
  AddMonoid.toAddZeroClass AddZeroClass.toAddZero AddZero.toZero
  Zero.toOfNat0

private theorem sourceGaloisWElement_ne_zero_of_order_eq_one (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    x ≠ 0 := by
  intro hzero
  have horder := hx
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder

private noncomputable def sourceGaloisWOrderOneElement (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    Q.valuationRing :=
  ⟨x, (Q.regularAt_iff_mem_valuationRing x).mp
    ((Q.regularAt_iff_order_nonnegative
      (sourceGaloisWElement_ne_zero_of_order_eq_one m Q x hx)).mpr (by omega))⟩

@[simp]
private theorem coe_sourceGaloisWOrderOneElement (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    (sourceGaloisWOrderOneElement m Q x hx : W m) = x :=
  rfl

private theorem sourceGaloisWOrderOneElement_ne_zero (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    sourceGaloisWOrderOneElement m Q x hx ≠ 0 := by
  intro hzero
  apply sourceGaloisWElement_ne_zero_of_order_eq_one m Q x hx
  have hcoe := congrArg (fun y : Q.valuationRing => (y : W m)) hzero
  exact hcoe

private theorem sourceGaloisWOrderOneElement_valuation (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) =
      WithZero.exp (-1 : ℤ) := by
  have hvaluation_ne :
      Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) ≠ 0 :=
    Q.valuation.ne_zero_iff.mpr (by
      simpa only [coe_sourceGaloisWOrderOneElement] using
        sourceGaloisWElement_ne_zero_of_order_eq_one m Q x hx)
  have hlog : WithZero.log
      (Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m)) = -1 := by
    have horder := hx
    simp only [GlobalPlace.order] at horder
    simpa only [coe_sourceGaloisWOrderOneElement] using (show
      WithZero.log (Q.valuation x) = -1 by omega)
  calc
    Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) =
        WithZero.exp (WithZero.log
          (Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m))) :=
      (WithZero.exp_log hvaluation_ne).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]

private theorem maximalIdeal_eq_span_sourceGaloisWOrderOneElement (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    IsLocalRing.maximalIdeal Q.valuationRing =
      Ideal.span ({sourceGaloisWOrderOneElement m Q x hx} :
        Set Q.valuationRing) := by
  letI : Q.valuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨Q.uniformizer, ?_, ?_⟩
    · apply Q.valuation.ne_zero_iff.mp
      rw [Q.valuation_uniformizer]
      exact WithZero.exp_ne_zero
    · rw [Q.valuation_uniformizer, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass Q.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass Q.valuation)) := inferInstance
  letI : Q.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' Q.valuation
  apply Valuation.IsUniformizer.is_generator
  change Q.valuation (sourceGaloisWOrderOneElement m Q x hx : W m) =
    ((Valuation.IsRankOneDiscrete.generator Q.valuation :
      (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))
  rw [sourceGaloisWOrderOneElement_valuation]
  simpa using congrArg
    (fun u : (WithZero (Multiplicative ℤ))ˣ =>
      (u : WithZero (Multiplicative ℤ)))
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v := Q.valuation) Q.normalized).symm

end SourceGaloisWOrderCertificate

private theorem sourceGaloisWPlaceOfHeightOne_order_integral_eq_multiplicity
    (m : ℕ) (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q))
    {y : C m Q} (hy : y ≠ 0) :
    (sourceGaloisWPlaceOfHeightOne m Q H).order
        (algebraMap (C m Q) (E m) y) =
      (multiplicity H.asIdeal (Ideal.span {y}) : ℤ) := by
  have hvaluation :
      H.valuation (E m) (algebraMap (C m Q) (E m) y) =
        WithZero.exp (-(multiplicity H.asIdeal (Ideal.span {y}) : ℤ)) := by
    calc
      H.valuation (E m) (algebraMap (C m Q) (E m) y) =
          H.intValuation y := H.valuation_of_algebraMap y
      _ = WithZero.exp
          (-(multiplicity H.asIdeal (Ideal.span {y}) : ℤ)) :=
        H.intValuation_eq_exp_neg_multiplicity hy
  unfold GlobalPlace.order
  change -WithZero.log
      (H.valuation (E m) (algebraMap (C m Q) (E m) y)) = _
  have hlog :
      WithZero.log
          (H.valuation (E m) (algebraMap (C m Q) (E m) y)) =
        -(multiplicity H.asIdeal (Ideal.span {y}) : ℤ) :=
    (congrArg WithZero.log hvaluation).trans (WithZero.log_exp _)
  omega

private theorem algebraMap_sourceGaloisWOrderOneElement_ne_zero
    (m : ℕ) (Q : GlobalPlace F256 (W m)) (x : W m)
    (hx : Q.order x = 1) :
    algebraMap Q.valuationRing (C m Q)
        (sourceGaloisWOrderOneElement m Q x hx) ≠ 0 := by
  exact (Module.isTorsionFree_iff_algebraMap_injective.mp
    (oIntegralClosureTorsionFree m Q)).ne
      (sourceGaloisWOrderOneElement_ne_zero m Q x hx)

private theorem span_algebraMap_sourceGaloisWOrderOneElement_eq_map_maximalIdeal
    (m : ℕ) (Q : GlobalPlace F256 (W m)) (x : W m)
    (hx : Q.order x = 1) :
    Ideal.span
        ({algebraMap Q.valuationRing (C m Q)
          (sourceGaloisWOrderOneElement m Q x hx)} : Set (C m Q)) =
      Ideal.map (algebraMap Q.valuationRing (C m Q))
        (IsLocalRing.maximalIdeal Q.valuationRing) := by
  let t : Q.valuationRing := sourceGaloisWOrderOneElement m Q x hx
  let tC : C m Q := algebraMap Q.valuationRing (C m Q) t
  have hbase := maximalIdeal_eq_span_sourceGaloisWOrderOneElement m Q x hx
  calc
    Ideal.span ({tC} : Set (C m Q)) =
      Ideal.map (algebraMap Q.valuationRing (C m Q))
          (Ideal.span ({t} : Set Q.valuationRing)) := by
      symm
      simp only [Ideal.map_span, Set.image_singleton, tC]
    _ = Ideal.map (algebraMap Q.valuationRing (C m Q))
          (IsLocalRing.maximalIdeal Q.valuationRing) :=
      congrArg (Ideal.map (algebraMap Q.valuationRing (C m Q))) hbase.symm

private theorem map_sourceGaloisWMaximalIdeal_ne_bot
    (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Ideal.map (algebraMap Q.valuationRing (C m Q))
        (IsLocalRing.maximalIdeal Q.valuationRing) ≠ ⊥ := by
  letI : IsDiscreteValuationRing Q.valuationRing :=
    Q.valuationRing_isDiscreteValuationRing
  exact Ideal.map_ne_bot_of_ne_bot
    (IsDiscreteValuationRing.not_a_field Q.valuationRing)

set_option synthInstance.maxHeartbeats 100000 in
private theorem multiplicity_span_algebraMap_sourceGaloisWOrderOneElement_eq_ramificationIdx
    (m : ℕ) (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q))
    (x : W m) (hx : Q.order x = 1) :
    multiplicity H.asIdeal
        (Ideal.span
          ({algebraMap Q.valuationRing (C m Q)
            (sourceGaloisWOrderOneElement m Q x hx)} : Set (C m Q))) =
      (IsLocalRing.maximalIdeal Q.valuationRing).ramificationIdx' H.asIdeal := by
  calc
    multiplicity H.asIdeal
        (Ideal.span
          ({algebraMap Q.valuationRing (C m Q)
            (sourceGaloisWOrderOneElement m Q x hx)} : Set (C m Q))) =
      multiplicity H.asIdeal
        (Ideal.map (algebraMap Q.valuationRing (C m Q))
          (IsLocalRing.maximalIdeal Q.valuationRing)) :=
      congrArg (multiplicity H.asIdeal)
        (span_algebraMap_sourceGaloisWOrderOneElement_eq_map_maximalIdeal m Q x hx)
    _ = (IsLocalRing.maximalIdeal Q.valuationRing).ramificationIdx' H.asIdeal :=
      (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
        (map_sourceGaloisWMaximalIdeal_ne_bot m Q) H.isPrime).symm

set_option synthInstance.maxHeartbeats 100000 in
private theorem sourceGaloisWPlaceOfHeightOne_order_of_order_eq_one
    (m : ℕ) (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q))
    (x : W m) (hx : Q.order x = 1) :
    (sourceGaloisWPlaceOfHeightOne m Q H).order
        (algebraMap (W m) (E m) x) =
      ((IsLocalRing.maximalIdeal (O m Q)).ramificationIdx' H.asIdeal : ℤ) := by
  let t : Q.valuationRing := sourceGaloisWOrderOneElement m Q x hx
  let tC : C m Q := algebraMap Q.valuationRing (C m Q) t
  have htC_ne : tC ≠ 0 :=
    algebraMap_sourceGaloisWOrderOneElement_ne_zero m Q x hx
  change (sourceGaloisWPlaceOfHeightOne m Q H).order
      (algebraMap (C m Q) (E m) tC) =
    ((IsLocalRing.maximalIdeal Q.valuationRing).ramificationIdx' H.asIdeal : ℤ)
  rw [sourceGaloisWPlaceOfHeightOne_order_integral_eq_multiplicity m Q H htC_ne]
  norm_cast
  exact multiplicity_span_algebraMap_sourceGaloisWOrderOneElement_eq_ramificationIdx
    m Q H x hx

/-- At every zero-fibre upper place, the embedded generator has order equal
to the common zero ramification index. -/
theorem sourceGaloisWZeroPlaceOfPrime_order_generator (m : ℕ)
    (P : SourceGaloisWZeroPrime m) :
    (sourceGaloisWZeroPlaceOfPrime m P).order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
          SourceGaloisClosureField m) =
      (sourceGaloisWZeroRamificationIndex m : ℤ) := by
  have horder := sourceGaloisWPlaceOfHeightOne_order_of_order_eq_one m
    (sourceGaloisWClosureZeroPlace m) (sourceGaloisWZeroUpperHeightOne m P)
    (sourceGaloisWClosureGenerator m)
    (sourceGaloisWClosureZeroPlace_order_generator m)
  rw [sourceGaloisWZeroRamificationIndex_eq_prime m P]
  exact horder

/-- At every infinity-fibre upper place, the embedded generator has order
equal to the negative common infinity ramification index. -/
theorem sourceGaloisWInfinityPlaceOfPrime_order_generator (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    (sourceGaloisWInfinityPlaceOfPrime m P).order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
          SourceGaloisClosureField m) =
      -(sourceGaloisWInfinityRamificationIndex m : ℤ) := by
  have hinverse_order :
      (sourceGaloisWClosureInfinityPlace m).order
          (sourceGaloisWClosureGenerator m)⁻¹ = 1 := by
    rw [GlobalPlace.order_inv,
      sourceGaloisWClosureInfinityPlace_order_generator]
    norm_num
  have horder := sourceGaloisWPlaceOfHeightOne_order_of_order_eq_one m
    (sourceGaloisWClosureInfinityPlace m) (sourceGaloisWInfinityUpperHeightOne m P)
    (sourceGaloisWClosureGenerator m)⁻¹ hinverse_order
  rw [map_inv₀, GlobalPlace.order_inv] at horder
  change
    -(sourceGaloisWInfinityPlaceOfPrime m P).order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
          SourceGaloisClosureField m) =
      ((IsLocalRing.maximalIdeal
        (sourceGaloisWClosureInfinityPlace m).valuationRing).ramificationIdx'
          (sourceGaloisWInfinityUpperHeightOne m P).asIdeal : ℤ) at horder
  have hram := congrArg (fun n : ℕ => (n : ℤ))
    (sourceGaloisWInfinityRamificationIndex_eq_prime m P)
  have hram' : (sourceGaloisWInfinityRamificationIndex m : ℤ) =
      ((IsLocalRing.maximalIdeal
        (sourceGaloisWClosureInfinityPlace m).valuationRing).ramificationIdx'
          (sourceGaloisWInfinityUpperHeightOne m P).asIdeal : ℤ) := by
    simpa only [sourceGaloisWInfinityUpperHeightOne_asIdeal] using hram
  calc
    (sourceGaloisWInfinityPlaceOfPrime m P).order
        ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
          SourceGaloisClosureField m) =
        -(-(sourceGaloisWInfinityPlaceOfPrime m P).order
          ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) :
            SourceGaloisClosureField m)) := by ring
    _ = -((IsLocalRing.maximalIdeal
          (sourceGaloisWClosureInfinityPlace m).valuationRing).ramificationIdx'
            (sourceGaloisWInfinityUpperHeightOne m P).asIdeal : ℤ) :=
      congrArg Neg.neg horder
    _ = -(sourceGaloisWInfinityRamificationIndex m : ℤ) :=
      congrArg Neg.neg hram'.symm

end


end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

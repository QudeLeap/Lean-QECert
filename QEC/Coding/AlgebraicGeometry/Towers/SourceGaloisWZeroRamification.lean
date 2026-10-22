import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisSeedTranslation

/-!
# The source Galois ramification constraint above w = 0

At a zero-fibre place the seed coordinate `x₀` is regular.  If its order is
positive, the already constructed normal-closure automorphism replaces it by
`x₀ + 1`; otherwise `x₀` itself has order zero.  Applying the same
automorphism to the first source-step coordinate gives an actual conjugate
whose recursion right-hand side has order `-alpha`.  The degree-sixteen
Artin--Schreier equation then forces `16 ∣ alpha`.

This file proves only that zero-fibre divisibility, parity, and lower bound at
levels containing the first source step.  It does not assert a different,
divisor, genus, canonicality, or asymptotic conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

private noncomputable local instance (priority := 4000)
    sourceZeroClosureBaseAlgebraPinned (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureFieldAlgebra (m + 1)

private noncomputable local instance (priority := 4000)
    sourceZeroClosureBaseSMulPinned (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisClosureField (m + 1)) :=
  (sourceZeroClosureBaseAlgebraPinned m).toSMul

private noncomputable local instance (priority := 4000)
    sourceZeroClosureBaseModulePinned (m : ℕ) :
    Module GaloisBaseField (SourceGaloisClosureField (m + 1)) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisClosureField (m + 1)) _ _
    (sourceZeroClosureBaseAlgebraPinned m)

private noncomputable local instance (priority := 4000)
    sourceZeroClosureConstantAlgebraPinned (m : ℕ) :
    Algebra F256 (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureConstantAlgebra (m + 1)

private noncomputable local instance (priority := 4000)
    sourceZeroClosureConstantSMulPinned (m : ℕ) :
    SMul F256 (SourceGaloisClosureField (m + 1)) :=
  (sourceZeroClosureConstantAlgebraPinned m).toSMul

private noncomputable local instance (priority := 4000)
    sourceZeroClosureConstantModulePinned (m : ℕ) :
    Module F256 (SourceGaloisClosureField (m + 1)) :=
  @Algebra.toModule F256 (SourceGaloisClosureField (m + 1)) _ _
    (sourceZeroClosureConstantAlgebraPinned m)

private noncomputable local instance sourceZeroClosureConstantBaseTowerPinned
    (m : ℕ) : IsScalarTower F256 GaloisBaseField
      (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureConstantBaseScalarTower (m + 1)

private noncomputable local instance (priority := 4000)
    sourceZeroClosureRatFuncAlgebraPinned (m : ℕ) :
    Algebra (RatFunc F256) (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureRatFuncAlgebra (m + 1)

private noncomputable local instance (priority := 4000)
    sourceZeroClosureRatFuncSMulPinned (m : ℕ) :
    SMul (RatFunc F256) (SourceGaloisClosureField (m + 1)) :=
  (sourceZeroClosureRatFuncAlgebraPinned m).toSMul

private noncomputable local instance (priority := 4000)
    sourceZeroClosureRatFuncModulePinned (m : ℕ) :
    Module (RatFunc F256) (SourceGaloisClosureField (m + 1)) :=
  @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField (m + 1)) _ _
    (sourceZeroClosureRatFuncAlgebraPinned m)

private noncomputable local instance sourceZeroClosureRatFuncTowerPinned
    (m : ℕ) : IsScalarTower F256 (RatFunc F256)
      (SourceGaloisClosureField (m + 1)) :=
  sourceGaloisClosureRatFuncScalarTower (m + 1)

/-- The literal embedding of source level one through `m` further recursion
steps. -/
private noncomputable def sourceFirstLevelEmbedding :
    (m : ℕ) → SourceField 1 →ₐ[F256] SourceField (m + 1)
  | 0 => AlgHom.id F256 (SourceField 1)
  | m + 1 =>
      (sourceRecursionEmbedding (m + 1)).comp
        (sourceFirstLevelEmbedding m)

private theorem sourceFirstLevelEmbedding_seed (m : ℕ)
    (r : RatFunc F256) :
    sourceFirstLevelEmbedding m (sourceRecursionEmbedding 0 r) =
      algebraMap (RatFunc F256) (SourceField (m + 1)) r := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      rw [sourceFirstLevelEmbedding]
      change sourceRecursionEmbedding (m + 1)
          (sourceFirstLevelEmbedding m (sourceRecursionEmbedding 0 r)) = _
      rw [ih]
      letI : IsScalarTower (RatFunc F256) (SourceField (m + 1))
          (SourceField (m + 2)) :=
        IsScalarTower.of_algebraMap_eq' rfl
      change algebraMap (SourceField (m + 1)) (SourceField (m + 2))
          (algebraMap (RatFunc F256) (SourceField (m + 1)) r) =
        algebraMap (RatFunc F256) (SourceField (m + 2)) r
      exact IsScalarTower.algebraMap_apply (RatFunc F256)
        (SourceField (m + 1)) (SourceField (m + 2)) r

private theorem sourceFirstLevelEmbedding_seedClosure (m : ℕ)
    (r : RatFunc F256) :
    sourceGaloisSeedToClosure (m + 1)
        (sourceFirstLevelEmbedding m (sourceRecursionEmbedding 0 r)) =
      sourceGaloisSeedRatFuncToClosure (m + 1) r := by
  rw [sourceFirstLevelEmbedding_seed]
  rfl

/-- The literal level-one embedding followed by the actual seed inclusion into
the normal closure, with the constant field fixed explicitly. -/
private noncomputable def sourceFirstLevelToClosure (m : ℕ) :
    SourceField 1 →ₐ[F256] SourceGaloisClosureField (m + 1) :=
  ((sourceGaloisSeedToClosure (m + 1)).restrictScalars F256).comp
    (sourceFirstLevelEmbedding m)

private theorem sourceFirstLevelToClosure_seed (m : ℕ)
    (r : RatFunc F256) :
    sourceFirstLevelToClosure m (sourceRecursionEmbedding 0 r) =
      sourceGaloisSeedRatFuncToClosure (m + 1) r := by
  change sourceGaloisSeedToClosure (m + 1)
      (sourceFirstLevelEmbedding m (sourceRecursionEmbedding 0 r)) = _
  exact sourceFirstLevelEmbedding_seedClosure m r

/-- The first successor source coordinate inside closure level `m+1`. -/
private noncomputable def sourceGaloisFirstSuccessorCoordinate (m : ℕ) :
    SourceGaloisClosureField (m + 1) :=
  sourceFirstLevelToClosure m (sourceDistinguishedCoordinate 1)

private theorem sourceDistinguishedCoordinate_zero :
    sourceDistinguishedCoordinate 0 = (RatFunc.X : RatFunc F256) := by
  rfl

private theorem sourceGaloisFirstSuccessorCoordinate_equation (m : ℕ) :
    sourceGaloisFirstSuccessorCoordinate m ^ 16 +
        sourceGaloisFirstSuccessorCoordinate m =
      sourceGaloisSeedCoordinate (m + 1) ^ 16 /
        (sourceGaloisSeedCoordinate (m + 1) ^ 15 + 1) := by
  have hlevel := sourceRecursion_equation 0
  rw [sourceDistinguishedCoordinate_zero] at hlevel
  have hclosure := congrArg (sourceFirstLevelToClosure m) hlevel
  rw [sourceFirstLevelToClosure_seed] at hclosure
  simpa only [sourceGaloisFirstSuccessorCoordinate, map_add, map_pow,
    sourceStepRhs, map_div₀, map_one, sourceGaloisSeedCoordinate] using hclosure

private theorem sourceZero_seedCoordinate_ne_zero (m : ℕ) :
    sourceGaloisSeedCoordinate (m + 1) ≠ 0 := by
  have h := (sourceGaloisSeedRatFuncToClosure (m + 1)).injective.ne RatFunc.X_ne_zero
  simp only [map_zero] at h
  exact h

private theorem sourceZero_w_ne_zero (m : ℕ) :
    (sourceGaloisWClosureGenerator (m + 1) :
      SourceGaloisClosureField (m + 1)) ≠ 0 := by
  have hw : galoisBaseW ≠ 0 := by
    intro hzero
    apply sourceGaloisBaseW_transcendental
    rw [hzero]
    exact isAlgebraic_zero
  change sourceGaloisSeedRatFuncToClosure (m + 1) galoisBaseW ≠ 0
  have h := (sourceGaloisSeedRatFuncToClosure (m + 1)).injective.ne hw
  simp only [map_zero] at h
  exact h

private theorem sourceZero_order_pow (m n : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)))
    (x : SourceGaloisClosureField (m + 1)) :
    Q.order (x ^ n) = (n : ℤ) * Q.order x := by
  unfold GlobalPlace.order
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

private theorem sourceZero_valuation_eq_exp_neg_order (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)))
    (x : SourceGaloisClosureField (m + 1)) (hx : x ≠ 0) :
    Q.valuation x = WithZero.exp (-Q.order x) := by
  unfold GlobalPlace.order
  rw [neg_neg]
  exact (WithZero.exp_log (Q.valuation.ne_zero_iff.mpr hx)).symm

private theorem sourceZero_seed_order_nonnegative (m : ℕ)
    (P : SourceGaloisWZeroPrime (m + 1)) :
    0 ≤ (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order
      (sourceGaloisSeedCoordinate (m + 1)) := by
  let Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)) :=
    sourceGaloisWZeroPlaceOfPrime (m + 1) P
  let x : SourceGaloisClosureField (m + 1) :=
    sourceGaloisSeedCoordinate (m + 1)
  let w : SourceGaloisClosureField (m + 1) :=
    sourceGaloisWClosureGenerator (m + 1)
  have hx : x ≠ 0 := by
    simpa only [x] using sourceZero_seedCoordinate_ne_zero m
  have hrelation : x ^ 16 + x = w := by
    simpa only [x, w] using
      sourceGaloisSeedCoordinate_pow_sixteen_add (m + 1)
  have hworder : Q.order w =
      (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) := by
    simpa only [Q, w] using
      sourceGaloisWZeroPlaceOfPrime_order_generator (m + 1) P
  by_contra hnot
  have hxorder_neg : Q.order x < 0 := lt_of_not_ge hnot
  have hxpow_order : Q.order (x ^ 16) = 16 * Q.order x := by
    simpa only [Nat.cast_ofNat] using sourceZero_order_pow m 16 Q x
  have hxvalue : Q.valuation x = WithZero.exp (-Q.order x) :=
    sourceZero_valuation_eq_exp_neg_order m Q x hx
  have hxpowvalue : Q.valuation (x ^ 16) =
      WithZero.exp (-(16 * Q.order x)) := by
    rw [sourceZero_valuation_eq_exp_neg_order m Q (x ^ 16)
      (pow_ne_zero 16 hx), hxpow_order]
  have hvalue_lt : Q.valuation x < Q.valuation (x ^ 16) := by
    rw [hxvalue, hxpowvalue]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hsumorder : Q.order (x ^ 16 + x) = 16 * Q.order x := by
    calc
      Q.order (x ^ 16 + x) = Q.order (x ^ 16) := by
        unfold GlobalPlace.order
        rw [Q.valuation.map_add_eq_of_lt_left hvalue_lt]
      _ = 16 * Q.order x := hxpow_order
  rw [hrelation, hworder] at hsumorder
  have hpositive := sourceGaloisWZeroRamificationIndex_pos (m + 1)
  omega

private theorem exists_sourceZero_order_zero_seed_and_successor (m : ℕ)
    (P : SourceGaloisWZeroPrime (m + 1)) :
    ∃ y t : SourceGaloisClosureField (m + 1),
      (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order y = 0 ∧
      y ^ 16 + y =
      (sourceGaloisWClosureGenerator (m + 1) :
        SourceGaloisClosureField (m + 1)) ∧
      t ^ 16 + t = y ^ 16 / (y ^ 15 + 1) := by
  let Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)) :=
    sourceGaloisWZeroPlaceOfPrime (m + 1) P
  let x : SourceGaloisClosureField (m + 1) :=
    sourceGaloisSeedCoordinate (m + 1)
  let t : SourceGaloisClosureField (m + 1) :=
    sourceGaloisFirstSuccessorCoordinate m
  let w : SourceGaloisClosureField (m + 1) :=
    sourceGaloisWClosureGenerator (m + 1)
  have hx : x ≠ 0 := by
    simpa only [x] using sourceZero_seedCoordinate_ne_zero m
  have hxorder_nonnegative : 0 ≤ Q.order x := by
    simpa only [Q, x] using sourceZero_seed_order_nonnegative m P
  have hxrelation : x ^ 16 + x = w := by
    simpa only [x, w] using
      sourceGaloisSeedCoordinate_pow_sixteen_add (m + 1)
  have htrelation : t ^ 16 + t = x ^ 16 / (x ^ 15 + 1) := by
    simpa only [t, x] using
      sourceGaloisFirstSuccessorCoordinate_equation m
  by_cases hxpositive : 0 < Q.order x
  · let sigma : SourceGaloisClosureField (m + 1) ≃ₐ[GaloisBaseField]
        SourceGaloisClosureField (m + 1) :=
      sourceGaloisSeedOneTranslation (m + 1)
    have hsigma_add (a b : SourceGaloisClosureField (m + 1)) :
        sigma (a + b) = sigma a + sigma b := by
      exact sigma.map_add a b
    have hsigma_pow (a : SourceGaloisClosureField (m + 1)) (n : ℕ) :
        sigma (a ^ n) = sigma a ^ n := by
      exact sigma.map_pow a n
    have hsigma_div (a b : SourceGaloisClosureField (m + 1)) :
        sigma (a / b) = sigma a / sigma b := by
      exact map_div₀ sigma a b
    have hsigma_one : sigma (1 : SourceGaloisClosureField (m + 1)) = 1 := by
      exact sigma.map_one
    refine ⟨sigma x, sigma t, ?_, ?_, ?_⟩
    · have hxvalue : Q.valuation x = WithZero.exp (-Q.order x) :=
        sourceZero_valuation_eq_exp_neg_order m Q x hx
      have hvalue_lt : Q.valuation x < Q.valuation 1 := by
        rw [hxvalue, map_one, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by omega)
      have hsumvalue : Q.valuation (x + 1) = Q.valuation 1 :=
        Q.valuation.map_add_eq_of_lt_right hvalue_lt
      rw [show sigma x = x + 1 by
        simpa only [sigma, x] using
          sourceGaloisSeedOneTranslation_apply_coordinate (m + 1)]
      unfold GlobalPlace.order
      rw [hsumvalue, map_one]
      simp
    · have hsw : sigma w = w := by
        simpa only [sigma, w] using
          sourceGaloisSeedOneTranslation_apply_w (m + 1)
      calc
        (sigma x) ^ 16 + sigma x = sigma (x ^ 16) + sigma x := by
          rw [hsigma_pow]
        _ = sigma (x ^ 16 + x) := (hsigma_add (x ^ 16) x).symm
        _ = sigma w := congrArg
          (fun z : SourceGaloisClosureField (m + 1) => sigma z) hxrelation
        _ = w := hsw
    · calc
        (sigma t) ^ 16 + sigma t = sigma (t ^ 16) + sigma t := by
          rw [hsigma_pow]
        _ = sigma (t ^ 16 + t) := (hsigma_add (t ^ 16) t).symm
        _ = sigma (x ^ 16 / (x ^ 15 + 1)) := congrArg
          (fun z : SourceGaloisClosureField (m + 1) => sigma z) htrelation
        _ = sigma (x ^ 16) / sigma (x ^ 15 + 1) :=
          hsigma_div (x ^ 16) (x ^ 15 + 1)
        _ = (sigma x) ^ 16 / (sigma (x ^ 15) + sigma 1) := by
          rw [hsigma_pow, hsigma_add]
        _ = (sigma x) ^ 16 / ((sigma x) ^ 15 + 1) := by
          rw [hsigma_pow, hsigma_one]
  · refine ⟨x, t, ?_, hxrelation, htrelation⟩
    exact le_antisymm (le_of_not_gt hxpositive) hxorder_nonnegative

private theorem sourceZero_unit_seed_data (m : ℕ)
    (P : SourceGaloisWZeroPrime (m + 1))
    (y : SourceGaloisClosureField (m + 1))
    (hyorder : (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order y = 0)
    (hyrelation : y ^ 16 + y =
      (sourceGaloisWClosureGenerator (m + 1) :
        SourceGaloisClosureField (m + 1))) :
    y ≠ 0 ∧ y ^ 15 + 1 ≠ 0 ∧
      (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order (y ^ 15 + 1) =
        (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) := by
  let Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)) :=
    sourceGaloisWZeroPlaceOfPrime (m + 1) P
  let w : SourceGaloisClosureField (m + 1) :=
    sourceGaloisWClosureGenerator (m + 1)
  have hw : w ≠ 0 := by
    simpa only [w] using sourceZero_w_ne_zero m
  have hy : y ≠ 0 := by
    intro hzero
    rw [hzero] at hyrelation
    simp only [zero_pow (by norm_num : (16 : ℕ) ≠ 0), zero_add] at hyrelation
    exact hw (by simpa only [w] using hyrelation.symm)
  have hfactor : y * (y ^ 15 + 1) = w := by
    calc
      y * (y ^ 15 + 1) = y ^ 16 + y := by ring
      _ = w := by simpa only [w] using hyrelation
  have hden : y ^ 15 + 1 ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hw hfactor.symm
  have hworder : Q.order w =
      (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) := by
    simpa only [Q, w] using
      sourceGaloisWZeroPlaceOfPrime_order_generator (m + 1) P
  have hdenorder : Q.order (y ^ 15 + 1) =
      (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) := by
    have hproduct := Q.order_mul hy hden
    rw [hfactor, hworder, hyorder] at hproduct
    omega
  exact ⟨hy, hden, hdenorder⟩

private theorem sourceZero_successor_data (m : ℕ)
    (P : SourceGaloisWZeroPrime (m + 1))
    (y t : SourceGaloisClosureField (m + 1))
    (hyorder : (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order y = 0)
    (htrelation : t ^ 16 + t = y ^ 16 / (y ^ 15 + 1))
    (hy : y ≠ 0) (hden : y ^ 15 + 1 ≠ 0)
    (hdenorder : (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order
      (y ^ 15 + 1) =
        (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ)) :
    (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order
        (y ^ 16 / (y ^ 15 + 1)) =
          -(sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) ∧
      t ≠ 0 ∧
        (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order t < 0 := by
  let Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)) :=
    sourceGaloisWZeroPlaceOfPrime (m + 1) P
  have hrhsorder : Q.order (y ^ 16 / (y ^ 15 + 1)) =
      -(sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) := by
    rw [div_eq_mul_inv,
      Q.order_mul (pow_ne_zero 16 hy) (inv_ne_zero hden),
      Q.order_inv, sourceZero_order_pow m 16 Q y,
      hyorder, hdenorder]
    ring
  have hrhsne : y ^ 16 / (y ^ 15 + 1) ≠ 0 :=
    div_ne_zero (pow_ne_zero 16 hy) hden
  have ht : t ≠ 0 := by
    intro hzero
    rw [hzero] at htrelation
    simp only [zero_pow (by norm_num : (16 : ℕ) ≠ 0), zero_add] at htrelation
    exact hrhsne htrelation.symm
  have htorder_neg : Q.order t < 0 := by
    by_contra hnot
    have htorder_nonnegative : 0 ≤ Q.order t := le_of_not_gt hnot
    have htregular : GlobalPlace.RegularAt Q t :=
      (Q.regularAt_iff_order_nonnegative ht).mpr htorder_nonnegative
    have htmem : t ∈ Q.valuationRing :=
      (Q.regularAt_iff_mem_valuationRing t).mp htregular
    have htpowmem : t ^ 16 ∈ Q.valuationRing :=
      Q.valuationRing.toSubring.pow_mem htmem 16
    have hrhsmem : y ^ 16 / (y ^ 15 + 1) ∈ Q.valuationRing := by
      rw [← htrelation]
      exact Q.valuationRing.add_mem _ _ htpowmem htmem
    have hrhsregular : GlobalPlace.RegularAt Q
        (y ^ 16 / (y ^ 15 + 1)) :=
      (Q.regularAt_iff_mem_valuationRing _).mpr hrhsmem
    have hrhsorder_nonnegative :
        0 ≤ Q.order (y ^ 16 / (y ^ 15 + 1)) :=
      (Q.regularAt_iff_order_nonnegative hrhsne).mp hrhsregular
    have hpositive := sourceGaloisWZeroRamificationIndex_pos (m + 1)
    omega
  exact ⟨hrhsorder, ht, htorder_neg⟩

private theorem sourceZero_successor_sum_order (m : ℕ)
    (P : SourceGaloisWZeroPrime (m + 1))
    (t : SourceGaloisClosureField (m + 1))
    (ht : t ≠ 0)
    (htorder_neg :
      (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order t < 0) :
    (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order (t ^ 16 + t) =
      16 * (sourceGaloisWZeroPlaceOfPrime (m + 1) P).order t := by
  let Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)) :=
    sourceGaloisWZeroPlaceOfPrime (m + 1) P
  have htorder_negQ : Q.order t < 0 := by
    simpa only [Q] using htorder_neg
  have htpoworder : Q.order (t ^ 16) = 16 * Q.order t := by
    simpa only [Nat.cast_ofNat] using sourceZero_order_pow m 16 Q t
  have htvalue : Q.valuation t = WithZero.exp (-Q.order t) :=
    sourceZero_valuation_eq_exp_neg_order m Q t ht
  have htpowvalue : Q.valuation (t ^ 16) =
      WithZero.exp (-(16 * Q.order t)) := by
    rw [sourceZero_valuation_eq_exp_neg_order m Q (t ^ 16)
      (pow_ne_zero 16 ht), htpoworder]
  have hvalue_lt : Q.valuation t < Q.valuation (t ^ 16) := by
    rw [htvalue, htpowvalue]
    exact WithZero.exp_lt_exp.mpr (by omega)
  calc
    Q.order (t ^ 16 + t) = Q.order (t ^ 16) := by
      unfold GlobalPlace.order
      rw [Q.valuation.map_add_eq_of_lt_left hvalue_lt]
    _ = 16 * Q.order t := htpoworder

/-- The common ramification index above `w = 0` is divisible by sixteen at
every source closure level containing the first recursion step. -/
theorem sourceGaloisWZeroRamificationIndex_sixteen_dvd (m : ℕ) :
    16 ∣ sourceGaloisWZeroRamificationIndex (m + 1) := by
  let P : SourceGaloisWZeroPrime (m + 1) :=
    Classical.choice (sourceGaloisWZeroPrime_nonempty (m + 1))
  let Q : GlobalPlace F256 (SourceGaloisClosureField (m + 1)) :=
    sourceGaloisWZeroPlaceOfPrime (m + 1) P
  obtain ⟨y, t, hyorder, hyrelation, htrelation⟩ :=
    exists_sourceZero_order_zero_seed_and_successor m P
  obtain ⟨hy, hden, hdenorder⟩ :=
    sourceZero_unit_seed_data m P y hyorder hyrelation
  obtain ⟨hrhsorder, ht, htorder_neg⟩ :=
    sourceZero_successor_data m P y t hyorder htrelation hy hden hdenorder
  have hsumorder : Q.order (t ^ 16 + t) = 16 * Q.order t := by
    simpa only [Q] using sourceZero_successor_sum_order m P t ht htorder_neg
  rw [htrelation, hrhsorder] at hsumorder
  let n : ℕ := Int.natAbs (Q.order t)
  have hn : (n : ℤ) = -Q.order t := by
    dsimp [n]
    rw [Int.natCast_natAbs, abs_of_neg htorder_neg]
  refine ⟨n, ?_⟩
  have hcast : (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) =
      16 * (n : ℤ) := by
    calc
      (sourceGaloisWZeroRamificationIndex (m + 1) : ℤ) =
          -(16 * Q.order t) := by omega
      _ = 16 * (-Q.order t) := by ring
      _ = 16 * (n : ℤ) := by rw [← hn]
  exact_mod_cast hcast

/-- The common zero-fibre ramification index is even at every level
containing the first source step. -/
theorem sourceGaloisWZeroRamificationIndex_even (m : ℕ) :
    Even (sourceGaloisWZeroRamificationIndex (m + 1)) := by
  obtain ⟨n, hn⟩ := sourceGaloisWZeroRamificationIndex_sixteen_dvd m
  refine ⟨8 * n, ?_⟩
  omega

/-- The common zero-fibre ramification index is at least two at every level
containing the first source step. -/
theorem sourceGaloisWZeroRamificationIndex_two_le (m : ℕ) :
    2 ≤ sourceGaloisWZeroRamificationIndex (m + 1) := by
  obtain ⟨n, hn⟩ := sourceGaloisWZeroRamificationIndex_sixteen_dvd m
  have hpositive := sourceGaloisWZeroRamificationIndex_pos (m + 1)
  omega

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

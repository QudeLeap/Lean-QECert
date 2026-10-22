import QEC.Coding.AlgebraicGeometry.Towers.SourceGaloisWRamification

/-!
# The seed translation inside the source Garcia--Stichtenoth normal closure

Translation of the rational seed coordinate by one preserves
`w = x₀^16 + x₀`, and therefore fixes the rational base
`F256(z)` with `z = w^15`.  This file constructs that literal rational
automorphism and lifts it through the already constructed normal closure.

Only the translation and its action on `x₀` and `w` are exposed.  No place,
ramification index, different, divisor, genus, or asymptotic conclusion is
stored here.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

open IntermediateField Polynomial

private local instance f256CharTwo : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2

private local instance ratFuncCharTwo : CharP (RatFunc F256) 2 :=
  charP_of_injective_algebraMap
    (algebraMap F256 (RatFunc F256)).injective 2

private theorem ratFunc_X_add_one_transcendental :
    Transcendental F256 ((RatFunc.X : RatFunc F256) + 1) := by
  have hmonic :
      (Polynomial.X + 1 : Polynomial F256).Monic := by
    simpa only [← Polynomial.C_1] using
      Polynomial.monic_X_add_C (1 : F256)
  have htrans := RatFunc.transcendental_X.aeval
    (Polynomial.X + 1 : Polynomial F256)
    (by rw [← Polynomial.C_1, Polynomial.natDegree_X_add_C]; norm_num)
    (by simp [hmonic.leadingCoeff])
  convert htrans using 1
  simp [RatFunc.aeval_X_left_eq_algebraMap, RatFunc.algebraMap_X]

private noncomputable def sourceSeedOneTranslationPolynomialHom :
    Polynomial F256 →ₐ[F256] RatFunc F256 :=
  Polynomial.aeval (RatFunc.X + 1)

private theorem sourceSeedOneTranslationPolynomialHom_injective :
    Function.Injective sourceSeedOneTranslationPolynomialHom := by
  exact transcendental_iff_injective.mp ratFunc_X_add_one_transcendental

private theorem sourceSeedOneTranslationPolynomialHom_nonZeroDivisors :
    nonZeroDivisors (Polynomial F256) ≤
      (nonZeroDivisors (RatFunc F256)).comap
        sourceSeedOneTranslationPolynomialHom :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    sourceSeedOneTranslationPolynomialHom_injective

private noncomputable def sourceSeedOneTranslationHom :
    RatFunc F256 →ₐ[F256] RatFunc F256 :=
  RatFunc.liftAlgHom sourceSeedOneTranslationPolynomialHom
    sourceSeedOneTranslationPolynomialHom_nonZeroDivisors

private theorem sourceSeedOneTranslationHom_apply_algebraMap
    (p : Polynomial F256) :
    sourceSeedOneTranslationHom
        (algebraMap (Polynomial F256) (RatFunc F256) p) =
      Polynomial.aeval (RatFunc.X + 1) p := by
  exact RatFunc.liftRingHom_algebraMap
    sourceSeedOneTranslationPolynomialHom.toRingHom
    sourceSeedOneTranslationPolynomialHom_nonZeroDivisors p

private theorem sourceSeedOneTranslationHom_apply_X :
    sourceSeedOneTranslationHom RatFunc.X = RatFunc.X + 1 := by
  change sourceSeedOneTranslationHom
      (algebraMap (Polynomial F256) (RatFunc F256) Polynomial.X) = _
  rw [sourceSeedOneTranslationHom_apply_algebraMap]
  simp only [aeval_X]

private theorem sourceSeedOneTranslationHom_comp_self :
    sourceSeedOneTranslationHom.comp sourceSeedOneTranslationHom =
      AlgHom.id F256 (RatFunc F256) := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := Polynomial F256)
  intro p
  change sourceSeedOneTranslationHom
      (sourceSeedOneTranslationHom
        (algebraMap (Polynomial F256) (RatFunc F256) p)) =
    algebraMap (Polynomial F256) (RatFunc F256) p
  calc
    sourceSeedOneTranslationHom
        (sourceSeedOneTranslationHom
          (algebraMap (Polynomial F256) (RatFunc F256) p)) =
        sourceSeedOneTranslationHom
          (Polynomial.aeval (RatFunc.X + 1) p) := by
            rw [sourceSeedOneTranslationHom_apply_algebraMap]
    _ = Polynomial.aeval
          (sourceSeedOneTranslationHom (RatFunc.X + 1)) p := by
            rw [Polynomial.aeval_algHom_apply]
    _ = Polynomial.aeval RatFunc.X p := by
      rw [map_add, sourceSeedOneTranslationHom_apply_X, map_one,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = algebraMap (Polynomial F256) (RatFunc F256) p :=
      RatFunc.aeval_X_left_eq_algebraMap p

private noncomputable def sourceSeedOneTranslationOverF256 :
    RatFunc F256 ≃ₐ[F256] RatFunc F256 :=
  AlgEquiv.ofAlgHom sourceSeedOneTranslationHom sourceSeedOneTranslationHom
    sourceSeedOneTranslationHom_comp_self
    sourceSeedOneTranslationHom_comp_self

private theorem sourceSeedOneTranslationOverF256_apply_X :
    sourceSeedOneTranslationOverF256 RatFunc.X = RatFunc.X + 1 :=
  sourceSeedOneTranslationHom_apply_X

private theorem sourceSeedOneTranslationOverF256_apply_galoisBaseW :
    sourceSeedOneTranslationOverF256 galoisBaseW = galoisBaseW := by
  letI : CharP (RatFunc F256) 2 := inferInstance
  rw [galoisBaseW, map_add, map_pow,
    sourceSeedOneTranslationOverF256_apply_X]
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, add_pow_char_pow]
  have hones : (1 : RatFunc F256) + 1 = 0 :=
    CharTwo.add_self_eq_zero 1
  linear_combination hones

private theorem sourceSeedOneTranslationOverF256_apply_galoisBaseZ :
    sourceSeedOneTranslationOverF256 galoisBaseZ = galoisBaseZ := by
  rw [galoisBaseZ, map_pow,
    sourceSeedOneTranslationOverF256_apply_galoisBaseW]

private theorem sourceSeedOneTranslationOverF256_fixes_galoisBase :
    sourceSeedOneTranslationOverF256.toAlgHom.comp
        (IntermediateField.adjoin F256
          ({galoisBaseZ} : Set (RatFunc F256))).val =
      (IntermediateField.adjoin F256
        ({galoisBaseZ} : Set (RatFunc F256))).val := by
  apply IntermediateField.adjoin_algHom_ext
  intro x hx
  have hx' : x = galoisBaseZ := Set.mem_singleton_iff.mp hx
  subst x
  exact sourceSeedOneTranslationOverF256_apply_galoisBaseZ

/-- The literal involution `x₀ ↦ x₀ + 1`, regarded as an automorphism over
the fixed source base `F256(z)`. -/
noncomputable def sourceSeedOneTranslation :
    RatFunc F256 ≃ₐ[GaloisBaseField] RatFunc F256 where
  __ := sourceSeedOneTranslationOverF256.toRingEquiv
  commutes' a := by
    exact DFunLike.congr_fun
      sourceSeedOneTranslationOverF256_fixes_galoisBase a

/-- The fixed-base seed translation has its literal action on `x₀`. -/
theorem sourceSeedOneTranslation_apply_X :
    sourceSeedOneTranslation RatFunc.X = RatFunc.X + 1 :=
  sourceSeedOneTranslationOverF256_apply_X

/-- The seed translation fixes `w = x₀^16 + x₀`. -/
theorem sourceSeedOneTranslation_apply_galoisBaseW :
    sourceSeedOneTranslation galoisBaseW = galoisBaseW :=
  sourceSeedOneTranslationOverF256_apply_galoisBaseW

/-- The seed translation lifted through normality to source closure level
`m`, using the actual seed embedding rather than the standard rational
presentation of the base parameter. -/
noncomputable def sourceGaloisSeedOneTranslation (m : ℕ) :
    SourceGaloisClosureField m ≃ₐ[GaloisBaseField]
      SourceGaloisClosureField m := by
  let seedAlgebra : Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
    (sourceGaloisSeedRatFuncToClosure m).toRingHom.toAlgebra
  letI seedSMul : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
    seedAlgebra.toSMul
  letI seedAlgebraInstance : Algebra (RatFunc F256)
      (SourceGaloisClosureField m) := seedAlgebra
  letI seedModule : Module (RatFunc F256) (SourceGaloisClosureField m) :=
    @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
      seedAlgebraInstance
  letI seedTower : IsScalarTower GaloisBaseField (RatFunc F256)
      (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      change algebraMap GaloisBaseField (SourceGaloisClosureField m) a =
        sourceGaloisSeedRatFuncToClosure m
          (algebraMap GaloisBaseField (RatFunc F256) a)
      exact (sourceGaloisSeedRatFuncToClosure m).commutes a |>.symm)
  exact sourceSeedOneTranslation.liftNormal (SourceGaloisClosureField m)

/-- The lifted translation sends the actual seed coordinate to `x₀ + 1`.
-/
theorem sourceGaloisSeedOneTranslation_apply_coordinate (m : ℕ) :
    sourceGaloisSeedOneTranslation m (sourceGaloisSeedCoordinate m) =
      sourceGaloisSeedCoordinate m + 1 := by
  let seedAlgebra : Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
    (sourceGaloisSeedRatFuncToClosure m).toRingHom.toAlgebra
  letI seedSMul : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
    seedAlgebra.toSMul
  letI seedAlgebraInstance : Algebra (RatFunc F256)
      (SourceGaloisClosureField m) := seedAlgebra
  letI seedModule : Module (RatFunc F256) (SourceGaloisClosureField m) :=
    @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
      seedAlgebraInstance
  letI seedTower : IsScalarTower GaloisBaseField (RatFunc F256)
      (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      change algebraMap GaloisBaseField (SourceGaloisClosureField m) a =
        sourceGaloisSeedRatFuncToClosure m
          (algebraMap GaloisBaseField (RatFunc F256) a)
      exact (sourceGaloisSeedRatFuncToClosure m).commutes a |>.symm)
  change sourceSeedOneTranslation.liftNormal (SourceGaloisClosureField m)
      (algebraMap (RatFunc F256) (SourceGaloisClosureField m) RatFunc.X) =
    algebraMap (RatFunc F256) (SourceGaloisClosureField m) RatFunc.X + 1
  rw [AlgEquiv.liftNormal_commutes, sourceSeedOneTranslation_apply_X,
    map_add, map_one]

/-- The lifted translation fixes the actual embedded `w` generator. -/
theorem sourceGaloisSeedOneTranslation_apply_w (m : ℕ) :
    sourceGaloisSeedOneTranslation m
        (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) := by
  let seedAlgebra : Algebra (RatFunc F256) (SourceGaloisClosureField m) :=
    (sourceGaloisSeedRatFuncToClosure m).toRingHom.toAlgebra
  letI seedSMul : SMul (RatFunc F256) (SourceGaloisClosureField m) :=
    seedAlgebra.toSMul
  letI seedAlgebraInstance : Algebra (RatFunc F256)
      (SourceGaloisClosureField m) := seedAlgebra
  letI seedModule : Module (RatFunc F256) (SourceGaloisClosureField m) :=
    @Algebra.toModule (RatFunc F256) (SourceGaloisClosureField m) _ _
      seedAlgebraInstance
  letI seedTower : IsScalarTower GaloisBaseField (RatFunc F256)
      (SourceGaloisClosureField m) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro a
      change algebraMap GaloisBaseField (SourceGaloisClosureField m) a =
        sourceGaloisSeedRatFuncToClosure m
          (algebraMap GaloisBaseField (RatFunc F256) a)
      exact (sourceGaloisSeedRatFuncToClosure m).commutes a |>.symm)
  change sourceSeedOneTranslation.liftNormal (SourceGaloisClosureField m)
      (algebraMap (RatFunc F256) (SourceGaloisClosureField m) galoisBaseW) =
    algebraMap (RatFunc F256) (SourceGaloisClosureField m) galoisBaseW
  rw [AlgEquiv.liftNormal_commutes,
    sourceSeedOneTranslation_apply_galoisBaseW]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

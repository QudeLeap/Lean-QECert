import QEC.Coding.AlgebraicGeometry.Towers.TraceRefinement
import QEC.Coding.AlgebraicGeometry.Towers.BasicProjectionFields

/-!
# Normalized refinements of the actual basic rational projections

The rational source parameter is normalized at every place. The trace
coordinates give the normalized chains used in the source's Property-(A)
pyramid, in addition to their weak-different consequence.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem adjoin_simple_gen_eq_top
    {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E] (y : E) :
    F⟮AdjoinSimple.gen F y⟯ = ⊤ := by
  apply IntermediateField.map_injective (F⟮y⟯).val
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map]
  change F⟮y⟯ = (F⟮y⟯).val.fieldRange
  exact (IntermediateField.fieldRange_val _).symm

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

/-- The literal additive extension, with normalization checked on the
initial field rather than its bottom-subfield copy. -/
theorem artinSchreier16_bottom_normalizedRefinement
    (a : F) (y : E) (hy : y ^ 16 + y = algebraMap F E a)
    (ha : ∀ P : GlobalPlace F256 F, P.order a = -1 ∨ 0 ≤ P.order a) :
    NormalizedRefinement A F E Q ⊥ F⟮y⟯ := by
  let K : IntermediateField F E := ⊥
  let a' : K := algebraMap F K a
  let P := heightOnePlace (k := F256) (K := K)
    (IntermediateIntegralModels.prime A F E Q K)
  let e : F ≃ₐ[F256] K := (IntermediateField.botEquiv F E).symm.restrictScalars F256
  have he : e a = a' := IntermediateField.botEquiv_symm a
  have ha' : P.order a' = -1 ∨ 0 ≤ P.order a' := by
    have h := ha (GlobalPlace.comapAlgEquiv e P)
    simpa only [GlobalPlace.comapAlgEquiv_order, he] using h
  have h := artinSchreier16_normalizedRefinement A Q K a' y hy ha'
  simpa only [K, IntermediateField.restrictScalars_adjoin_eq_sup, bot_sup_eq] using h

end

section Rational

variable {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : Transcendental F256 x) (y : E)
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F256⟮x⟯] [IsFractionRing A F256⟮x⟯]
    [Algebra A E] [IsScalarTower A F256⟮x⟯ E]
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

include hx in
/-- Property (A)'s actual normalized chain on a rational basic projection,
already embedded in the supplied finite ambient field. The lower order
alternative is derived from the source rational function at every place. -/
theorem sourceBasicRationalProjection_normalizedRefinement
    (hy : y ^ 16 + y = algebraMap F256⟮x⟯ E
      (sourceStepRhs (AdjoinSimple.gen F256 x))) :
    NormalizedRefinement A F256⟮x⟯ E Q ⊥ (F256⟮x⟯)⟮y⟯ :=
  artinSchreier16_bottom_normalizedRefinement A F256⟮x⟯ E Q
    (sourceStepRhs (AdjoinSimple.gen F256 x)) y hy
    (sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy x hx)

end Rational

noncomputable section

/-- The four normalized trace steps in the actual forward basic extension.
The ambient carrier and its finite separable structure are the already
constructed source fields; no different or normalized higher-tower input
is required. -/
theorem sourceBasicForward_normalizedRefinement
    (i : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (SourceBasicForwardField i)] [IsFractionRing A (SourceBasicForwardField i)]
    [Algebra A (SourceBasicForwardExtensionField i)]
    [IsScalarTower A (SourceBasicForwardField i) (SourceBasicForwardExtensionField i)]
    [Module.Finite A (integralClosure A (SourceBasicForwardExtensionField i))]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure A (SourceBasicForwardExtensionField i))) :
    NormalizedRefinement A (SourceBasicForwardField i) (SourceBasicForwardExtensionField i)
      Q ⊥ ⊤ := by
  let y := AdjoinSimple.gen (SourceBasicForwardField i) (sourceDistinguishedCoordinate (i + 1))
  have hy : y ^ 16 + y = algebraMap (SourceBasicForwardField i)
      (SourceBasicForwardExtensionField i)
      (sourceStepRhs (AdjoinSimple.gen F256
        (sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)))) := by
    apply Subtype.ext
    exact sourceBasicForward_root_equation i
  have h := artinSchreier16_bottom_normalizedRefinement A (SourceBasicForwardField i)
    (SourceBasicForwardExtensionField i) Q _ y hy
    (sourceBasicForwardEmbedded_rhs_order_dichotomy i)
  rwa [adjoin_simple_gen_eq_top] at h

/-- The inverse-coordinate orientation gives a normalized chain on the
same source basic cell, now over the actual reverse rational field. -/
theorem sourceBasicReverse_normalizedRefinement
    (i : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (SourceBasicReverseField i)] [IsFractionRing A (SourceBasicReverseField i)]
    [Algebra A (SourceBasicReverseExtensionField i)]
    [IsScalarTower A (SourceBasicReverseField i) (SourceBasicReverseExtensionField i)]
    [Module.Finite A (integralClosure A (SourceBasicReverseExtensionField i))]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure A (SourceBasicReverseExtensionField i))) :
    NormalizedRefinement A (SourceBasicReverseField i) (SourceBasicReverseExtensionField i)
      Q ⊥ ⊤ := by
  let x := (sourceDistinguishedCoordinate (i + 1))⁻¹
  have hx : Transcendental F256 x := by
    intro halg
    exact sourceBasicSourceCoordinate_transcendental (i + 1) (IsAlgebraic.inv_iff.mp halg)
  let y := AdjoinSimple.gen (SourceBasicReverseField i)
    (sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹))
  have hy : y ^ 16 + y = algebraMap (SourceBasicReverseField i)
      (SourceBasicReverseExtensionField i) (sourceStepRhs (AdjoinSimple.gen F256 x)) := by
    apply Subtype.ext
    exact sourceBasicReverse_root_equation i
  have h := artinSchreier16_bottom_normalizedRefinement A (SourceBasicReverseField i)
    (SourceBasicReverseExtensionField i) Q _ y hy
    (sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy x hx)
  rwa [adjoin_simple_gen_eq_top] at h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

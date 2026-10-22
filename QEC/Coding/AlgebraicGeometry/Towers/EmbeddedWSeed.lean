import QEC.Coding.AlgebraicGeometry.Towers.EmbeddedSourceCoordinates
import QEC.Coding.AlgebraicGeometry.Towers.RationalTraceSeed

/-!
# The actual w-rooted source chain in a finite ambient extension

The source's F9 chain begins at `k(w)`, not at `k(x₀)` or at a later normal
closure level. This file prepends the literal additive trace seed to the
already proved embedded source-coordinate chain.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

/-- A transcendental rational generator has only regular places and its
simple pole, with normalized order measured on the actual generated field. -/
theorem rationalGenerator_order_dichotomy (w : E) (hw : Transcendental F256 w)
    (P : GlobalPlace F256 F256⟮w⟯) :
    P.order (AdjoinSimple.gen F256 w) = -1 ∨ 0 ≤ P.order (AdjoinSimple.gen F256 w) := by
  have h := rationalPlace_order_X_dichotomy
    (GlobalPlace.comapAlgEquiv (RatFunc.algEquivOfTranscendental w hw) P)
  have heq : RatFunc.algEquivOfTranscendental w hw RatFunc.X = AdjoinSimple.gen F256 w := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X w hw
  simpa only [GlobalPlace.comapAlgEquiv_order, heq] using h

/-- The actual additive seed, with no different or trace-normalization
input: these follow from the literal rational generator `w`. -/
theorem rationalAdditiveSeed_normalized (Q : GlobalPlace F256 E) (w x : E)
    (hw : Transcendental F256 w) (hx : x ^ 16 + x = w)
    [FiniteDimensional F256⟮w⟯ E] [Algebra.IsSeparable F256⟮w⟯ E] :
    PlaceNormalizedExtension Q F256⟮w⟯ F256⟮x⟯ := by
  have hle : F256⟮w⟯ ≤ F256⟮x⟯ := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z = w := Set.mem_singleton_iff.mp hz
    subst z
    rw [← hx]
    exact (F256⟮x⟯).add_mem ((F256⟮x⟯).toSubalgebra.pow_mem (mem_adjoin_simple_self F256 x) 16)
      (mem_adjoin_simple_self F256 x)
  refine ⟨hle, ?_⟩
  have h := artinSchreier16_bottom_normalizedRefinement
    (AmbientPlaceModels.baseRing F256⟮w⟯ Q) F256⟮w⟯ E (AmbientPlaceModels.prime F256⟮w⟯ Q)
    (AdjoinSimple.gen F256 w) x hx (rationalGenerator_order_dichotomy w hw)
  have heq : (F256⟮w⟯)⟮x⟯ = IntermediateField.extendScalars hle := by
    apply IntermediateField.restrictScalars_injective F256
    rw [IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.extendScalars_restrictScalars, sup_eq_right.mpr hle]
  rwa [heq] at h

end

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (m : ℕ) {E : Type*} [_root_.Field E] [Algebra F256 E]
    [Algebra (SourceField m) E] [IsScalarTower F256 (SourceField m) E]
    [FiniteDimensional (SourceField m) E] [Algebra.IsSeparable (SourceField m) E]

/-- Finiteness and separability over the image of the actual rational
`w`-field are derived from the existing additive seed and source extension. -/
theorem embeddedSourceW_finite_separable :
    FiniteDimensional F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E ∧
    Algebra.IsSeparable F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E := by
  letI : Algebra (RatFunc F256) E :=
    ((algebraMap (SourceField m) E).comp (algebraMap (RatFunc F256) (SourceField m))).toAlgebra
  letI : IsScalarTower (RatFunc F256) (SourceField m) E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F256 (RatFunc F256) E := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    change algebraMap F256 E c = algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) (algebraMap F256 (RatFunc F256) c))
    rw [← IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceField m),
      ← IsScalarTower.algebraMap_apply F256 (SourceField m) E])
  letI : FiniteDimensional (RatFunc F256) E :=
    FiniteDimensional.trans (RatFunc F256) (SourceField m) E
  letI : Algebra.IsSeparable (RatFunc F256) E :=
    Algebra.IsSeparable.trans (RatFunc F256) (SourceField m) E
  letI : FiniteDimensional F256⟮galoisBaseW⟯ (RatFunc F256) :=
    inferInstanceAs (FiniteDimensional SourceGaloisWField (RatFunc F256))
  letI : Algebra.IsSeparable F256⟮galoisBaseW⟯ (RatFunc F256) :=
    inferInstanceAs (Algebra.IsSeparable SourceGaloisWField (RatFunc F256))
  have h := finite_separable_over_mapped_subfield (E := E) F256⟮galoisBaseW⟯
  have heq : (F256⟮galoisBaseW⟯).map (IsScalarTower.toAlgHom F256 (RatFunc F256) E) =
      F256⟮algebraMap (SourceField m) E
        (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [heq] at h
  exact h

scoped instance embeddedSourceW_finite :
    FiniteDimensional F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E :=
  (embeddedSourceW_finite_separable m).1

scoped instance embeddedSourceW_separable :
    Algebra.IsSeparable F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯ E :=
  (embeddedSourceW_finite_separable m).2

/-- The entire original source chain, rooted at its literal `k(w)` image
and ending at the whole source field range, at one fixed ambient place. -/
theorem embeddedSourceW_normalized (Q : GlobalPlace F256 E) [Finite Q.residueField] :
    PlaceNormalizedExtension Q F256⟮algebraMap (SourceField m) E
      (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)⟯
      (IsScalarTower.toAlgHom F256 (SourceField m) E).fieldRange := by
  let f := IsScalarTower.toAlgHom F256 (SourceField m) E
  let j := f.comp (IsScalarTower.toAlgHom F256 (RatFunc F256) (SourceField m))
  letI : FiniteDimensional F256⟮j galoisBaseW⟯ E := embeddedSourceW_finite m
  letI : Algebra.IsSeparable F256⟮j galoisBaseW⟯ E := embeddedSourceW_separable m
  have hw : Transcendental F256 (j galoisBaseW) := fun ha =>
    sourceGaloisBaseW_transcendental ((isAlgebraic_algHom_iff j j.injective).mp ha)
  have hseed := rationalAdditiveSeed_normalized Q (j galoisBaseW)
    (algebraMap (SourceField m) E (sourceCoordinates m 0)) hw (by
      rw [sourceCoordinates_zero]
      change j RatFunc.X ^ 16 + j RatFunc.X = j galoisBaseW
      simp only [galoisBaseW, map_add, map_pow])
  exact PlaceNormalizedExtension.trans Q hseed (embeddedSourceCoordinates_normalized m Q)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

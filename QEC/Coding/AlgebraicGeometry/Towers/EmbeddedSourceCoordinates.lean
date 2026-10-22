import QEC.Coding.AlgebraicGeometry.Towers.SourceCoordinates

/-!
# Literal source-coordinate chains in a finite ambient extension

The ambient place stays fixed while the source field is embedded into it.
Both basic projections are evaluated on the actual embedded coordinates;
their full window is proved to be the embedding's field range.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable {F E : Type*} [_root_.Field F] [_root_.Field E]
    [Algebra F256 F] [Algebra F256 E] [Algebra F E] [IsScalarTower F256 F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The finite separable extension over an actual subfield survives its
literal embedding into the ambient field. No ramification premise occurs. -/
theorem finite_separable_over_mapped_subfield (K : IntermediateField F256 F)
    [FiniteDimensional K F] [Algebra.IsSeparable K F] :
    FiniteDimensional (K.map (IsScalarTower.toAlgHom F256 F E)) E ∧
      Algebra.IsSeparable (K.map (IsScalarTower.toAlgHom F256 F E)) E := by
  let f := IsScalarTower.toAlgHom F256 F E
  let j : K →ₐ[F256] E := f.comp K.val
  let J := j.fieldRange
  letI : Algebra K E := j.toRingHom.toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K E := FiniteDimensional.trans K F E
  letI : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K F E
  let jJ : K →ₐ[F256] J := j.codRestrict J.toSubalgebra (fun x => ⟨x, rfl⟩)
  letI : Algebra K J := jJ.toRingHom.toAlgebra
  letI : IsScalarTower K J E := IsScalarTower.of_algebraMap_eq' rfl
  have hresult : FiniteDimensional J E ∧ Algebra.IsSeparable J E :=
    ⟨Module.Finite.of_restrictScalars_finite K J E,
      Algebra.isSeparable_tower_top_of_isSeparable K J E⟩
  have hJ : J = K.map f := by
    change (f.comp K.val).fieldRange = K.map f
    rw [← AlgHom.map_fieldRange, IntermediateField.fieldRange_val]
  rw [hJ] at hresult
  exact hresult

end

noncomputable section

variable (m : ℕ) {E : Type*} [_root_.Field E] [Algebra F256 E]
    [Algebra (SourceField m) E] [IsScalarTower F256 (SourceField m) E]
    [FiniteDimensional (SourceField m) E] [Algebra.IsSeparable (SourceField m) E]

/-- All embedded coordinate fields are genuine finite separable bases of
the ambient extension, by the proved source-coordinate results. -/
theorem embeddedSourceCoordinates_finite_separable (i : ℕ) :
    FiniteDimensional F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E ∧
      Algebra.IsSeparable F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E := by
  have h := finite_separable_over_mapped_subfield (E := E) F256⟮sourceCoordinates m i⟯
  have heq : (F256⟮sourceCoordinates m i⟯).map (IsScalarTower.toAlgHom F256 (SourceField m) E) =
      F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [heq] at h
  exact h

scoped instance embeddedSourceCoordinates_finite (i : ℕ) :
    FiniteDimensional F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E :=
  (embeddedSourceCoordinates_finite_separable m i).1

scoped instance embeddedSourceCoordinates_separable (i : ℕ) :
    Algebra.IsSeparable F256⟮algebraMap (SourceField m) E (sourceCoordinates m i)⟯ E :=
  (embeddedSourceCoordinates_finite_separable m i).2

/-- The whole source chain inside a finite ambient extension. It starts
at the actual image of `k(x₀)` and ends at the whole source field range. -/
theorem embeddedSourceCoordinates_normalized
    (Q : GlobalPlace F256 E) [Finite Q.residueField] :
    PlaceNormalizedExtension Q
      F256⟮algebraMap (SourceField m) E (sourceCoordinates m 0)⟯
      (IsScalarTower.toAlgHom F256 (SourceField m) E).fieldRange := by
  let f := IsScalarTower.toAlgHom F256 (SourceField m) E
  let x := fun i => f (sourceCoordinates m i)
  letI : ∀ i, FiniteDimensional F256⟮x i⟯ E := fun i => embeddedSourceCoordinates_finite m i
  letI : ∀ i, Algebra.IsSeparable F256⟮x i⟯ E := fun i => embeddedSourceCoordinates_separable m i
  have hx (i : ℕ) : Transcendental F256 (x i) := by
    intro ha
    exact sourceCoordinates_transcendental m i ((isAlgebraic_algHom_iff f f.injective).mp ha)
  have hrec (i : ℕ) (hi : i < m) : x (i + 1) ^ 16 + x (i + 1) = sourceStepRhs (x i) := by
    simpa only [x, map_pow, map_add, sourceStepRhs, map_div₀, map_one] using
      congrArg f (sourceCoordinates_recursion m i hi)
  have h := rationalCoordinateWindow_normalized Q x hx m hrec
  have htop : coordinateWindow x 0 m = f.fieldRange := by
    rw [← coordinateWindow_map f (sourceCoordinates m), sourceCoordinates_window_eq_top,
      ← AlgHom.fieldRange_eq_map]
  rwa [htop] at h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

import QEC.Coding.AlgebraicGeometry.Towers.CoordinateWindows

/-!
# Basic cells on the literal source coordinates

The two incoming normalized chains in the source pyramid are derived here
from its displayed recursion, in the actual ambient field. The reverse
projection uses inverse coordinates and has the same two-coordinate carrier.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem coordinate_adjoin_inv (x : E) : F256⟮x⁻¹⟯ = F256⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z = x⁻¹ := Set.mem_singleton_iff.mp hz
    subst z
    exact (F256⟮x⟯).inv_mem (mem_adjoin_simple_self F256 x)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    have hmem := (F256⟮x⁻¹⟯).inv_mem (mem_adjoin_simple_self F256 x⁻¹)
    simp only [inv_inv] at hmem
    exact hmem

omit [Algebra F256 E] in
/-- The inverse-coordinate recursion is an algebraic consequence of the
source's displayed equation; it is not a second assumed projection. -/
theorem rationalRecursion_reverse {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 16 + y = sourceStepRhs x) :
    x⁻¹ ^ 16 + x⁻¹ = sourceStepRhs y⁻¹ := by
  have hleft : (sourceStepRhs x)⁻¹ = x⁻¹ ^ 16 + x⁻¹ := by
    rw [sourceStepRhs, inv_div]
    field_simp [hx]
    ring
  have hright : sourceStepRhs y⁻¹ = (y ^ 16 + y)⁻¹ := by
    rw [sourceStepRhs]
    field_simp [hy]
    ring
  rw [hright, h, hleft]

/-- The forward basic projection, in the literal two-coordinate field. -/
theorem rationalCoordinate_forward_normalized
    (Q : GlobalPlace F256 E) (x y : E) (hx : Transcendental F256 x)
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    (h : y ^ 16 + y = sourceStepRhs x) :
    PlaceNormalizedExtension Q F256⟮x⟯ (F256⟮x⟯ ⊔ F256⟮y⟯) := by
  refine ⟨le_sup_left, ?_⟩
  have hc := sourceBasicRationalProjection_normalizedRefinement x hx y
    (AmbientPlaceModels.baseRing F256⟮x⟯ Q) (AmbientPlaceModels.prime F256⟮x⟯ Q) h
  have heq : (F256⟮x⟯)⟮y⟯ =
      IntermediateField.extendScalars (show F256⟮x⟯ ≤ F256⟮x⟯ ⊔ F256⟮y⟯ from le_sup_left) := by
    apply IntermediateField.restrictScalars_injective F256
    rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    rfl
  rwa [heq] at hc

/-- The reverse basic projection is derived from the same displayed
equation, then identified with the very same two-coordinate field. -/
theorem rationalCoordinate_reverse_normalized
    (Q : GlobalPlace F256 E) (x y : E)
    (hx : Transcendental F256 x) (hy : Transcendental F256 y)
    [FiniteDimensional F256⟮y⟯ E] [Algebra.IsSeparable F256⟮y⟯ E]
    (h : y ^ 16 + y = sourceStepRhs x) :
    PlaceNormalizedExtension Q F256⟮y⟯ (F256⟮x⟯ ⊔ F256⟮y⟯) := by
  have hx0 : x ≠ 0 := fun heq => hx (heq ▸ isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun heq => hy (heq ▸ isAlgebraic_zero)
  have hyinv : Transcendental F256 y⁻¹ := fun ha => hy (IsAlgebraic.inv_iff.mp ha)
  letI : FiniteDimensional F256⟮y⁻¹⟯ E := by rw [coordinate_adjoin_inv]; infer_instance
  letI : Algebra.IsSeparable F256⟮y⁻¹⟯ E := by rw [coordinate_adjoin_inv]; infer_instance
  have hr := rationalCoordinate_forward_normalized Q y⁻¹ x⁻¹ hyinv
    (rationalRecursion_reverse hx0 hy0 h)
  simpa only [coordinate_adjoin_inv, sup_comm] using hr

/-- The literal basic cell is finite and separable over its rational
coordinate base, by its already constructed degree-sixteen source model. -/
theorem rationalCoordinate_adjoin_finite_separable (x y : E)
    (hx : Transcendental F256 x) (h : y ^ 16 + y = sourceStepRhs x) :
    FiniteDimensional F256⟮x⟯ (F256⟮x⟯)⟮y⟯ ∧
      Algebra.IsSeparable F256⟮x⟯ (F256⟮x⟯)⟮y⟯ := by
  let P := sourceBasicRationalInfinityPlace x hx
  let t := AdjoinSimple.gen F256 x
  have ht : P.order t = -1 := sourceBasicRationalInfinityPlace_order_gen x hx
  have hd := sourceStepLiteral_adjoin_finrank P t ht y h
  let e := sourceStepLiteralAdjoinEquiv P t ht y h
  exact ⟨Module.finite_of_finrank_pos (by rw [hd]; norm_num),
    Algebra.IsSeparable.of_algHom F256⟮x⟯ (SourceStepField P t ht) e.symm.toAlgHom⟩

/-- The finite separable ambient extension can be viewed over the next
actual coordinate field. Its proof uses the reverse basic cell, not an
assumed common rational subfield of all coordinate windows. -/
theorem rationalRecursion_next_finite_separable (x y : E)
    (hx : Transcendental F256 x) (hy : Transcendental F256 y)
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    (h : y ^ 16 + y = sourceStepRhs x) :
    FiniteDimensional F256⟮y⟯ E ∧ Algebra.IsSeparable F256⟮y⟯ E := by
  have hx0 : x ≠ 0 := fun heq => hx (heq ▸ isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun heq => hy (heq ▸ isAlgebraic_zero)
  have hyinv : Transcendental F256 y⁻¹ := fun ha => hy (IsAlgebraic.inv_iff.mp ha)
  let K := F256⟮y⁻¹⟯
  let T := K⟮x⁻¹⟯
  obtain ⟨hfinite, hsep⟩ := rationalCoordinate_adjoin_finite_separable y⁻¹ x⁻¹ hyinv
    (rationalRecursion_reverse hx0 hy0 h)
  letI : FiniteDimensional K T := hfinite
  letI : Algebra.IsSeparable K T := hsep
  have hle : F256⟮x⟯ ≤ T.restrictScalars F256 := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, coordinate_adjoin_inv]
    exact le_sup_right
  letI : Algebra F256⟮x⟯ T := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : IsScalarTower F256⟮x⟯ T E := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional T E := Module.Finite.of_restrictScalars_finite F256⟮x⟯ T E
  letI : Algebra.IsSeparable T E := Algebra.isSeparable_tower_top_of_isSeparable F256⟮x⟯ T E
  have hresult : FiniteDimensional K E ∧ Algebra.IsSeparable K E :=
    ⟨FiniteDimensional.trans K T E, Algebra.IsSeparable.trans K T E⟩
  change FiniteDimensional F256⟮y⁻¹⟯ E ∧ Algebra.IsSeparable F256⟮y⁻¹⟯ E at hresult
  rw [coordinate_adjoin_inv y] at hresult
  exact hresult

/-- The complete source pyramid for literal recursion coordinates. The
displayed source equations provide both basic projections, so no
normalized higher-window input remains. -/
theorem rationalCoordinateWindow_normalized
    (Q : GlobalPlace F256 E) [Finite Q.residueField]
    (x : ℕ → E) [∀ a, FiniteDimensional F256⟮x a⟯ E]
    [∀ a, Algebra.IsSeparable F256⟮x a⟯ E]
    (hx : ∀ a, Transcendental F256 (x a)) (N : ℕ)
    (hrec : ∀ a, a < N → x (a + 1) ^ 16 + x (a + 1) = sourceStepRhs (x a)) :
    PlaceNormalizedExtension Q F256⟮x 0⟯ (coordinateWindow x 0 N) := by
  apply coordinateWindow_normalized_prefix Q x N _ N le_rfl
  intro a ha
  constructor
  · exact rationalCoordinate_forward_normalized Q (x a) (x (a + 1)) (hx a) (hrec a ha)
  · exact rationalCoordinate_reverse_normalized Q (x a) (x (a + 1))
      (hx a) (hx (a + 1)) (hrec a ha)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

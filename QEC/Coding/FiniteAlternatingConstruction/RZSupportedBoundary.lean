import QEC.Coding.FiniteAlternatingConstruction.RZConcreteParity
import QEC.Coding.FourDimensionalToricCode.Decoder.RZCoarseGraining

/-!
# Supported RZ Z-block boundary exactness

Restriction and zero extension identify the actual supported ambient spaces
with the cylinder coordinates. Graph connectivity then identifies the boundary
range with the region-parity kernel and gives its explicit quotient chart.
-/

namespace QEC.Coding.BDL26RZSupportedBoundary

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26RZConcreteParity
open MultiscaleDecoder
open MultiscaleDecoder.RZCoarseGraining.RZCoarseGrainingData
open scoped Classical BigOperators

/-- The actual ambient correction region owned by the old Z coordinate. -/
noncomputable def correctionRegion (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : Finset (RZQ P S) :=
  fiberRegion (rzCorrectionOwner P S) (.z z)

noncomputable abbrev correctionSpace (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) := supportedSubmodule (correctionRegion P S z)

noncomputable abbrev topSpace (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) := supportedSubmodule (blockRegion P S z)

/-- Zero extension satisfies the actual owner-region support condition. -/
theorem extendEdge_supported (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (e : Word BDL26Field (ZDoubleCylinderEdge P z S)) :
    extendZEdgeWord P S z e ∈ correctionSpace P S z := by
  intro p hp
  rcases p with ⟨w,edge⟩ | ⟨q,v⟩
  · by_cases h : w = z
    · subst w
      apply False.elim
      apply hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · simp [extendZEdgeWord, h]
  · rfl

theorem extendVertex_supported (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (r : Word BDL26Field (ZDoubleCylinderVertex P z S)) :
    extendZVertexWord P S z r ∈ topSpace P S z := by
  intro p hp
  rcases p with ⟨w,v⟩
  by_cases h : w = z
  · subst w
    exact False.elim (hp (by simp [blockRegion, fiberRegion]))
  · simp [extendZVertexWord, h]

/-- Restriction to actual Z edges, inverse to their ambient zero extension. -/
noncomputable def correctionEquiv (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : correctionSpace P S z ≃ₗ[BDL26Field]
      Word BDL26Field (ZDoubleCylinderEdge P z S) where
  toFun e edge := e.1 (Sum.inl ⟨z,edge⟩)
  invFun e := ⟨extendZEdgeWord P S z e, extendEdge_supported P S z e⟩
  left_inv e := by
    apply Subtype.ext
    funext p
    rcases p with ⟨w,edge⟩ | ⟨q,v⟩
    · change (if h : w = z then e.1 (Sum.inl ⟨z,h ▸ edge⟩) else 0) =
        e.1 (Sum.inl ⟨w,edge⟩)
      by_cases h : w = z
      · subst w
        simp
      · rw [dif_neg h]
        symm
        apply e.2
        intro hm
        have ho := (Finset.mem_filter.mp hm).2
        change Vertex.z w = Vertex.z z at ho
        exact h (Vertex.z.inj ho)
    · change 0 = e.1 (Sum.inr ⟨q,v⟩)
      symm
      apply e.2
      intro hm
      have ho := (Finset.mem_filter.mp hm).2
      change Vertex.q q = Vertex.z z at ho
      cases ho
  right_inv e := by funext edge; simp [extendZEdgeWord]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to actual Z vertices, inverse to their ambient zero extension. -/
noncomputable def topEquiv (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : topSpace P S z ≃ₗ[BDL26Field]
      Word BDL26Field (ZDoubleCylinderVertex P z S) where
  toFun r v := r.1 ⟨z,v⟩
  invFun r := ⟨extendZVertexWord P S z r, extendVertex_supported P S z r⟩
  left_inv r := by
    apply Subtype.ext
    funext p
    rcases p with ⟨w,v⟩
    by_cases h : w = z
    · subst w
      simp [extendZVertexWord]
    · change (if h : w = z then r.1 ⟨z,h ▸ v⟩ else 0) = r.1 ⟨w,v⟩
      rw [dif_neg h]
      symm
      exact r.2 _ (by simp [blockRegion, fiberRegion, h])
  right_inv r := by funext v; simp [extendZVertexWord]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every supported correction is its actual coordinate restriction extended. -/
theorem correction_extend_restrict (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (e : correctionSpace P S z) :
    extendZEdgeWord P S z (correctionEquiv P S z e) = e.1 :=
  congrArg Subtype.val ((correctionEquiv P S z).symm_apply_apply e)

/-- The actual successor coboundary preserves these concrete supported spaces. -/
theorem coboundary_supported (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (e : correctionSpace P S z) :
    tannerCoboundary1 (rzReplacementPresentation P A.toTannerSquareAdmissible S)
      e.1 ∈ topSpace P S z := by
  rw [← correction_extend_restrict P S z e, rzCoboundary1_extendZEdgeWord]
  exact extendVertex_supported P S z _

/-- Restriction of the actual successor coboundary, with derived support. -/
noncomputable def boundary (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    correctionSpace P S z →ₗ[BDL26Field] topSpace P S z where
  toFun e := ⟨tannerCoboundary1
    (rzReplacementPresentation P A.toTannerSquareAdmissible S) e.1,
    coboundary_supported P A S z e⟩
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul _ _ _

/-- The supported ambient boundary is conjugate to the genuine graph boundary. -/
theorem boundary_coordinates (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (e : correctionSpace P S z) :
    topEquiv P S z (boundary P A S z e) =
      rzCzGraphBoundary P z S (correctionEquiv P S z e) := by
  change (fun v => tannerCoboundary1
    (rzReplacementPresentation P A.toTannerSquareAdmissible S) e.1 ⟨z,v⟩) = _
  rw [← correction_extend_restrict P S z e, rzCoboundary1_extendZEdgeWord]
  funext v
  simp [extendZVertexWord]

/-- Region parity on the actual supported top space. -/
noncomputable def parity (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) : topSpace P S z →ₗ[BDL26Field] BDL26Field :=
  totalParity.comp (topEquiv P S z).toLinearMap

theorem parity_eq_region_sum (P : TannerSquarePresentation) (S : OddScale)
    (z : P.Z) (r : topSpace P S z) :
    parity P S z r = ∑ p ∈ blockRegion P S z, r.1 p := by
  exact blockParity_eq_region_sum P S r.1 z

/-- Connectivity of the actual local graph gives exactness in ambient support. -/
theorem boundary_range_eq_parity_ker (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    LinearMap.range (boundary P A S z) = LinearMap.ker (parity P S z) := by
  have hlocal : LinearMap.range (rzCzGraphBoundary P z S) =
      LinearMap.ker totalParity := by
    simpa only [rzCzTopCoboundary_eq_graphBoundary] using
      rzCzTopCoboundary_range_eq_totalParity_ker P A.toTannerSquareAdmissible z S
  ext r
  constructor
  · rintro ⟨e, rfl⟩
    change totalParity (topEquiv P S z (boundary P A S z e)) = 0
    rw [boundary_coordinates]
    exact LinearMap.mem_ker.mp (hlocal ▸
      (LinearMap.mem_range.mpr ⟨correctionEquiv P S z e, rfl⟩))
  · intro hr
    have hr' : topEquiv P S z r ∈ LinearMap.range (rzCzGraphBoundary P z S) := by
      rw [hlocal]
      exact hr
    obtain ⟨e, he⟩ := hr'
    refine ⟨(correctionEquiv P S z).symm e, ?_⟩
    apply (topEquiv P S z).injective
    rw [boundary_coordinates, LinearEquiv.apply_symm_apply]
    exact he

/-- The selected degree-two distinguished-root lift as a supported word. -/
noncomputable def supportedRootLift (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (b : BDL26Field) : topSpace P S z :=
  ⟨rootLift P A S z b, by
    intro p hp
    by_contra hn
    exact hp (rootLift_support P A S z b (by simpa [hammingSupport] using hn))⟩

theorem parity_rootLift (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (b : BDL26Field) : parity P S z (supportedRootLift P A S z b) = b := by
  change blockParity P S (map2Coord P A S (Pi.single z b)) z = b
  rw [blockParity_map2]
  simp

theorem parity_surjective (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    Function.Surjective (parity P S z) :=
  fun b => ⟨supportedRootLift P A S z b, parity_rootLift P A S z b⟩

abbrev topQuotient (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :=
  topSpace P S z ⧸ LinearMap.range (boundary P A S z)

/-- Explicit supported top quotient chart, derived from boundary exactness. -/
noncomputable def quotientEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z) :
    topQuotient P A S z ≃ₗ[BDL26Field] BDL26Field :=
  (Submodule.quotEquivOfEq _ _ (boundary_range_eq_parity_ker P A S z)).trans
    ((parity P S z).quotKerEquivOfSurjective (parity_surjective P A S z))

theorem quotientEquiv_mkQ (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (z : P.Z)
    (r : topSpace P S z) :
    quotientEquiv P A S z ((LinearMap.range (boundary P A S z)).mkQ r) =
      ∑ p ∈ blockRegion P S z, r.1 p := by
  simpa [quotientEquiv] using parity_eq_region_sum P S z r

end QEC.Coding.BDL26RZSupportedBoundary

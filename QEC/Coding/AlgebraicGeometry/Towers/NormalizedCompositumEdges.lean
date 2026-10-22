import QEC.Coding.AlgebraicGeometry.Towers.IntermediateIntegralModels
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticCompositumCell
import QEC.Coding.AlgebraicGeometry.Differents.RelativeTower

/-!
# Normalized generator edges in the literal compositum lattice

An edge records the source's equation `y² + y = a`, its generated subfield,
and normalization of `a` at the contraction of a fixed final prime. It does
not contain a different formula. The compositum theorem constructs the two
new normalized edges by the residue-square calculation of Lemma 1.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem adjoin_in_subfield_eq_top
    {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
    (K L : IntermediateField F E) [Fact (K ≤ L)]
    (z : E) (hz : z ∈ L) (hL : (K⟮z⟯).restrictScalars F = L) :
    K⟮(⟨z, hz⟩ : L)⟯ = ⊤ := by
  let f : L →ₐ[K] E := IsScalarTower.toAlgHom K L E
  apply IntermediateField.map_injective f
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map]
  apply IntermediateField.restrictScalars_injective F
  change (K⟮z⟯).restrictScalars F = f.fieldRange.restrictScalars F
  rw [hL]
  ext x
  change x ∈ L ↔ ∃ y : L, (y : E) = x
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q

/-- A literal normalized quadratic equation propagates normalized order to
its actual root, including degree-one stages of an embedded refinement. -/
theorem normalizedLiteralRoot_order
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) (P K)).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a) :
    (heightOnePlace (k := F256) (K := L) (P L)).order y = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := L) (P L)).order y := by
  have hdeg := literalQuadratic_finrank_eq_one_or_two a y hy hgen
  letI : FaithfulSMul (C K) (C L) :=
    Module.isTorsionFree_iff_faithfulSMul.mp
      (IntermediateIntegralModels.modelRelativeTorsionFree A F E K L)
  exact heightOnePlace_artinSchreier_order_dichotomy_of_finrank_le_two
    (P K) (P L) a y hy (by omega) ha

/-- The actual normalized equation and generated field of one quadratic
edge, allowing a redundant degree-one step. No ramification output is stored. -/
def NormalizedEdge (K L : IntermediateField F E) : Prop :=
  ∃ (a : K) (y : E),
    y ^ 2 + y = (a : E) ∧
    ((heightOnePlace (k := F256) (K := K) (P K)).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a) ∧
    (K⟮y⟯).restrictScalars F = L

theorem NormalizedEdge.le {K L : IntermediateField F E}
    (h : NormalizedEdge A F E Q K L) : K ≤ L := by
  obtain ⟨a, y, _, _, hL⟩ := h
  rw [← hL, IntermediateField.restrictScalars_adjoin_eq_sup]
  exact le_sup_left

/-- The literal identity edge is available at every intermediate field. -/
theorem normalizedEdge_refl (K : IntermediateField F E) :
    NormalizedEdge A F E Q K K := by
  refine ⟨0, 0, by simp, Or.inr ?_, ?_⟩
  · simp [GlobalPlace.order]
  · rw [IntermediateField.restrictScalars_adjoin_eq_sup]
    simp

/-- One side of the actual compositum square, including redundant steps.
The new generator is constructed in the fixed ambient field. -/
theorem NormalizedEdge.compositum_left
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedEdge A F E Q K L)
    (hRight : NormalizedEdge A F E Q K M) :
    NormalizedEdge A F E Q L (L ⊔ M) := by
  have hKL := hLeft.le A F E Q
  have hKM := hRight.le A F E Q
  letI : Fact (K ≤ L) := ⟨hKL⟩
  letI : Fact (K ≤ M) := ⟨hKM⟩
  let U := L ⊔ M
  letI : Fact (K ≤ U) := ⟨hKL.trans le_sup_left⟩
  letI : Fact (L ≤ U) := ⟨le_sup_left⟩
  obtain ⟨a, y, hy, ha, hL⟩ := hLeft
  obtain ⟨b, z, hz, hb, hM⟩ := hRight
  have hyL : y ∈ L := by
    rw [← hL]
    exact IntermediateField.mem_adjoin_simple_self K y
  have hzM : z ∈ M := by
    rw [← hM]
    exact IntermediateField.mem_adjoin_simple_self K z
  have hzU : z ∈ U := (show M ≤ U from le_sup_right) hzM
  have hU : (L⟮z⟯).restrictScalars F = U := by
    change (L⟮z⟯).restrictScalars F = L ⊔ M
    rw [← hM, IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.restrictScalars_adjoin_eq_sup, ← sup_assoc,
      sup_eq_left.mpr hKL]
  let yL : L := ⟨y, hyL⟩
  let zU : U := ⟨z, hzU⟩
  have hyEq : yL ^ 2 + yL = algebraMap K L a := by
    apply Subtype.ext
    exact hy
  have hzEq : zU ^ 2 + zU = algebraMap K U b := by
    apply Subtype.ext
    exact hz
  letI : Finite (heightOnePlace (k := F256) (K := K) (P K)).residueField :=
    IntermediateIntegralModels.modelResidueFieldFinite A F E K (P K)
  obtain ⟨c, hc, heq, _, _⟩ :=
    quadraticCompositumCell_normalized_weakDifferent_or_redundant
      A (C K) (C L) (C U) K L U (P K) (P L) (P U) a b yL zU
      hyEq hzEq (adjoin_in_subfield_eq_top K L y hyL hL)
      (adjoin_in_subfield_eq_top L U z hzU hU) ha hb
  refine ⟨algebraMap K L b + c ^ 2 + c, z + (c : E), ?_, hc, ?_⟩
  · exact congrArg (fun t : U => (t : E)) heq
  · change (L⟮z + algebraMap L E c⟯).restrictScalars F = U
    rw [adjoin_add_algebraMap_eq, hU]

/-- Both upper edges of the source's quadratic square are normalized at
the contractions of the same supplied final prime. -/
theorem NormalizedEdge.compositum
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedEdge A F E Q K L)
    (hRight : NormalizedEdge A F E Q K M) :
    NormalizedEdge A F E Q L (L ⊔ M) ∧
      NormalizedEdge A F E Q M (L ⊔ M) := by
  refine ⟨hLeft.compositum_left A F E Q hRight, ?_⟩
  simpa only [sup_comm] using hRight.compositum_left A F E Q hLeft

/-- A finite chain of the source's normalized quadratic generator edges. -/
abbrev NormalizedRefinement (K L : IntermediateField F E) : Prop :=
  Relation.ReflTransGen (NormalizedEdge A F E Q) K L

theorem NormalizedRefinement.le {K L : IntermediateField F E}
    (h : NormalizedRefinement A F E Q K L) : K ≤ L := by
  induction h with
  | refl => exact le_rfl
  | tail h hstep ih => exact ih.trans (hstep.le A F E Q)

/-- Sweep a single normalized edge through a finite normalized chain. Each
new upper edge is constructed by the preceding two-sided square theorem. -/
theorem NormalizedEdge.compositum_refinement
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedEdge A F E Q K L)
    (hRight : NormalizedRefinement A F E Q K M) :
    NormalizedRefinement A F E Q L (L ⊔ M) ∧
      NormalizedEdge A F E Q M (L ⊔ M) := by
  induction hRight with
  | refl =>
      rw [sup_eq_left.mpr (hLeft.le A F E Q)]
      exact ⟨.refl, hLeft⟩
  | @tail M N hchain hstep ih =>
      have hsquare := ih.2.compositum A F E Q hstep
      have hsup : (L ⊔ M) ⊔ N = L ⊔ N := by
        rw [sup_assoc, sup_eq_right.mpr (hstep.le A F E Q)]
      rw [hsup] at hsquare
      exact ⟨ih.1.tail hsquare.1, hsquare.2⟩

/-- The finite quadratic grid in Figures 1--2 of Garcia--Stichtenoth (2005):
two normalized lower chains yield normalized chains on both sides of their
literal compositum. The proof sweeps cells, not an assumed different law. -/
theorem NormalizedRefinement.compositum_left
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedRefinement A F E Q K L)
    (hRight : NormalizedRefinement A F E Q K M) :
    NormalizedRefinement A F E Q L (L ⊔ M) := by
  induction hLeft with
  | refl =>
      rw [sup_eq_right.mpr (hRight.le A F E Q)]
      exact hRight
  | @tail L N hchain hstep ih =>
      have h := (hstep.compositum_refinement A F E Q ih).1
      have hsup : N ⊔ (L ⊔ M) = N ⊔ M := by
        rw [← sup_assoc, sup_eq_left.mpr (hstep.le A F E Q)]
      rwa [hsup] at h

theorem NormalizedRefinement.compositum
    [Finite (IsLocalRing.ResidueField A)]
    {K L M : IntermediateField F E}
    (hLeft : NormalizedRefinement A F E Q K L)
    (hRight : NormalizedRefinement A F E Q K M) :
    NormalizedRefinement A F E Q L (L ⊔ M) ∧
      NormalizedRefinement A F E Q M (L ⊔ M) := by
  refine ⟨hLeft.compositum_left A F E Q hRight, ?_⟩
  simpa only [sup_comm] using hRight.compositum_left A F E Q hLeft

/-- The different law is a consequence of a normalized literal edge, not a
field of its definition. -/
theorem NormalizedEdge.weakDifferent
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : NormalizedEdge A F E Q K L) :
    multiplicity (P L).asIdeal (differentIdeal (C K) (C L)) =
      2 * ((P K).asIdeal.ramificationIdx' (P L).asIdeal - 1) := by
  obtain ⟨a, y, hy, ha, hL⟩ := h
  have hyL : y ∈ L := by
    rw [← hL]
    exact IntermediateField.mem_adjoin_simple_self K y
  let yL : L := ⟨y, hyL⟩
  have heq : yL ^ 2 + yL = algebraMap K L a := by
    apply Subtype.ext
    exact hy
  have hgen := adjoin_in_subfield_eq_top K L y hyL hL
  rcases literalQuadratic_finrank_eq_one_or_two a yL heq hgen with hdeg | hdeg
  · exact (ramificationIdx_and_weakDifferent_of_finrank_eq_one
      (C K) (C L) K L (P K) (P L) hdeg).2
  · exact quadraticLiteral_integralModel_weakDifferent
      A (C K) (C L) K L (P K) (P L) a yL heq hdeg hgen ha

/-- Transitivity computes the actual different over any finite normalized
chain at the contractions of the same final prime. -/
theorem NormalizedRefinement.weakDifferent
    {K L : IntermediateField F E}
    (h : NormalizedRefinement A F E Q K L) :
    letI : Fact (K ≤ L) := ⟨h.le A F E Q⟩
    multiplicity (P L).asIdeal (differentIdeal (C K) (C L)) =
      2 * ((P K).asIdeal.ramificationIdx' (P L).asIdeal - 1) := by
  induction h with
  | refl =>
      letI : Fact (K ≤ K) := ⟨le_rfl⟩
      exact self_weakDifferent (C K) (P K)
  | @tail L M hchain hstep ih =>
      letI : Fact (K ≤ L) := ⟨NormalizedRefinement.le A F E Q hchain⟩
      letI : Fact (L ≤ M) := ⟨hstep.le A F E Q⟩
      letI : Fact (K ≤ M) :=
        ⟨(NormalizedRefinement.le A F E Q hchain).trans (hstep.le A F E Q)⟩
      exact weakDifferent_tower_of_fractionFields
        (C K) (C L) (C M) K M (P K) (P L) (P M)
        ih (hstep.weakDifferent A F E Q)

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

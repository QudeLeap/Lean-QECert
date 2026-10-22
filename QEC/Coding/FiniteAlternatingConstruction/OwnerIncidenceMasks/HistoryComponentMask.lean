import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.HistoryWitness

/-! # Component-mask obstruction independent of every lower marking

The top marks are the exact three clauses evaluated on the actual top RZ
output. Every set of lower marks is allowed, so the statement does not depend
on any unresolved base-piece labelling convention.
-/
namespace QEC.Coding.BDL26OwnerIncidenceMasks

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

abbrev StrictLowerNode := Σ i : Fin 4, GraphVertex scaleFive i.val

noncomputable def includeLowerNode (v : StrictLowerNode) : BDL26TopOwnerIsolation.Node :=
  ⟨v.1.castSucc, v.2⟩

noncomputable def marksWithLower (lower : Finset StrictLowerNode) : Finset BDL26TopOwnerIsolation.Node :=
  witnessTopMarks.image BDL26TopOwnerIsolation.topNode ∪ lower.image includeLowerNode

theorem marksWithLower_top_iff (lower : Finset StrictLowerNode)
    (v : Vertex (state scaleFive 3).presentation) :
    BDL26TopOwnerIsolation.topNode v ∈ marksWithLower lower ↔ v ∈ witnessTopMarks := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with ht | hl
    · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp ht
      have hv : w = v := by cases he; rfl
      exact hv ▸ hw
    · obtain ⟨w, _, he⟩ := Finset.mem_image.mp hl
      have hv := congrArg (fun p : BDL26TopOwnerIsolation.Node => p.1.val) he
      change w.1.val = 4 at hv
      have hlt := w.1.isLt
      omega
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, h, rfl⟩)

theorem marksWithLower_only_z (lower : Finset StrictLowerNode) :
    BDL26TopOwnerIsolation.TopMarksAreZ (marksWithLower lower) := by
  intro v hv
  exact witnessTopMarks_only_z v ((marksWithLower_top_iff lower v).mp hv)

theorem marksWithLower_active (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    BDL26TopOwnerIsolation.topNode (witnessTopOwner p) ∈ marksWithLower lower :=
  (marksWithLower_top_iff lower _).mpr
    (outputMarks_contains_syndrome witnessTopOutput witnessTopOwner witnessTopComponentOwner p hp)

noncomputable def componentWithLower (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    Finset BDL26TopOwnerIsolation.Node :=
  (BDL26TopOwnerIsolation.markedComponent (marksWithLower lower)
    ⟨BDL26TopOwnerIsolation.topNode (witnessTopOwner p), marksWithLower_active lower p hp⟩).image Subtype.val

theorem componentWithLower_singleton (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    componentWithLower lower p hp = {BDL26TopOwnerIsolation.topNode (witnessTopOwner p)} := by
  have hn := witnessTopOwner_parent_none p hp
  unfold componentWithLower
  change parent scaleFive 3 (Vertex.z p.1) = none at hn
  exact BDL26TopOwnerIsolation.markedComponent_image_eq_singleton (marksWithLower lower)
    (marksWithLower_only_z lower) p.1 hn _

noncomputable def upperOwnerMaskRegion (K : Finset BDL26TopOwnerIsolation.Node) :
    Finset (FamilyZ scaleFive 4 (4 : LevelIndex 4)) :=
  Finset.univ.filter (fun q => BDL26TopOwnerIsolation.topNode (witnessTopOwner q) ∈ K)

noncomputable def lowerOwnerMaskRegion (K : Finset BDL26TopOwnerIsolation.Node) :
    Finset (FamilyZ scaleFive 4 (3 : LevelIndex 4)) :=
  Finset.univ.filter (fun q => (⟨(3 : Fin 5), witnessNextOwner q⟩ : BDL26TopOwnerIsolation.Node) ∈ K)

theorem componentWithLower_lower_empty (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    lowerOwnerMaskRegion (componentWithLower lower p hp) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have he := (Finset.mem_filter.mp hq).2
  rw [componentWithLower_singleton] at he
  have hv := congrArg (fun w : BDL26TopOwnerIsolation.Node => w.1.val)
    (Finset.mem_singleton.mp he)
  norm_num [BDL26TopOwnerIsolation.topNode] at hv

theorem componentWithLower_upper_self (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    p ∈ upperOwnerMaskRegion (componentWithLower lower p hp) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [componentWithLower_singleton]
  exact Finset.mem_singleton_self _

/-- For every possible lower marking, the actual top connected component
violates the selected-map2 mask equation on the actual recovered syndrome. -/
theorem actualHistory_component_mask_counterexample (lower : Finset StrictLowerNode) :
    ∃ p : FamilyZ scaleFive 4 (4 : LevelIndex 4), ∃ hp : witnessUpper.val p ≠ 0,
      maskWord (upperOwnerMaskRegion (componentWithLower lower p hp))
        (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessTopOutput.coarse.val) ≠
      ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2
        (maskWord (lowerOwnerMaskRegion (componentWithLower lower p hp)) witnessTopOutput.coarse.val) := by
  obtain ⟨p, hp⟩ : ∃ p, witnessUpper.val p ≠ 0 := by
    by_contra h
    push Not at h
    exact witnessUpper_nonzero (funext h)
  refine ⟨p, hp, ?_⟩
  rw [witnessTopOutput_coarse, componentWithLower_lower_empty]
  have hm : maskWord (∅ : Finset (FamilyZ scaleFive 4 (3 : LevelIndex 4))) witnessLower.val = 0 := by
    funext q
    simp [maskWord]
  rw [hm, map_zero]
  intro he
  have hval := congrFun he p
  have hmem := componentWithLower_upper_self lower p hp
  change (if p ∈ upperOwnerMaskRegion (componentWithLower lower p hp) then witnessUpper.val p else 0) = 0 at hval
  rw [if_pos hmem] at hval
  exact hp hval

/-- Negation of the universal component-mask equation required by the
unconditional owner/component coherence route. -/
theorem not_actualHistory_component_mask_commutation (lower : Finset StrictLowerNode) :
    ¬ (∀ (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0),
      maskWord (upperOwnerMaskRegion (componentWithLower lower p hp))
        (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessTopOutput.coarse.val) =
      ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2
        (maskWord (lowerOwnerMaskRegion (componentWithLower lower p hp)) witnessTopOutput.coarse.val)) := by
  intro h
  obtain ⟨p, hp, hn⟩ := actualHistory_component_mask_counterexample lower
  exact hn (h p hp)

end QEC.Coding.BDL26OwnerIncidenceMasks

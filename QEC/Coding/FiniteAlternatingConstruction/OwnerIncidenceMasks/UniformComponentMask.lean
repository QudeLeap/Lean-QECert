import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformWitness
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformIsolation

/-! # Actual marked-component mask obstruction at every even physical depth -/
namespace QEC.Coding.BDL26UniformHistoryObstruction

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

abbrev UniformNode (S : OddScale) (j : Nat) := BDL26UniformTopOwnerIsolation.Node S (2 * j + 3)
abbrev StrictLowerNode (S : OddScale) (j : Nat) := Σ i : Fin (2 * j + 4), GraphVertex S i.val
noncomputable def includeLowerNode (S : OddScale) (j : Nat)
    (v : StrictLowerNode S j) : UniformNode S j := ⟨v.1.castSucc,v.2⟩
noncomputable def markedNodes (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) : Finset (UniformNode S j) :=
  (topMarks S j).image (BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3)) ∪
    lower.image (includeLowerNode S j)

theorem markedNodes_top_iff (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (v : Vertex (state S (2 * j + 3)).presentation) :
    BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) v ∈ markedNodes S j lower ↔
      v ∈ topMarks S j := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with ht | hl
    · obtain ⟨w,hw,he⟩ := Finset.mem_image.mp ht
      have hv : w = v := by cases he; rfl
      exact hv ▸ hw
    · obtain ⟨w,_,he⟩ := Finset.mem_image.mp hl
      have hv := congrArg (fun p : UniformNode S j => p.1.val) he
      change w.1.val = 2 * j + 4 at hv
      have hlt := w.1.isLt
      omega
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,h,rfl⟩)

theorem markedNodes_only_z (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j)) :
    BDL26UniformTopOwnerIsolation.TopMarksAreZ S (2 * j + 3) (markedNodes S j lower) := by
  intro v hv
  exact topMarks_only_z S j v ((markedNodes_top_iff S j lower v).mp hv)

theorem markedNodes_active (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) (topOwner S j p) ∈ markedNodes S j lower :=
  (markedNodes_top_iff S j lower _).mpr (topMarks_active S j p hp)

noncomputable def component (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : Finset (UniformNode S j) :=
  (BDL26UniformTopOwnerIsolation.markedComponent S (2 * j + 3) (markedNodes S j lower)
    ⟨BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) (topOwner S j p),
      markedNodes_active S j lower p hp⟩).image Subtype.val

theorem component_singleton (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    component S j lower p hp = {BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) (topOwner S j p)} := by
  obtain ⟨z,hz⟩ := topMarks_only_z S j (topOwner S j p) (topMarks_active S j p hp)
  have hn := topOwner_parent_none S j p hp
  rw [hz] at hn
  have ha : BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) (.z z) ∈ markedNodes S j lower := by
    rw [← hz]
    exact markedNodes_active S j lower p hp
  simpa only [component, hz] using
    BDL26UniformTopOwnerIsolation.markedComponent_image_eq_singleton S (2 * j + 3)
      (markedNodes S j lower) (markedNodes_only_z S j lower) z hn ha

noncomputable def upperRegion (S : OddScale) (j : Nat) (K : Finset (UniformNode S j)) :
    Finset (FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4))) :=
  Finset.univ.filter (fun q => BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) (topOwner S j q) ∈ K)

noncomputable def lowerOwner (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) ⟨2 * j + 3, by omega⟩) :
    Vertex (state S (2 * j + 2)).presentation :=
  BDL26RXDecoderAdapter.vertexEquiv (state S (2 * j + 2)).presentation
    ((BDL26RXDecoderAdapter.rxData S (2 * j + 4) ⟨2 * j + 2, by omega⟩ (by simp)).topCenter p)

noncomputable def lowerRegion (S : OddScale) (j : Nat) (K : Finset (UniformNode S j)) :
    Finset (FamilyZ S (2 * j + 4) ⟨2 * j + 3, by omega⟩) :=
  Finset.univ.filter (fun q => (⟨⟨2 * j + 3, by omega⟩, lowerOwner S j q⟩ : UniformNode S j) ∈ K)

theorem component_lower_empty (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : lowerRegion S j (component S j lower p hp) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have he := (Finset.mem_filter.mp hq).2
  rw [component_singleton] at he
  have hv := congrArg (fun w : UniformNode S j => w.1.val) (Finset.mem_singleton.mp he)
  change 2 * j + 3 = 2 * j + 4 at hv
  omega

theorem component_upper_self (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : p ∈ upperRegion S j (component S j lower p hp) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [component_singleton]
  exact Finset.mem_singleton_self _

/-- Uniform failure on the actual recovered coarse word, for every strictly-lower marking. -/
theorem actualHistory_component_mask_counterexample (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) :
    ∃ p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      maskWord (upperRegion S j (component S j lower p hp))
        (((indexedDecoderData S (2 * j + 4)).selectedMap ⟨2 * j + 3, by omega⟩).map2
          (topOutput S j).coarse.val) ≠
      ((indexedDecoderData S (2 * j + 4)).selectedMap ⟨2 * j + 3, by omega⟩).map2
        (maskWord (lowerRegion S j (component S j lower p hp)) (topOutput S j).coarse.val) := by
  obtain ⟨p,hp⟩ : ∃ p, (upperSyndrome S j).val p ≠ 0 := by
    by_contra h
    push Not at h
    exact upperSyndrome_nonzero S j (funext h)
  refine ⟨p,hp,?_⟩
  intro he
  have heval := congrFun he p
  have hself := component_upper_self S j lower p hp
  rw [component_lower_empty] at heval
  have hz : maskWord (∅ : Finset (FamilyZ S (2 * j + 4) ⟨2 * j + 3, by omega⟩))
      (topOutput S j).coarse.val = 0 := by
    funext q
    simp [maskWord]
  rw [hz, map_zero] at heval
  have hc := topOutput_coarse S j
  have hupper : ((indexedDecoderData S (2 * j + 4)).selectedMap
      ⟨2 * j + 3, by omega⟩).map2 (topOutput S j).coarse.val = (upperSyndrome S j).val := by
    rw [hc]
    rfl
  rw [hupper] at heval
  exact hp (by simpa [maskWord, hself] using heval)

/-- Public internal/API quantifier: every k at least two, with the exact
physical-depth equality exposing the subtraction-free construction. -/
theorem every_even_depth_counterexample (S : OddScale) (k : Nat) (hk : 2 ≤ k) :
    2 * (k - 2) + 4 = 2 * k ∧
    ∀ lower : Finset (StrictLowerNode S (k - 2)),
    ∃ p : FamilyZ S (2 * (k - 2) + 4) (TopIndex (2 * (k - 2) + 4)),
    ∃ hp : (upperSyndrome S (k - 2)).val p ≠ 0,
      maskWord (upperRegion S (k - 2) (component S (k - 2) lower p hp))
        (((indexedDecoderData S (2 * (k - 2) + 4)).selectedMap
          ⟨2 * (k - 2) + 3, by omega⟩).map2 (topOutput S (k - 2)).coarse.val) ≠
      ((indexedDecoderData S (2 * (k - 2) + 4)).selectedMap
        ⟨2 * (k - 2) + 3, by omega⟩).map2
        (maskWord (lowerRegion S (k - 2) (component S (k - 2) lower p hp))
          (topOutput S (k - 2)).coarse.val) :=
  ⟨by omega, actualHistory_component_mask_counterexample S (k - 2)⟩

end QEC.Coding.BDL26UniformHistoryObstruction

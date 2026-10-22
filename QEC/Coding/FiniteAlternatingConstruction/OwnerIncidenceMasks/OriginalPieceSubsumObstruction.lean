import Mathlib.Algebra.BigOperators.Fin
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformComponentMask
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.Consistency

/-! # Obstruction for subsums of the original RZ correction pieces

BDL26 v1 paper.tex3584–3614 defines a component correction as a sum of
original local corrections. On the existing uniform valid input, every such
subsum has zero coboundary, so none repairs the singleton's adjacent-level
equation. The graph, owners, selected maps and complete actual marks are the
original ones. This is an internal obstruction under that fixed interpretation,
not a stability or memory-lifetime counterexample.
-/
namespace QEC.Coding.BDL26OriginalPieceSubsumObstruction

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

/-- Positions refer to the original ordered output list, even for repeated words. -/
noncomputable def outputPieceSubsum (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i)
    (A : Finset (Fin O.localComponents.length)) : (indexedFamily S depth).Correction i.succ :=
  ∑ a ∈ A, O.componentAt a

theorem outputPieceSubsum_empty (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i) :
    outputPieceSubsum S depth i O ∅ = 0 := by simp [outputPieceSubsum]

theorem outputPieceSubsum_singleton (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i)
    (a : Fin O.localComponents.length) :
    outputPieceSubsum S depth i O {a} = O.componentAt a := by simp [outputPieceSubsum]

/-- Summing every original position recovers the actual original correction. -/
theorem outputPieceSubsum_univ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i) :
    outputPieceSubsum S depth i O Finset.univ = O.correction := by
  change (∑ a : Fin O.localComponents.length, O.localComponents.get a) = O.correction
  rw [← Fin.sum_ofFn, List.ofFn_get]
  exact O.correction_decomposition.symm

/-- Actual embedded valid RZ inputs, with no supplied zero-boundary certificate. -/
theorem rz_originalPieceSubsum_boundary_zero (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (s : (indexedFamily S depth).Syndrome i.castSucc)
    (A : Finset (Fin (BDL26RZDecoderAdapter.rzStepOutput S depth i h
      (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)).localComponents.length)) :
    (indexedFamily S depth).coboundary1 i.succ
      (outputPieceSubsum S depth i
        (BDL26RZDecoderAdapter.rzStepOutput S depth i h
          (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)) A) = 0 := by
  rw [outputPieceSubsum, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  have hb := AssemblyStepOutput.componentCoboundaryAt_eq
    (D := indexedDecoderData S depth) (i := i)
    (BDL26RZDecoderAdapter.rzStepOutput S depth i h
      (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)) a
  exact hb.symm.trans
    (BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero S depth i h s a)

/-- All positions in the genuine actual top output have zero recorded boundary.
The entire dependent statement is transported before introducing its index. -/
theorem topOutput_piece_boundary_zero (S : OddScale) (j : Nat) :
    ∀ a : Fin (topOutput S j).localComponents.length,
      (topOutput S j).componentCoboundaryAt a = 0 := by
  have ho : topOutput S j = BDL26RZDecoderAdapter.rzStepOutput S (2*j+4)
      ⟨2*j+3, by omega⟩ (by simp) (upperSyndrome S j) :=
    congrFun (actualStep_rz S (2*j+4) ⟨2*j+3, by omega⟩ (by simp)) (upperSyndrome S j)
  rw [ho]
  exact fun a => BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero
    S (2*j+4) ⟨2*j+3, by omega⟩ (by simp) (lowerSyndrome S j) a

/-- No restriction or recomputation is applied to the original local words. -/
noncomputable def topPieceSubsum (S : OddScale) (j : Nat)
    (A : Finset (Fin (topOutput S j).localComponents.length)) :
    (indexedFamily S (2*j+4)).Correction (TopIndex (2*j+4)) :=
  outputPieceSubsum S (2*j+4) ⟨2*j+3, by omega⟩ (topOutput S j) A

theorem topPieceSubsum_empty (S : OddScale) (j : Nat) :
    topPieceSubsum S j ∅ = 0 := outputPieceSubsum_empty S _ _ _

theorem topPieceSubsum_singleton (S : OddScale) (j : Nat)
    (a : Fin (topOutput S j).localComponents.length) :
    topPieceSubsum S j {a} = (topOutput S j).componentAt a :=
  outputPieceSubsum_singleton S _ _ _ a

theorem topPieceSubsum_univ (S : OddScale) (j : Nat) :
    topPieceSubsum S j Finset.univ = (topOutput S j).correction :=
  outputPieceSubsum_univ S _ _ _

theorem topPieceSubsum_boundary_zero (S : OddScale) (j : Nat)
    (A : Finset (Fin (topOutput S j).localComponents.length)) :
    (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
      (topPieceSubsum S j A) = 0 := by
  rw [topPieceSubsum, outputPieceSubsum, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  have hb := AssemblyStepOutput.componentCoboundaryAt_eq
    (D := indexedDecoderData S (2*j+4)) (i := ⟨2*j+3, by omega⟩) (topOutput S j) a
  exact hb.symm.trans (topOutput_piece_boundary_zero S j a)

/-- The same active coordinate refutes every choice of original correction pieces. -/
theorem component_subsum_obstruction (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) :
    ∃ p : FamilyZ S (2*j+4) (TopIndex (2*j+4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S j).localComponents.length),
        maskWord (upperRegion S j (component S j lower p hp)) (upperSyndrome S j).val +
          (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
            (topPieceSubsum S j A) ≠
        ((indexedDecoderData S (2*j+4)).selectedMap ⟨2*j+3, by omega⟩).map2
          (maskWord (lowerRegion S j (component S j lower p hp))
            (topOutput S j).coarse.val) := by
  obtain ⟨p,hp⟩ : ∃ p, (upperSyndrome S j).val p ≠ 0 := by
    by_contra h
    push Not at h
    exact upperSyndrome_nonzero S j (funext h)
  refine ⟨p,hp,?_⟩
  intro A he
  rw [topPieceSubsum_boundary_zero, add_zero, component_lower_empty] at he
  have hz : maskWord (∅ : Finset (FamilyZ S (2*j+4) ⟨2*j+3, by omega⟩))
      (topOutput S j).coarse.val = 0 := by
    funext q
    simp [maskWord]
  rw [hz, map_zero] at he
  have hv := congrFun he p
  have hself := component_upper_self S j lower p hp
  exact hp (by simpa only [maskWord, if_pos hself, Pi.zero_apply] using hv)

/-- The complete source marking, with the actual stopped history and bottom closure. -/
noncomputable def canonicalMarks (S : OddScale) (j : Nat) : Finset (UniformNode S j) :=
  BDL26CanonicalHistoryMarks.marks S (2*j+2) (upperSyndrome S j)

theorem canonical_top_iff (S : OddScale) (j : Nat)
    (v : Vertex (state S (2*j+3)).presentation) :
    BDL26UniformTopOwnerIsolation.topNode S (2*j+3) v ∈ canonicalMarks S j ↔
      v ∈ topMarks S j := by
  have hm := BDL26CanonicalHistoryMarks.mem_marks_physical S (2*j+2)
    (upperSyndrome S j) (Fin.last (2*j+2)) v
  have ht := congrArg (fun M : Finset (Vertex (state S (2*j+3)).presentation) => v ∈ M)
    (BDL26CanonicalHistoryMarks.uniform_topMarks S j)
  exact hm.trans ht.to_iff

/-- Pull back precisely the strict-lower nodes of the real complete marked set. -/
noncomputable def canonicalLowerMarks (S : OddScale) (j : Nat) :
    Finset (StrictLowerNode S j) :=
  Finset.univ.filter (fun v => includeLowerNode S j v ∈ canonicalMarks S j)

private theorem includeLowerNode_injective (S : OddScale) (j : Nat) :
    Function.Injective (includeLowerNode S j) := by
  rintro ⟨i,v⟩ ⟨k,w⟩ he
  have hi : i = k := Fin.ext (congrArg (fun u : UniformNode S j => u.1.val) he)
  subst k
  have hv : v = w := by cases he; rfl
  subst w
  rfl

theorem markedNodes_lower_iff (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) (v : StrictLowerNode S j) :
    includeLowerNode S j v ∈ markedNodes S j lower ↔ v ∈ lower := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with ht | hl
    · obtain ⟨w,_,he⟩ := Finset.mem_image.mp ht
      have hv := congrArg (fun u : UniformNode S j => u.1.val) he
      change 2*j+4 = v.1.val at hv
      have hlt := v.1.isLt
      omega
    · obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hl
      exact (includeLowerNode_injective S j he) ▸ hw
  · intro hv
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)

/-- Exact equality retains every physical mark and the real G1/G0 root closure. -/
theorem canonical_markedNodes_eq (S : OddScale) (j : Nat) :
    markedNodes S j (canonicalLowerMarks S j) = canonicalMarks S j := by
  apply Finset.ext
  rintro ⟨i,v⟩
  revert v
  refine Fin.lastCases ?_ (fun k => ?_) i
  · intro v
    let w : Vertex (state S (2*j+3)).presentation := v
    exact (markedNodes_top_iff S j (canonicalLowerMarks S j) w).trans
      (canonical_top_iff S j w).symm
  · intro v
    change includeLowerNode S j ⟨k,v⟩ ∈ markedNodes S j (canonicalLowerMarks S j) ↔
      includeLowerNode S j ⟨k,v⟩ ∈ canonicalMarks S j
    rw [markedNodes_lower_iff]
    simp only [canonicalLowerMarks, Finset.mem_filter, Finset.mem_univ, true_and]

theorem canonical_active (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    BDL26UniformTopOwnerIsolation.topNode S (2*j+3) (topOwner S j p) ∈ canonicalMarks S j :=
  (canonical_top_iff S j _).mpr (topMarks_active S j p hp)

/-- Reachability in the original graph restricted to the COMPLETE actual marks. -/
noncomputable def canonicalComponent (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) : Finset (UniformNode S j) :=
  (BDL26UniformTopOwnerIsolation.markedComponent S (2*j+3) (canonicalMarks S j)
    ⟨BDL26UniformTopOwnerIsolation.topNode S (2*j+3) (topOwner S j p),
      canonical_active S j p hp⟩).image Subtype.val

theorem canonicalComponent_singleton (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    canonicalComponent S j p hp =
      {BDL26UniformTopOwnerIsolation.topNode S (2*j+3) (topOwner S j p)} := by
  obtain ⟨z,hz⟩ := topMarks_only_z S j _ (topMarks_active S j p hp)
  have hn := topOwner_parent_none S j p hp
  rw [hz] at hn
  have ha : BDL26UniformTopOwnerIsolation.topNode S (2*j+3) (.z z) ∈ canonicalMarks S j := by
    rw [← hz]
    exact canonical_active S j p hp
  have hM : BDL26UniformTopOwnerIsolation.TopMarksAreZ S (2*j+3) (canonicalMarks S j) := by
    intro v hv
    exact topMarks_only_z S j v ((canonical_top_iff S j v).mp hv)
  simpa only [canonicalComponent, hz] using
    BDL26UniformTopOwnerIsolation.markedComponent_image_eq_singleton S (2*j+3)
      (canonicalMarks S j) hM z hn ha

theorem canonicalComponent_eq_component (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    canonicalComponent S j p hp = component S j (canonicalLowerMarks S j) p hp := by
  rw [canonicalComponent_singleton, component_singleton]

theorem canonicalComponent_lower_empty (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    lowerRegion S j (canonicalComponent S j p hp) = ∅ := by
  rw [canonicalComponent_eq_component]
  exact component_lower_empty S j _ p hp

theorem canonicalComponent_upper_self (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    p ∈ upperRegion S j (canonicalComponent S j p hp) := by
  rw [canonicalComponent_eq_component]
  exact component_upper_self S j _ p hp

/-- Primitive inputs are only S,j. The one actual component defeats every subsum. -/
theorem canonical_component_subsum_obstruction (S : OddScale) (j : Nat) :
    ∃ p : FamilyZ S (2*j+4) (TopIndex (2*j+4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S j).localComponents.length),
        maskWord (upperRegion S j (canonicalComponent S j p hp)) (upperSyndrome S j).val +
          (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
            (topPieceSubsum S j A) ≠
        ((indexedDecoderData S (2*j+4)).selectedMap ⟨2*j+3, by omega⟩).map2
          (maskWord (lowerRegion S j (canonicalComponent S j p hp))
            (topOutput S j).coarse.val) := by
  obtain ⟨p,hp,h⟩ := component_subsum_obstruction S j (canonicalLowerMarks S j)
  refine ⟨p,hp,?_⟩
  intro A
  rw [canonicalComponent_eq_component]
  exact h A

theorem every_even_depth_obstruction (S : OddScale) (k : Nat) (hk : 2 ≤ k) :
    2*(k-2)+4 = 2*k ∧
    ∃ p : FamilyZ S (2*(k-2)+4) (TopIndex (2*(k-2)+4)),
    ∃ hp : (upperSyndrome S (k-2)).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S (k-2)).localComponents.length),
        maskWord (upperRegion S (k-2) (canonicalComponent S (k-2) p hp))
            (upperSyndrome S (k-2)).val +
          (indexedFamily S (2*(k-2)+4)).coboundary1 (TopIndex (2*(k-2)+4))
            (topPieceSubsum S (k-2) A) ≠
        ((indexedDecoderData S (2*(k-2)+4)).selectedMap ⟨2*(k-2)+3, by omega⟩).map2
          (maskWord (lowerRegion S (k-2) (canonicalComponent S (k-2) p hp))
            (topOutput S (k-2)).coarse.val) :=
  ⟨by omega, canonical_component_subsum_obstruction S (k-2)⟩

end QEC.Coding.BDL26OriginalPieceSubsumObstruction

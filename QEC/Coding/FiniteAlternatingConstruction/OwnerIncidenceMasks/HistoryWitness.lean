import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.History
import QEC.Coding.FiniteAlternatingConstruction.OwnerParentObstruction
import QEC.Coding.FiniteAlternatingConstruction.TopOwnerIsolation

/-! # Actual depth-four history used to test owner coherence

The upper input is a genuine selected-map image of an actual nonzero
coboundary at physical C3. The canonical RZ step recovers that input.
-/
namespace QEC.Coding.BDL26OwnerIncidenceMasks

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical

noncomputable def witnessLower : (indexedFamily scaleFive 4).Syndrome (3 : LevelIndex 4) :=
  ⟨(indexedFamily scaleFive 4).coboundary1 (3 : LevelIndex 4) evidenceCorrection,
    ⟨evidenceCorrection, rfl⟩⟩

theorem witnessLower_val : witnessLower.val = evidenceLowerSyndrome := by
  change (indexedFamily scaleFive 4).coboundary1 (3 : LevelIndex 4) evidenceCorrection = _
  rw [indexedFamily_coboundary1]
  rfl

noncomputable def witnessUpper : (indexedFamily scaleFive 4).Syndrome (4 : LevelIndex 4) :=
  BDL26RZDecoderAdapter.embeddedSyndrome scaleFive 4 (3 : StepIndex 4) witnessLower

theorem witnessUpper_val : witnessUpper.val = evidenceUpperSyndrome := by
  change ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessLower.val = _
  rw [witnessLower_val]
  rfl

theorem witnessLower_nonzero : witnessLower.val ≠ 0 := by
  rw [witnessLower_val]
  exact evidenceLowerSyndrome_nonzero

theorem witnessUpper_nonzero : witnessUpper.val ≠ 0 := by
  rw [witnessUpper_val]
  exact evidenceUpperSyndrome_nonzero

noncomputable def witnessTopOutput : AssemblyStepOutput (indexedDecoderData scaleFive 4) (3 : StepIndex 4) :=
  (actualAboveTwoSteps scaleFive 2).step 3 (by decide) witnessUpper
noncomputable def witnessNextOutput : AssemblyStepOutput (indexedDecoderData scaleFive 4) (2 : StepIndex 4) :=
  (actualAboveTwoSteps scaleFive 2).step 2 (by decide) witnessTopOutput.coarse

theorem witnessTopOutput_coarse : witnessTopOutput.coarse = witnessLower := by
  change (actualStep scaleFive 4 (3 : StepIndex 4) witnessUpper).coarse = witnessLower
  rw [actualStep_rz scaleFive 4 3 (by decide)]
  exact BDL26RZDecoderAdapter.rzStepOutput_map2_coarse scaleFive 4 3 (by decide) witnessLower

/-- Actual top syndrome owner, in the unchanged graph carrier G4. -/
noncomputable def witnessTopOwner
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) :
    Vertex (state scaleFive 3).presentation :=
  (BDL26RZDecoderAdapter.rzData scaleFive 4 (3 : StepIndex 4) (by decide)).topCenter p

theorem witnessTopOwner_eq (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) :
    witnessTopOwner p = Vertex.z p.1 := rfl

theorem witnessTopOwner_parent_none (p : FamilyZ scaleFive 4 (4 : LevelIndex 4))
    (hp : witnessUpper.val p ≠ 0) : parent scaleFive 3 (witnessTopOwner p) = none := by
  have he := evidenceUpperSyndrome_parent_none p
    (by simpa only [witnessUpper_val] using hp)
  exact he

/-- Each top correction retains the exact owner from the RZ output enumeration. -/
noncomputable def witnessTopComponentOwner
    (j : Fin witnessTopOutput.localComponents.length) : Vertex (state scaleFive 3).presentation :=
  Vertex.z (BDL26RZDecoderAdapter.componentOwner scaleFive 4 (3 : StepIndex 4)
    (by decide) witnessUpper j)

/-- Literal support marking: syndrome, nonzero component, or its coboundary.
No graph closure or parent-support conclusion is built into this operation. -/
noncomputable def outputMarks {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
    {V : Type} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) (synOwner : C2 i.succ → V)
    (pieceOwner : Fin O.localComponents.length → V) : Finset V :=
  Finset.univ.filter (fun v =>
    (∃ p, synOwner p = v ∧ O.input.val p ≠ 0) ∨
    (∃ j, pieceOwner j = v ∧ O.componentAt j ≠ 0) ∨
    (∃ j p, synOwner p = v ∧ O.componentCoboundaryAt j p ≠ 0))

theorem outputMarks_contains_syndrome {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
    {V : Type} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) (synOwner : C2 i.succ → V)
    (pieceOwner : Fin O.localComponents.length → V)
    (p : C2 i.succ) (hp : O.input.val p ≠ 0) :
    synOwner p ∈ outputMarks O synOwner pieceOwner :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, rfl, hp⟩⟩

noncomputable def witnessTopMarks :=
  outputMarks witnessTopOutput witnessTopOwner witnessTopComponentOwner

theorem witnessTopMarks_only_z (v : Vertex (state scaleFive 3).presentation)
    (hv : v ∈ witnessTopMarks) : ∃ z, v = Vertex.z z := by
  have hm := (Finset.mem_filter.mp hv).2
  rcases hm with ⟨p, rfl, _⟩ | ⟨j, rfl, _⟩ | ⟨j, p, rfl, _⟩
  · exact ⟨p.1, witnessTopOwner_eq p⟩
  · exact ⟨_, rfl⟩
  · exact ⟨p.1, witnessTopOwner_eq p⟩

theorem witnessTopMarks_nonempty : witnessTopMarks.Nonempty := by
  have hn := witnessUpper_nonzero
  obtain ⟨p, hp⟩ : ∃ p, witnessUpper.val p ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  refine ⟨witnessTopOwner p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact Or.inl ⟨p, rfl, hp⟩


/-- Actual RX syndrome ownership at physical C3. -/
noncomputable def witnessNextOwner (p : FamilyZ scaleFive 4 (3 : LevelIndex 4)) :
    Vertex (state scaleFive 2).presentation :=
  BDL26RXDecoderAdapter.vertexEquiv (state scaleFive 2).presentation
    ((BDL26RXDecoderAdapter.rxData scaleFive 4 (2 : StepIndex 4) (by decide)).topCenter p)

noncomputable def witnessNextComponentOwner
    (j : Fin witnessNextOutput.localComponents.length) : Vertex (state scaleFive 2).presentation :=
  BDL26RXDecoderAdapter.vertexEquiv (state scaleFive 2).presentation
    (BDL26RXDecoderAdapter.componentOwner scaleFive 4 (2 : StepIndex 4)
      (by decide) witnessTopOutput.coarse j)

noncomputable def witnessNextMarks :=
  outputMarks witnessNextOutput witnessNextOwner witnessNextComponentOwner

noncomputable def witnessBaseCorrection := (actualBase scaleFive 2).decode witnessNextOutput.coarse

noncomputable def witnessBaseEntry :
    RecursiveBaseLevelCorrection (LevelTwoHistory.suffixData (indexedDecoderData scaleFive 4)) where
  input := witnessNextOutput.coarse
  correction := witnessBaseCorrection
  relation := ((actualBase scaleFive 2).rightInverse witnessNextOutput.coarse).symm

/-- All three entries, including the executable physical-C2 correction, are
exactly the real history producing the top and next outputs above. -/
theorem witnessHistory_exact : actualHistory scaleFive 2 witnessUpper =
    [CorrectionHistoryEntry.step (1 : StepIndex 2)
      (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 1 witnessTopOutput),
     CorrectionHistoryEntry.step (0 : StepIndex 2)
      (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 0 witnessNextOutput),
     CorrectionHistoryEntry.base witnessBaseEntry] := by
  have h3 : (actualAboveTwoSteps scaleFive 2).step 3 (by decide) witnessUpper =
      witnessTopOutput := rfl
  have h2 : (actualAboveTwoSteps scaleFive 2).step 2 (by decide) witnessTopOutput.coarse =
      witnessNextOutput := rfl
  have h := LevelTwoHistory.stoppedHistory_two (indexedDecoderData scaleFive 4)
    (actualAboveTwoSteps scaleFive 2) (actualBase scaleFive 2) witnessUpper
  simp only [h3, h2] at h
  exact h

/-- The tested outputs are literally the first two entries of the actual stopped history. -/
theorem witnessHistory_prefix : ∃ tail,
    actualHistory scaleFive 2 witnessUpper =
      CorrectionHistoryEntry.step (1 : StepIndex 2)
        (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 1 witnessTopOutput) ::
      CorrectionHistoryEntry.step (0 : StepIndex 2)
        (LevelTwoHistory.suffixOutput (indexedDecoderData scaleFive 4) 0 witnessNextOutput) :: tail := by
  exact ⟨[CorrectionHistoryEntry.base witnessBaseEntry], witnessHistory_exact⟩



theorem witnessTopOutput_boundary_zero
    (j : Fin witnessTopOutput.localComponents.length) :
    witnessTopOutput.componentCoboundaryAt j = 0 :=
  BDL26RZDecoderAdapter.rzStepOutput_map2_component_boundary_zero
    scaleFive 4 3 (by decide) witnessLower j

theorem witnessNextOwner_eq (p : FamilyZ scaleFive 4 (3 : LevelIndex 4)) :
    witnessNextOwner p = rxSyndromeOwner evidenceStateTwo.presentation scaleFive p := by
  rcases p with (⟨x, f⟩ | ⟨q, e⟩) | ⟨z, c⟩ <;> rfl

theorem witnessNextOutput_input : witnessNextOutput.input = witnessLower := by
  exact ((actualStep_relation scaleFive 4 (2 : StepIndex 4)).input_eq
    witnessTopOutput.coarse).trans witnessTopOutput_coarse

/-- The real next-level syndrome marks its actual X owner. -/
theorem witnessNextMarks_contains_x : Vertex.x evidenceX ∈ witnessNextMarks := by
  obtain ⟨p, hp⟩ : ∃ p, witnessLower.val p ≠ 0 := by
    by_contra h
    push Not at h
    exact witnessLower_nonzero (funext h)
  have ho : witnessNextOwner p = Vertex.x evidenceX := by
    rw [witnessNextOwner_eq]
    exact evidenceLowerSyndrome_owner p (by simpa only [witnessLower_val] using hp)
  have hi : witnessNextOutput.input.val p ≠ 0 := by
    rw [witnessNextOutput_input]
    exact hp
  rw [← ho]
  exact outputMarks_contains_syndrome witnessNextOutput witnessNextOwner witnessNextComponentOwner p hi

/-- Explicit physical-C4 error producing the counterexample input. No bound
relative to a small-error threshold is asserted for this error. -/
noncomputable def witnessUpperError : (indexedFamily scaleFive 4).Correction (4 : LevelIndex 4) :=
  ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map1 evidenceCorrection

theorem witnessUpperError_syndrome :
    (indexedFamily scaleFive 4).coboundary1 (4 : LevelIndex 4) witnessUpperError = witnessUpper.val := by
  exact LinearMap.congr_fun
    (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).commutes_coboundary1)
    evidenceCorrection


end QEC.Coding.BDL26OwnerIncidenceMasks

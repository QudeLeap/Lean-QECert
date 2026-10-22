import QEC.Coding.FourDimensionalToricCode.Decoder.Assembly

/-!
# Histories stopping at physical level two

The suffix family starts at physical C2. Its level zero is an index in a
restricted family, not the graph root G0 or the original physical C0.
The existing assembly proves termination and the syndrome equation on this
suffix. Only actual steps above C2 and a C2 right inverse are supplied.
-/

namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory

universe u v

variable {n : Nat}

abbrev physicalLevel (i : LevelIndex n) : LevelIndex (n + 2) :=
  ⟨i.val + 2, by have := i.isLt; omega⟩

abbrev physicalStep (i : StepIndex n) : StepIndex (n + 2) :=
  ⟨i.val + 2, by have := i.isLt; omega⟩

@[simp] theorem physicalLevel_val (i : LevelIndex n) :
    (physicalLevel i).val = i.val + 2 := rfl

@[simp] theorem physicalStep_val (i : StepIndex n) :
    (physicalStep i).val = i.val + 2 := rfl

theorem physicalStep_parity (i : StepIndex n) :
    replacementKind (physicalStep i).val = replacementKind i.val := by
  simp [replacementKind]

variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

abbrev Suffix (C : LevelIndex (n + 2) → Type u) (i : LevelIndex n) :=
  C (physicalLevel i)

noncomputable abbrev suffixFamily (D : BDL26DecoderData (n + 2) C0 C1 C2) :
    BDL26CochainFamily n (Suffix C0) (Suffix C1) (Suffix C2) where
  complex := fun i => D.family.complex (physicalLevel i)

@[simp] theorem suffix_coboundary0 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : LevelIndex n) :
    (suffixFamily D).coboundary0 i = D.family.coboundary0 (physicalLevel i) := rfl

@[simp] theorem suffix_coboundary1 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : LevelIndex n) :
    (suffixFamily D).coboundary1 i = D.family.coboundary1 (physicalLevel i) := rfl

/-- Each stored edge is the original selected map at the corresponding physical step. -/
noncomputable def suffixEdge (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : BDL26CochainMap (suffixFamily D) i where
  map0 := (D.selectedMap (physicalStep i)).map0
  map1 := (D.selectedMap (physicalStep i)).map1
  map2 := (D.selectedMap (physicalStep i)).map2
  commutes_coboundary0 := (D.selectedMap (physicalStep i)).commutes_coboundary0
  commutes_coboundary1 := (D.selectedMap (physicalStep i)).commutes_coboundary1

noncomputable abbrev suffixData (D : BDL26DecoderData (n + 2) C0 C1 C2) :
    BDL26DecoderData n (Suffix C0) (Suffix C1) (Suffix C2) where
  family := suffixFamily D
  rxMap := suffixEdge D
  rzMap := suffixEdge D

@[simp] theorem suffix_selectedMap (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : (suffixData D).selectedMap i = suffixEdge D i := by
  simp [BDL26DecoderData.selectedMap, suffixData]

@[simp] theorem suffix_selected_map0 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : ((suffixData D).selectedMap i).map0 =
      (D.selectedMap (physicalStep i)).map0 := by rw [suffix_selectedMap]; rfl

@[simp] theorem suffix_selected_map1 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : ((suffixData D).selectedMap i).map1 =
      (D.selectedMap (physicalStep i)).map1 := by rw [suffix_selectedMap]; rfl

@[simp] theorem suffix_selected_map2 (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) : ((suffixData D).selectedMap i).map2 =
      (D.selectedMap (physicalStep i)).map2 := by rw [suffix_selectedMap]; rfl

/-- Only physical steps with lower index at least two are requested. -/
structure AboveTwoSteps (D : BDL26DecoderData (n + 2) C0 C1 C2) where
  step : ∀ i : StepIndex (n + 2), 2 ≤ i.val → AssemblyStep D i
  relation : ∀ i h, AssemblyStepRelation D i (step i h)

noncomputable def suffixOutput (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    AssemblyStepOutput (suffixData D) i where
  input := O.input
  coarse := O.coarse
  correction := O.correction
  localComponents := O.localComponents
  componentSupports := O.componentSupports
  componentCoboundaries := O.componentCoboundaries
  relation := by
    rw [suffix_selected_map2]
    change O.input.val = D.family.coboundary1 (physicalStep i).succ O.correction +
      (D.selectedMap (physicalStep i)).map2 O.coarse.val
    exact O.relation
  correction_decomposition := O.correction_decomposition
  componentSupports_length := O.componentSupports_length
  componentCoboundaries_length := O.componentCoboundaries_length
  componentSupport_eq := O.componentSupport_eq
  componentCoboundary_eq := O.componentCoboundary_eq

@[simp] theorem suffixOutput_components (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    (suffixOutput D i O).localComponents = O.localComponents := rfl

theorem suffixOutput_supports (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    (suffixOutput D i O).componentSupports = O.componentSupports := rfl

theorem suffixOutput_coboundaries (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    (suffixOutput D i O).componentCoboundaries = O.componentCoboundaries := rfl

noncomputable def suffixSteps (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) : AlternatingStepData (suffixData D) where
  step := fun i sigma => suffixOutput D i (S.step (physicalStep i) (by simp) sigma)
  relation := by
    intro i
    refine ⟨?_, ?_⟩
    · intro sigma
      exact (S.relation (physicalStep i) (by simp)).input_eq sigma
    · intro sigma
      exact (suffixOutput D i (S.step (physicalStep i) (by simp) sigma)).relation

/-- Convert the externally proved physical C2 right inverse into the suffix base. -/
noncomputable def suffixBase (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (decode : D.family.Syndrome (physicalLevel (0 : LevelIndex n)) →
      D.family.Correction (physicalLevel (0 : LevelIndex n)))
    (hdecode : ∀ sigma, D.family.coboundary1 (physicalLevel (0 : LevelIndex n))
      (decode sigma) = sigma.val) : AuditedBaseDecoder (suffixData D) where
  decode := decode
  rightInverse := hdecode

noncomputable def stoppedHistory (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) : CorrectionHistory (suffixData D) :=
  buildCorrectionHistory (suffixData D) (suffixSteps D S) B sigma

/-- A zero-preserving physical decoder retains zero syndrome snapshots in its
fixed C2-stopped history. Corrections and components are not erased. -/
theorem stoppedHistory_zero_inputs (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (hz : ∀ i hi sigma, sigma.val = 0 → (S.step i hi sigma).coarse.val = 0)
    (sigma : D.family.Syndrome (TopIndex (n + 2))) (hs : sigma.val = 0) :
    ∀ e ∈ stoppedHistory D S B sigma, e.inputSyndrome.2.val = 0 :=
  buildCorrectionHistory_zero_inputs (suffixData D) (suffixSteps D S) B
    (fun i s h => hz (physicalStep i) (by simp) s h) sigma hs

/-- Expose the canonical first physical step without expanding the history tail. -/
theorem stoppedHistory_head
    (m : Nat) {A0 A1 A2 : LevelIndex ((m + 1) + 2) → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData ((m + 1) + 2) A0 A1 A2)
    (S : AboveTwoSteps (n := m + 1) D)
    (B : AuditedBaseDecoder (suffixData (n := m + 1) D))
    (sigma : D.family.Syndrome (TopIndex ((m + 1) + 2))) :
    ∃ tail, stoppedHistory D S B sigma =
      CorrectionHistoryEntry.step (Fin.last m)
        (suffixOutput D (Fin.last m)
          (S.step (physicalStep (Fin.last m)) (by simp [physicalStep]) sigma)) :: tail :=
  buildCorrectionHistory_head m (suffixData D) (suffixSteps D S) B sigma

/-- Physical C4-to-C2 expansion before instantiating a concrete finite family. -/
theorem stoppedHistory_two
    {A0 A1 A2 : LevelIndex 4 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 4 A0 A1 A2) (S : AboveTwoSteps (n := 2) D)
    (B : AuditedBaseDecoder (suffixData (n := 2) D))
    (sigma : D.family.Syndrome (TopIndex 4)) :
    stoppedHistory (n := 2) D S B sigma =
      [.step 1 (suffixOutput D 1 (S.step 3 (by decide) sigma)),
       .step 0 (suffixOutput D 0 (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse)),
       .base { input := (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse
               correction := B.decode (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse
               relation := (B.rightInverse
                 (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse).symm }] :=
  buildCorrectionHistory_two (suffixData D) (suffixSteps D S) B sigma


theorem stoppedHistory_length (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    (stoppedHistory D S B sigma).length = n + 1 :=
  buildCorrectionHistory_terminates (suffixData D) (suffixSteps D S) B sigma

noncomputable def entryPhysicalLevel (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (e : CorrectionHistoryEntry (suffixData D)) : Nat := e.level + 2

theorem entryPhysicalLevel_bounds (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (e : CorrectionHistoryEntry (suffixData D)) :
    2 ≤ entryPhysicalLevel D e ∧ entryPhysicalLevel D e ≤ n + 2 := by
  cases e with
  | base B => simp [entryPhysicalLevel, CorrectionHistoryEntry.level]
  | step i O =>
    have := i.isLt
    simp only [entryPhysicalLevel, CorrectionHistoryEntry.level, Fin.val_succ]
    omega

/-- Ordered physical snapshots, with no fabricated lower-level corrections. -/
noncomputable def physicalInputSnapshots (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) :
    List (Σ i : LevelIndex (n + 2), D.family.Syndrome i) :=
  H.map (fun e => ⟨physicalLevel e.inputSyndrome.1, e.inputSyndrome.2⟩)

noncomputable def physicalCorrectionSnapshots (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) :
    List (Σ i : LevelIndex (n + 2), D.family.Correction i) :=
  H.map (fun e => ⟨physicalLevel e.correction.1, e.correction.2⟩)

noncomputable def physicalLocalComponents (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (e : CorrectionHistoryEntry (suffixData D)) :
    List (Σ i : LevelIndex (n + 2), D.family.Correction i) :=
  e.localComponents.map (fun p => ⟨physicalLevel p.1, p.2⟩)

/-- Read out a history's syndrome at a physical index, padding absent levels by zero.
For histories produced by assembly the level snapshots are ordered and unique;
the sum definition also makes zero padding well-defined for any supplied list. -/
noncomputable def syndromeReadout (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex (n + 2)) :
    D.family.Cochain2 i := by
  classical
  exact ((physicalInputSnapshots D H).map (fun p =>
    if h : p.1 = i then h ▸ p.2.val else 0)).sum


/-- Physical reindexing preserves the exact sum of matching input snapshots. -/
theorem syndromeReadout_physical
    (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex n) :
    syndromeReadout D H (physicalLevel i) = historyInputReadout (suffixData D) H i := by
  classical
  unfold syndromeReadout physicalInputSnapshots historyInputReadout
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  by_cases h : e.inputSyndrome.1 = i
  · cases h
    simp
  · have hp : physicalLevel e.inputSyndrome.1 ≠ physicalLevel i := by
      intro he
      apply h
      apply Fin.ext
      have hv := congrArg Fin.val he
      simpa only [physicalLevel, Nat.add_right_cancel_iff] using hv
    simp [h, hp]

/-- The physical C2 snapshot agrees with the actual recursively selected input. -/
theorem stoppedHistory_base_readout
    (D : BDL26DecoderData (n + 2) C0 C1 C2) (S : AboveTwoSteps D)
    (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    syndromeReadout D (stoppedHistory D S B sigma) (physicalLevel (0 : LevelIndex n)) =
      (terminalInput (suffixData D) (suffixSteps D S) sigma).val := by
  rw [syndromeReadout_physical]
  exact buildCorrectionHistory_base_readout (suffixData D) (suffixSteps D S) B sigma

/-- Accumulate the actual above-C2 primitive inequalities, with no steps at C1/C0. -/
theorem stoppedHistory_base_weight
    (D : BDL26DecoderData (n + 2) C0 C1 C2) (S : AboveTwoSteps D)
    (B : AuditedBaseDecoder (suffixData D))
    (hstep : ∀ (i : StepIndex n)
      (s : (suffixData D).family.Syndrome i.succ),
      if i.val % 2 = 0 then
        2 * HammingWeight (S.step (physicalStep i) (by simp) s).coarse.val ≤
          HammingWeight s.val
      else HammingWeight (S.step (physicalStep i) (by simp) s).coarse.val ≤
        HammingWeight s.val)
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    2 ^ ((n + 1) / 2) * HammingWeight
      (syndromeReadout D (stoppedHistory D S B sigma)
        (physicalLevel (0 : LevelIndex n))) ≤ HammingWeight sigma.val := by
  rw [syndromeReadout_physical]
  apply buildCorrectionHistory_base_weight (suffixData D) (suffixSteps D S) B
  intro i s
  exact hstep i s

theorem syndromeReadout_below_two (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (H : CorrectionHistory (suffixData D)) (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    syndromeReadout D H i = 0 := by
  classical
  unfold syndromeReadout
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have htwo : 2 ≤ p.1.val := by
    unfold physicalInputSnapshots at hp
    obtain ⟨e, _, he⟩ := List.mem_map.mp hp
    have hv := congrArg (fun q : Σ j : LevelIndex (n + 2), D.family.Syndrome j =>
      q.1.val) he
    change e.inputSyndrome.1.val + 2 = p.1.val at hv
    omega
  have hne : p.1 ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact dif_neg hne

/-- The actual lifted sum of this same history has the supplied top syndrome. -/
theorem stoppedHistory_syndrome (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    D.family.coboundary1 (TopIndex (n + 2))
      (historyLiftedCorrection (suffixData D) (stoppedHistory D S B sigma)) = sigma.val :=
  historyLiftedCorrection_syndrome_eq (suffixData D) (suffixSteps D S) B sigma

end QEC.Coding.MultiscaleDecoder.LevelTwoHistory

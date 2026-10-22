import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.HistoryWitness

/-! # Unique actual stopped-history snapshots

The input-level list is exactly the reversed physical interval. The chosen
entry is consequently an actual entry, unique at its level, rather than an
externally supplied snapshot or a sum of possibly duplicated inputs.
-/
namespace QEC.Coding.BDL26CanonicalHistoryMarks

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

variable (S : OddScale) (n : Nat)

noncomputable abbrev Data := LevelTwoHistory.suffixData (indexedDecoderData S (n + 2))
abbrev Input := (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2))

variable (sigma : Input S n)

theorem entry_existsUnique (i : LevelIndex n) :
    ∃! e : CorrectionHistoryEntry (Data S n),
      e ∈ actualHistory S n sigma ∧ e.inputSyndrome.1 = i := by
  have hl := buildCorrectionHistory_input_levels (Data S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma
  have hm : i.val ∈ (actualHistory S n sigma).map (fun e => e.inputSyndrome.1.val) := by
    rw [show (actualHistory S n sigma).map (fun e => e.inputSyndrome.1.val) =
      (List.range (n + 1)).reverse from hl]
    simp only [List.mem_reverse, List.mem_range]
    exact i.isLt
  obtain ⟨e, he, hi⟩ := List.mem_map.mp hm
  have hei : e.inputSyndrome.1 = i := Fin.ext hi
  refine ⟨e, ⟨he, hei⟩, ?_⟩
  intro f hf
  have hn := buildCorrectionHistory_input_levels_nodup (Data S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n) sigma
  exact List.inj_on_of_nodup_map hn hf.1 he
    (congrArg Fin.val (hf.2.trans hei.symm))

noncomputable def entryAt (i : LevelIndex n) : CorrectionHistoryEntry (Data S n) :=
  Classical.choose (ExistsUnique.exists (entry_existsUnique S n sigma i))

theorem entryAt_spec (i : LevelIndex n) :
    entryAt S n sigma i ∈ actualHistory S n sigma ∧
      (entryAt S n sigma i).inputSyndrome.1 = i :=
  Classical.choose_spec (ExistsUnique.exists (entry_existsUnique S n sigma i))

theorem entryAt_eq (i : LevelIndex n) (e : CorrectionHistoryEntry (Data S n))
    (he : e ∈ actualHistory S n sigma) (hi : e.inputSyndrome.1 = i) :
    entryAt S n sigma i = e :=
  (entry_existsUnique S n sigma i).unique (entryAt_spec S n sigma i) ⟨he, hi⟩

noncomputable def inputAt (i : LevelIndex n) : (Data S n).family.Syndrome i :=
  (entryAt_spec S n sigma i).2 ▸ (entryAt S n sigma i).inputSyndrome.2

theorem inputAt_step (i : StepIndex n) (O : AssemblyStepOutput (Data S n) i)
    (he : CorrectionHistoryEntry.step i O ∈ actualHistory S n sigma) :
    inputAt S n sigma i.succ = O.input := by
  have hh : HEq (entryAt S n sigma i.succ).inputSyndrome.2 O.input := by
    rw [entryAt_eq S n sigma i.succ (.step i O) he rfl]
    rfl
  exact eq_of_heq (rec_heq_of_heq (entryAt_spec S n sigma i.succ).2 hh)

theorem inputAt_base (B : RecursiveBaseLevelCorrection (Data S n))
    (he : CorrectionHistoryEntry.base B ∈ actualHistory S n sigma) :
    inputAt S n sigma 0 = B.input := by
  have hh : HEq (entryAt S n sigma 0).inputSyndrome.2 B.input := by
    rw [entryAt_eq S n sigma 0 (.base B) he rfl]
    rfl
  exact eq_of_heq (rec_heq_of_heq (entryAt_spec S n sigma 0).2 hh)

/-- Recompute precisely the unique stored output from the unique actual input. -/
noncomputable def outputAt (i : StepIndex n) :
    AssemblyStepOutput (indexedDecoderData S (n + 2)) (LevelTwoHistory.physicalStep i) :=
  actualStep S (n + 2) (LevelTwoHistory.physicalStep i) (inputAt S n sigma i.succ)

theorem entryAt_step (i : StepIndex n) :
    entryAt S n sigma i.succ = .step i
      (LevelTwoHistory.suffixOutput (indexedDecoderData S (n + 2)) i
        (outputAt S n sigma i)) := by
  have hs := entryAt_spec S n sigma i.succ
  have hp := buildCorrectionHistory_entry_provenance (Data S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    sigma (entryAt S n sigma i.succ) hs.1
  generalize he : entryAt S n sigma i.succ = e at hs hp ⊢
  cases e with
  | base B =>
      have hv := congrArg Fin.val hs.2
      simp [CorrectionHistoryEntry.inputSyndrome] at hv
  | step k O =>
      have hk : k = i := by
        apply Fin.ext
        have hv := congrArg Fin.val hs.2
        simpa only [CorrectionHistoryEntry.inputSyndrome, Fin.val_succ,
          Nat.add_right_cancel_iff] using hv
      subst k
      have hi := inputAt_step S n sigma i O hs.1
      rw [show outputAt S n sigma i =
        actualStep S (n + 2) (LevelTwoHistory.physicalStep i) O.input by
        simp only [outputAt, hi]]
      exact congrArg (CorrectionHistoryEntry.step i) hp

noncomputable def baseInput := inputAt S n sigma (0 : LevelIndex n)
noncomputable def baseCorrection := actualBaseDecode S n (baseInput S n sigma)

/-- The base entry is unique and its correction is the real selected decoder. -/
theorem entryAt_base :
    ∃ B : RecursiveBaseLevelCorrection (Data S n),
      entryAt S n sigma 0 = .base B ∧
      B.input = baseInput S n sigma ∧ B.correction = baseCorrection S n sigma := by
  have hs := entryAt_spec S n sigma 0
  have hp := buildCorrectionHistory_entry_provenance (Data S n)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
    sigma (entryAt S n sigma 0) hs.1
  generalize he : entryAt S n sigma 0 = e at hs hp ⊢
  cases e with
  | step i O =>
      have hv := congrArg Fin.val hs.2
      simp [CorrectionHistoryEntry.inputSyndrome] at hv
  | base B =>
      refine ⟨B, rfl, ?_, ?_⟩
      · exact (inputAt_base S n sigma B hs.1).symm
      · change B.correction = (actualBase S n).decode (inputAt S n sigma 0)
        rw [inputAt_base S n sigma B hs.1]
        exact hp

theorem outputAt_input (i : StepIndex n) :
    (outputAt S n sigma i).input = inputAt S n sigma i.succ :=
  (actualStep_relation S (n + 2) (LevelTwoHistory.physicalStep i)).input_eq _

/-- Every above-C2 unique snapshot contains the same ordered correction,
support and coboundary lists as the actual physical adapter. -/
theorem entryAt_components (i : StepIndex n) :
    (entryAt S n sigma i.succ).localComponents =
      (outputAt S n sigma i).localComponents.map (fun f => ⟨i.succ, f⟩) := by
  rw [entryAt_step]
  rfl

theorem baseInput_depthTwo (s : Input S 0) : baseInput S 0 s = s := by
  have hh := buildCorrectionHistory_zero (Data S 0)
    (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S 0)) (actualBase S 0) s
  let B : RecursiveBaseLevelCorrection (Data S 0) :=
    { input := s, correction := (actualBase S 0).decode s,
      relation := ((actualBase S 0).rightInverse s).symm }
  have hm : CorrectionHistoryEntry.base B ∈ actualHistory S 0 s := by
    rw [show actualHistory S 0 s = [.base B] from hh]
    exact List.mem_singleton_self _
  exact inputAt_base S 0 s B hm

/-- The literal top snapshot is the real top adapter output for any non-base depth. -/
theorem outputAt_top (m : Nat) (s : Input S (m + 1)) :
    outputAt S (m + 1) s (Fin.last m) =
      actualStep S ((m + 1) + 2) (LevelTwoHistory.physicalStep (Fin.last m)) s := by
  obtain ⟨tail, ht⟩ := LevelTwoHistory.stoppedHistory_head m
    (indexedDecoderData S ((m + 1) + 2)) (actualAboveTwoSteps S (m + 1))
    (actualBase S (m + 1)) s
  have hm : CorrectionHistoryEntry.step (Fin.last m)
      (LevelTwoHistory.suffixOutput (indexedDecoderData S ((m + 1) + 2)) (Fin.last m)
        (actualStep S ((m + 1) + 2) (LevelTwoHistory.physicalStep (Fin.last m)) s)) ∈
      actualHistory S (m + 1) s := by
    rw [show actualHistory S (m + 1) s = _ from ht]
    exact List.mem_cons_self
  have hi := inputAt_step S (m + 1) s (Fin.last m) _ hm
  have ho := (actualStep_relation S ((m + 1) + 2)
    (LevelTwoHistory.physicalStep (Fin.last m))).input_eq s
  simpa only [outputAt, LevelTwoHistory.suffixOutput, ho] using
    congrArg (actualStep S ((m + 1) + 2) (LevelTwoHistory.physicalStep (Fin.last m))) hi

end QEC.Coding.BDL26CanonicalHistoryMarks

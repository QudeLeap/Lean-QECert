import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.Snapshots

/-! # Physical-level marks of the actual stopped history

All three source guards are retained independently. The physical-C2 pieces
are exactly the owner fibres of the real selected correction, including any
nonzero piece with zero coboundary.
-/
namespace QEC.Coding.BDL26CanonicalHistoryMarks

open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators

variable (S : OddScale) (n : Nat) (sigma : Input S n)

noncomputable def syndromeOwner (i : StepIndex n) :
    FamilyZ S (n + 2) (LevelTwoHistory.physicalStep i).succ →
      GraphVertex S (i.val + 3) :=
  if h : (LevelTwoHistory.physicalStep i).val % 2 = 0 then
    fun p => BDL26RXDecoderAdapter.vertexEquiv (state S (i.val + 2)).presentation
      ((BDL26RXDecoderAdapter.rxData S (n + 2) (LevelTwoHistory.physicalStep i) h).topCenter p)
  else fun p =>
    (BDL26RZDecoderAdapter.rzData S (n + 2) (LevelTwoHistory.physicalStep i) h).topCenter p

/-- The actual parity-specific ordered piece label, preserving its finite index. -/
noncomputable def pieceOwner (i : StepIndex n)
    (a : Fin (outputAt S n sigma i).localComponents.length) :
    GraphVertex S (i.val + 3) :=
  if h : (LevelTwoHistory.physicalStep i).val % 2 = 0 then
    BDL26RXDecoderAdapter.vertexEquiv (state S (i.val + 2)).presentation
      (BDL26RXDecoderAdapter.componentOwner S (n + 2) (LevelTwoHistory.physicalStep i) h
        (inputAt S n sigma i.succ) ⟨a.val, by
          simpa only [outputAt, actualStep_rx S (n + 2) (LevelTwoHistory.physicalStep i) h]
            using a.isLt⟩)
  else Vertex.z
      (BDL26RZDecoderAdapter.componentOwner S (n + 2) (LevelTwoHistory.physicalStep i) h
        (inputAt S n sigma i.succ) ⟨a.val, by
          simpa only [outputAt, actualStep_rz S (n + 2) (LevelTwoHistory.physicalStep i) h]
            using a.isLt⟩)

noncomputable def aboveMarks (i : StepIndex n) : Finset (GraphVertex S (i.val + 3)) :=
  outputMarks (outputAt S n sigma i) (syndromeOwner S n i) (pieceOwner S n sigma i)

theorem mem_aboveMarks (i : StepIndex n) (v : GraphVertex S (i.val + 3)) :
    v ∈ aboveMarks S n sigma i ↔
      (∃ p, syndromeOwner S n i p = v ∧ (outputAt S n sigma i).input.val p ≠ 0) ∨
      (∃ a, pieceOwner S n sigma i a = v ∧ (outputAt S n sigma i).componentAt a ≠ 0) ∨
      (∃ a p, syndromeOwner S n i p = v ∧
        (outputAt S n sigma i).componentCoboundaryAt a p ≠ 0) := by
  simp only [aboveMarks, outputMarks, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Base ownership is RZ ownership in the actual state-one replacement. -/
noncomputable def baseCorrectionOwner :
    FamilyQ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) → GraphVertex S 2 :=
  rzCorrectionOwner (state S 1).presentation S

noncomputable def baseSyndromeOwner :
    FamilyZ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) → GraphVertex S 2 :=
  fun p => Vertex.z (rzSyndromeOwner (state S 1).presentation S p)

noncomputable def basePiece (v : GraphVertex S 2) :
    (indexedFamily S (n + 2)).Correction (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) :=
  fiberPart (baseCorrectionOwner S n) v (baseCorrection S n sigma)

theorem basePiece_partition : (∑ v : GraphVertex S 2, basePiece S n sigma v) =
    baseCorrection S n sigma := sum_fiberPart _ _

theorem basePiece_support_iff (v : GraphVertex S 2)
    (p : FamilyQ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) :
    p ∈ hammingSupport (basePiece S n sigma v) ↔
      baseCorrectionOwner S n p = v ∧ baseCorrection S n sigma p ≠ 0 := by
  simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    basePiece, fiberPart_apply]
  by_cases h : baseCorrectionOwner S n p = v <;> simp [h]

noncomputable def basePieceBoundary (v : GraphVertex S 2) :=
  (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalLevel (0 : LevelIndex n))
    (basePiece S n sigma v)

theorem basePieceBoundary_partition :
    (∑ v : GraphVertex S 2, basePieceBoundary S n sigma v) =
      (baseInput S n sigma).val := by
  unfold basePieceBoundary
  rw [← map_sum, basePiece_partition]
  exact actualBaseDecode_rightInverse S n _

noncomputable def baseMarks : Finset (GraphVertex S 2) :=
  Finset.univ.filter (fun v =>
    (∃ p, baseSyndromeOwner S n p = v ∧ (baseInput S n sigma).val p ≠ 0) ∨
    basePiece S n sigma v ≠ 0 ∨
    (∃ u p, baseSyndromeOwner S n p = v ∧ basePieceBoundary S n sigma u p ≠ 0))

theorem mem_baseMarks (v : GraphVertex S 2) : v ∈ baseMarks S n sigma ↔
    (∃ p, baseSyndromeOwner S n p = v ∧ (baseInput S n sigma).val p ≠ 0) ∨
    basePiece S n sigma v ≠ 0 ∨
    (∃ u p, baseSyndromeOwner S n p = v ∧ basePieceBoundary S n sigma u p ≠ 0) := by
  simp only [baseMarks, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A nonzero closed fibre is retained by guard 1.2 without testing its boundary. -/
theorem baseMarks_contains_nonzero_piece (v : GraphVertex S 2)
    (h : basePiece S n sigma v ≠ 0) : v ∈ baseMarks S n sigma :=
  (mem_baseMarks S n sigma v).mpr (Or.inr (Or.inl h))

/-- A positive-dimensional local-Z graph node need not have a parent. Its
literal syndrome guard still marks it, without adding a connector edge. -/
theorem unparented_base_syndrome_guard
    (v : GraphVertex S 2) (hv : parent S 1 v = none)
    (p : FamilyZ S (n + 2) (LevelTwoHistory.physicalLevel (0 : LevelIndex n)))
    (ho : baseSyndromeOwner S n p = v) (hp : (baseInput S n sigma).val p ≠ 0) :
    v ∈ baseMarks S n sigma ∧ parent S 1 v = none :=
  ⟨(mem_baseMarks S n sigma v).mpr (Or.inl ⟨p, ho, hp⟩), hv⟩

/-- Suffix level zero is physical C2; every successor is the unique above-C2 step. -/
noncomputable def physicalMarks : (i : LevelIndex n) → Finset (GraphVertex S (i.val + 2))
  | ⟨0, _⟩ => baseMarks S n sigma
  | ⟨k + 1, hk⟩ => aboveMarks S n sigma ⟨k, by omega⟩

@[simp] theorem physicalMarks_base : physicalMarks S n sigma (0 : LevelIndex n) =
    baseMarks S n sigma := rfl

@[simp] theorem physicalMarks_step (i : StepIndex n) :
    physicalMarks S n sigma i.succ = aboveMarks S n sigma i := rfl

end QEC.Coding.BDL26CanonicalHistoryMarks

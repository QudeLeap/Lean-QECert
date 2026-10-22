import QEC.Coding.FiniteAlternatingConstruction.RZCohomology.Indexed
import QEC.Coding.FiniteAlternatingConstruction.FiniteCohomology
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.Snapshots

/-!
# Full actual RZ updated-error pullback

The full updated error includes the original error and the actual selected
correction. The resulting lower error is constructed using actual coarse
validity and the proved RZ H¹ inverse. Its stabilizer potential is a full
upper degree-zero word. No support or parent-locality claim is made here.
-/

noncomputable section
namespace QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks

variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

abbrev Lower := (indexedFamily S depth).Correction i.castSucc
abbrev Upper := (indexedFamily S depth).Correction i.succ
abbrev Potential := (indexedFamily S depth).Cochain0 i.succ

/-- Pointwise characteristic-two cancellation also covers empty coordinate types. -/
private theorem word_add_self {α : Type*} (w : Word (ZMod 2) α) : w + w = 0 := by
  funext q
  exact CharTwo.add_self_eq_zero (w q)

/-- The genuine image syndrome of the supplied original error. -/
def errorSyndrome (a : Upper S depth i) : (indexedFamily S depth).Syndrome i.succ :=
  ⟨(indexedFamily S depth).coboundary1 i.succ a, ⟨a, rfl⟩⟩

/-- The selected actual RZ output, with its correction retained even at zero. -/
def run (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  BDL26RZDecoderAdapter.rzStepOutput S depth i h (errorSyndrome S depth i a)

def updated (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) : Upper S depth i :=
  a + b + (run S depth i h a).correction + (run S depth i h b).correction

/-- Validity of this sum is derived from the actual two coarse outputs. -/
def coarseSum (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).Syndrome i.castSucc :=
  ⟨(run S depth i h a).coarse.val + (run S depth i h b).coarse.val,
    ((indexedFamily S depth).syndromeSubmodule i.castSucc).add_mem
      (run S depth i h a).coarse.property (run S depth i h b).coarse.property⟩

theorem correction_delta (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h a).correction =
      (errorSyndrome S depth i a).val +
        ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  have hr := BDL26RZDecoderAdapter.rzStepOutput_relation S depth i h (errorSyndrome S depth i a)
  funext z
  exact (CharTwo.eq_add_iff_add_eq.mp (congrFun hr z)).symm

/-- Bare corrections retain the original syndrome difference. -/
theorem correction_difference_delta (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((run S depth i h a).correction + (run S depth i h b).correction) =
    (errorSyndrome S depth i a).val + (errorSyndrome S depth i b).val +
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  rw [map_add, correction_delta S depth i h a, correction_delta S depth i h b]
  change _ = _ + _ + ((indexedDecoderData S depth).selectedMap i).map2
    ((run S depth i h a).coarse.val + (run S depth i h b).coarse.val)
  rw [map_add]
  abel

/-- The full updated-error difference has precisely the transported coarse syndrome. -/
theorem updated_delta (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  have hr := correction_difference_delta S depth i h a b
  calc
    (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) =
        (errorSyndrome S depth i a).val + (errorSyndrome S depth i b).val +
          (indexedFamily S depth).coboundary1 i.succ
            ((run S depth i h a).correction + (run S depth i h b).correction) := by
              simp only [updated, errorSyndrome, map_add]
              abel
    _ = ((indexedDecoderData S depth).selectedMap i).map2
        (coarseSum S depth i h a b).val := by
      rw [hr, ← add_assoc, word_add_self, zero_add]

theorem one_updated_delta (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) =
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  rw [map_add, correction_delta]
  change (errorSyndrome S depth i a).val + ((errorSyndrome S depth i a).val + _) = _
  rw [← add_assoc, word_add_self, zero_add]

/-- The actual inverse representative's full discrepancy is an upper boundary.
The representative identities use the actual equivalence whose right inverse
is proved by `forward_backward_residual_boundary`, including its full potential. -/
theorem inverse_residual_boundary (h : ¬ i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    (BDL26FiniteCohomology.stepCocycle S i.val
        (nextBackwardCocycle S i.val (state S i.val) h w) :
      Cocycle (state S (i.val + 1)).presentation) - w ∈
      (BDL26RZCohomology.complex (state S (i.val + 1)).presentation).middleCoboundaryInCocycles := by
  let u : BDL26FiniteCohomology.Cocycle S i.val :=
    nextBackwardCocycle S i.val (state S i.val) h w
  have hf : BDL26FiniteCohomology.stepEquiv S i.val
      (BDL26FiniteCohomology.classOf S i.val u) =
      BDL26FiniteCohomology.classOf S (i.val + 1)
        (BDL26FiniteCohomology.stepCocycle S i.val u) := by
    rw [BDL26FiniteCohomology.stepEquiv_rz S i.val h]
    exact nextEquiv_mk S i.val (state S i.val) h u
  have hb : (BDL26FiniteCohomology.stepEquiv S i.val).symm
      (BDL26FiniteCohomology.classOf S (i.val + 1) w) =
      BDL26FiniteCohomology.classOf S i.val u := by
    rw [BDL26FiniteCohomology.stepEquiv_rz S i.val h]
    exact nextEquiv_symm_mk S i.val (state S i.val) h w
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change BDL26FiniteCohomology.classOf S (i.val + 1)
    (BDL26FiniteCohomology.stepCocycle S i.val u -
      (w : BDL26FiniteCohomology.Cocycle S (i.val + 1))) = 0
  rw [map_sub, ← hf, ← hb, LinearEquiv.apply_symm_apply, sub_self]

/-- The actual indexed forward word is literally the selected map1. -/
theorem inverse_forward_value (v : Cocycle (state S i.val).presentation) :
    (nextCocycle S i.val (state S i.val) v).val =
      ((indexedDecoderData S depth).selectedMap i).map1 v.val := by
  rw [selectedMap_eq]
  rfl

/-- Extract a full upper degree-zero potential from the actual residual theorem. -/
theorem inverse_residual_potential (h : ¬ i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    ∃ p : Potential S depth i,
      (indexedFamily S depth).coboundary0 i.succ p = fun q =>
        (((indexedDecoderData S depth).selectedMap i).map1
          (nextBackwardCocycle S i.val (state S i.val) h w).val) q - w.val q := by
  have hb := inverse_residual_boundary S depth i h w
  change (BDL26FiniteCohomology.stepCocycle S i.val
    (nextBackwardCocycle S i.val (state S i.val) h w)).val - w.val ∈
      (BDL26RZCohomology.complex (state S (i.val + 1)).presentation).firstCoboundaryCheckCode.carrier at hb
  obtain ⟨p, hp⟩ := (mem_boundary_iff _ _).mp hb
  refine ⟨p, ?_⟩
  rw [indexedFamily_coboundary0]
  funext q
  have hv := congrFun (inverse_forward_value S depth i
    (nextBackwardCocycle S i.val (state S i.val) h w)) q
  exact (congrFun hp q).trans (congrArg (fun x : ZMod 2 => x - w.val q) hv)

theorem potential_cocycle (p : Potential S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ p) = 0 :=
  LinearMap.congr_fun ((indexedFamily S depth).coboundary1_comp_coboundary0 i.succ) p

/-- Actual coarse validity and compatibility suffice to construct both full words.
This helper's compatibility is derived by the actual-run endpoints below. -/
theorem pullback_of_compatible (h : ¬ i.val % 2 = 0) (E : Upper S depth i)
    (tau : (indexedFamily S depth).Syndrome i.castSucc)
    (hE : (indexedFamily S depth).coboundary1 i.succ E =
      ((indexedDecoderData S depth).selectedMap i).map2 tau.val) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        E + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = tau.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 tau.val =
        (indexedFamily S depth).coboundary1 i.succ E ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 := by
  obtain ⟨v, hv⟩ := tau.property
  let r : Upper S depth i := E - ((indexedDecoderData S depth).selectedMap i).map1 v
  have hr : (indexedFamily S depth).coboundary1 i.succ r = 0 := by
    have hc := LinearMap.congr_fun
      (((indexedDecoderData S depth).selectedMap i).commutes_coboundary1) v
    change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).selectedMap i).map1 v) =
      ((indexedDecoderData S depth).selectedMap i).map2
        ((indexedFamily S depth).coboundary1 i.castSucc v) at hc
    rw [hv] at hc
    dsimp only [r]
    rw [map_sub, hE, hc, sub_self]
  let w : Cocycle (state S (i.val + 1)).presentation :=
    ⟨r, (mem_cocycle_iff _ _).mpr (by
      rw [indexedFamily_coboundary1] at hr
      exact hr)⟩
  let uRaw := nextBackwardCocycle S i.val (state S i.val) h w
  let u : {v : Lower S depth i //
      (indexedFamily S depth).coboundary1 i.castSucc v = 0} :=
    ⟨uRaw.val, by
      rw [indexedFamily_coboundary1]
      exact (mem_cocycle_iff _ _).mp uRaw.property⟩
  have hu : (indexedFamily S depth).coboundary1 i.castSucc u.val = 0 := u.property
  obtain ⟨p, hp⟩ := inverse_residual_potential S depth i h w
  refine ⟨v + u.val, p, ?_, ?_, hE.symm, potential_cocycle S depth i p⟩
  · rw [map_add, hp]
    change _ = E + (((indexedDecoderData S depth).selectedMap i).map1 u.val -
      (E - ((indexedDecoderData S depth).selectedMap i).map1 v))
    abel
  · rw [map_add, hv, hu, add_zero]

/-- The full two-run result, with no caller-supplied lower error or potential. -/
theorem two_run (_above : 2 ≤ i.val) (h : ¬ i.val % 2 = 0) (a b : Upper S depth i) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        a + b + (run S depth i h a).correction + (run S depth i h b).correction +
          (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l =
        (run S depth i h a).coarse.val + (run S depth i h b).coarse.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2
        ((run S depth i h a).coarse.val + (run S depth i h b).coarse.val) =
          (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 :=
  pullback_of_compatible S depth i h (updated S depth i h a b)
    (coarseSum S depth i h a b) (updated_delta S depth i h a b)

/-- Direct one-run update, rather than silently discarding the zero-run correction. -/
theorem one_run (_above : 2 ≤ i.val) (h : ¬ i.val % 2 = 0) (a : Upper S depth i) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        a + (run S depth i h a).correction + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = (run S depth i h a).coarse.val ∧
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val =
        (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 :=
  pullback_of_compatible S depth i h (a + (run S depth i h a).correction)
    (run S depth i h a).coarse (one_updated_delta S depth i h a)

/-- Zero coarse syndrome is established independently of the correction selector. -/
theorem zero_run_coarse (h : ¬ i.val % 2 = 0) : (run S depth i h 0).coarse.val = 0 := by
  funext z
  exact (BDL26RZDecoderAdapter.rzStepOutput_coarse_apply S depth i h
    (errorSyndrome S depth i 0) z).trans (by simp [errorSyndrome])

section History

variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)

/-- Identify the unique actual stopped-history snapshot with the same RZ selector. -/
theorem snapshot_output_eq (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.outputAt S n sigma k =
      BDL26RZDecoderAdapter.rzStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ) := by
  unfold BDL26CanonicalHistoryMarks.outputAt
  rw [actualStep_rz S (n + 2) (LevelTwoHistory.physicalStep k) h]

theorem snapshot_entry_eq (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.entryAt S n sigma k.succ =
      CorrectionHistoryEntry.step k
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (n + 2)) k
          (BDL26RZDecoderAdapter.rzStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
            (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ))) := by
  rw [BDL26CanonicalHistoryMarks.entryAt_step, snapshot_output_eq S n sigma k h]

/-- Genuine history inputs supply source errors internally; the lower error and
full potential are then obtained from the actual two-run theorem. -/
theorem snapshot_two_run (sigmaB : BDL26CanonicalHistoryMarks.Input S n)
    (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    ∃ (a b : Upper S (n + 2) (LevelTwoHistory.physicalStep k))
      (l : Lower S (n + 2) (LevelTwoHistory.physicalStep k))
      (p : Potential S (n + 2) (LevelTwoHistory.physicalStep k)),
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ a =
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ).val ∧
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ b =
        (BDL26CanonicalHistoryMarks.inputAt S n sigmaB k.succ).val ∧
      ((indexedDecoderData S (n + 2)).selectedMap (LevelTwoHistory.physicalStep k)).map1 l =
        a + b + (BDL26CanonicalHistoryMarks.outputAt S n sigma k).correction +
          (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).correction +
            (indexedFamily S (n + 2)).coboundary0 (LevelTwoHistory.physicalStep k).succ p ∧
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).castSucc l =
        (BDL26CanonicalHistoryMarks.outputAt S n sigma k).coarse.val +
          (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).coarse.val ∧
      ((indexedDecoderData S (n + 2)).selectedMap (LevelTwoHistory.physicalStep k)).map2
        ((BDL26CanonicalHistoryMarks.outputAt S n sigma k).coarse.val +
          (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).coarse.val) =
        (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ
          (a + b + (BDL26CanonicalHistoryMarks.outputAt S n sigma k).correction +
            (BDL26CanonicalHistoryMarks.outputAt S n sigmaB k).correction) ∧
      (indexedFamily S (n + 2)).coboundary1 (LevelTwoHistory.physicalStep k).succ
        ((indexedFamily S (n + 2)).coboundary0 (LevelTwoHistory.physicalStep k).succ p) = 0 := by
  obtain ⟨a, ha⟩ := (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ).property
  obtain ⟨b, hb⟩ := (BDL26CanonicalHistoryMarks.inputAt S n sigmaB k.succ).property
  have hsa : errorSyndrome S (n + 2) (LevelTwoHistory.physicalStep k) a =
      BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ := Subtype.ext ha
  have hsb : errorSyndrome S (n + 2) (LevelTwoHistory.physicalStep k) b =
      BDL26CanonicalHistoryMarks.inputAt S n sigmaB k.succ := Subtype.ext hb
  have hoa : run S (n + 2) (LevelTwoHistory.physicalStep k) h a =
      BDL26CanonicalHistoryMarks.outputAt S n sigma k := by
    rw [run, hsa]
    exact (snapshot_output_eq S n sigma k h).symm
  have hob : run S (n + 2) (LevelTwoHistory.physicalStep k) h b =
      BDL26CanonicalHistoryMarks.outputAt S n sigmaB k := by
    rw [run, hsb]
    exact (snapshot_output_eq S n sigmaB k h).symm
  obtain ⟨l, p, hl, hs, hm, hp⟩ := two_run S (n + 2) (LevelTwoHistory.physicalStep k)
    (by change 2 ≤ k.val + 2; omega) h a b
  refine ⟨a, b, l, p, ha, hb, ?_, ?_, ?_, hp⟩
  · simpa only [hoa, hob] using hl
  · simpa only [hoa, hob] using hs
  · simpa only [updated, hoa, hob] using hm

end History

end QEC.Coding.BDL26RZErrorPullback

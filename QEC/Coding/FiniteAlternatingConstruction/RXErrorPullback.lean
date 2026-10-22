import QEC.Coding.FiniteAlternatingConstruction.RXCohomology.Indexed
import QEC.Coding.FiniteAlternatingConstruction.FiniteCohomology
import QEC.Coding.FiniteAlternatingConstruction.RXErrorPullback.EmbeddedReadout
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.CanonicalHistoryMarks.Snapshots

/-!
# Full actual RX updated-error pullback

The full updated error includes the original error and the actual selected
correction. The resulting lower error is constructed using actual coarse
validity and the proved RX H¹ inverse. Its stabilizer potential is a full
upper degree-zero word. BDL26 `paper.tex:2320–2375,1821–1935,2746–2806`
supplies the actual coarse relation and RX cohomology context; this is a
project-derived global algebraic consequence. No support or parent-locality claim is made here.
-/

noncomputable section
namespace QEC.Coding.BDL26RXErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RXCohomology BDL26AlternatingCochain
open BDL26RZCohomology (mem_cocycle_iff mem_boundary_iff)
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

/-- The selected actual RX output, with its correction retained even at zero. -/
def run (h : i.val % 2 = 0) (a : Upper S depth i) :
    AssemblyStepOutput (indexedDecoderData S depth) i :=
  BDL26RXDecoderAdapter.rxStepOutput S depth i h (errorSyndrome S depth i a)

def updated (h : i.val % 2 = 0) (a b : Upper S depth i) : Upper S depth i :=
  a + b + (run S depth i h a).correction + (run S depth i h b).correction

/-- Validity of this sum is derived from the actual two coarse outputs. -/
def coarseSum (h : i.val % 2 = 0) (a b : Upper S depth i) :
    (indexedFamily S depth).Syndrome i.castSucc :=
  ⟨(run S depth i h a).coarse.val + (run S depth i h b).coarse.val,
    ((indexedFamily S depth).syndromeSubmodule i.castSucc).add_mem
      (run S depth i h a).coarse.property (run S depth i h b).coarse.property⟩

theorem correction_delta (h : i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h a).correction =
      (errorSyndrome S depth i a).val +
        ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  have hr := BDL26RXDecoderAdapter.rxStepOutput_relation S depth i h (errorSyndrome S depth i a)
  funext z
  exact (CharTwo.eq_add_iff_add_eq.mp (congrFun hr z)).symm

/-- Bare corrections retain the original syndrome difference. -/
theorem correction_difference_delta (h : i.val % 2 = 0) (a b : Upper S depth i) :
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
theorem updated_delta (h : i.val % 2 = 0) (a b : Upper S depth i) :
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

theorem one_updated_delta (h : i.val % 2 = 0) (a : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (a + (run S depth i h a).correction) =
      ((indexedDecoderData S depth).selectedMap i).map2 (run S depth i h a).coarse.val := by
  rw [map_add, correction_delta]
  change (errorSyndrome S depth i a).val + ((errorSyndrome S depth i a).val + _) = _
  rw [← add_assoc, word_add_self, zero_add]

/-- Choose an actual lower cocycle representing the proved RX quotient inverse.
The only input is the upper cocycle; no inverse or normal form is supplied. -/
def inverseCocycle (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    Cocycle (state S i.val).presentation :=
  Classical.choose ((complex (state S i.val).presentation).middleCoboundaryInCocycles.mkQ_surjective
    ((nextEquiv S i.val (state S i.val) h).symm
      (classOf (state S (i.val + 1)).presentation w)))

/-- Its quotient class is exactly the actual RX H¹ inverse. -/
theorem inverseCocycle_class (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    classOf (state S i.val).presentation (inverseCocycle S depth i h w) =
      (nextEquiv S i.val (state S i.val) h).symm
        (classOf (state S (i.val + 1)).presentation w) :=
  Classical.choose_spec ((complex (state S i.val).presentation).middleCoboundaryInCocycles.mkQ_surjective
    ((nextEquiv S i.val (state S i.val) h).symm
      (classOf (state S (i.val + 1)).presentation w)))

/-- The proved quotient right inverse makes the entire forward discrepancy
an actual upper boundary, rather than just zero on a selected sector. -/
theorem inverse_residual_boundary (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    (BDL26FiniteCohomology.stepCocycle S i.val (inverseCocycle S depth i h w) :
      Cocycle (state S (i.val + 1)).presentation) - w ∈
      (complex (state S (i.val + 1)).presentation).middleCoboundaryInCocycles := by
  let u : BDL26FiniteCohomology.Cocycle S i.val := inverseCocycle S depth i h w
  have hf := BDL26FiniteCohomology.stepEquiv_mk S i.val u
  have hb : (BDL26FiniteCohomology.stepEquiv S i.val).symm
      (BDL26FiniteCohomology.classOf S (i.val + 1) w) =
      BDL26FiniteCohomology.classOf S i.val u := by
    rw [BDL26FiniteCohomology.stepEquiv_rx S i.val h]
    exact (inverseCocycle_class S depth i h w).symm
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
theorem inverse_residual_potential (h : i.val % 2 = 0)
    (w : Cocycle (state S (i.val + 1)).presentation) :
    ∃ p : Potential S depth i,
      (indexedFamily S depth).coboundary0 i.succ p = fun q =>
        (((indexedDecoderData S depth).selectedMap i).map1
          (inverseCocycle S depth i h w).val) q - w.val q := by
  have hb := inverse_residual_boundary S depth i h w
  change (BDL26FiniteCohomology.stepCocycle S i.val
    (inverseCocycle S depth i h w)).val - w.val ∈
      (BDL26RXCohomology.complex (state S (i.val + 1)).presentation).firstCoboundaryCheckCode.carrier at hb
  obtain ⟨p, hp⟩ := (mem_boundary_iff _ _).mp hb
  refine ⟨p, ?_⟩
  rw [indexedFamily_coboundary0]
  funext q
  have hv := congrFun (inverse_forward_value S depth i (inverseCocycle S depth i h w)) q
  exact (congrFun hp q).trans (congrArg (fun x : ZMod 2 => x - w.val q) hv)

theorem potential_cocycle (p : Potential S depth i) :
    (indexedFamily S depth).coboundary1 i.succ
      ((indexedFamily S depth).coboundary0 i.succ p) = 0 :=
  LinearMap.congr_fun ((indexedFamily S depth).coboundary1_comp_coboundary0 i.succ) p

/-- Actual coarse validity and compatibility suffice to construct both full words.
This helper's compatibility is derived by the actual-run endpoints below. -/
theorem pullback_of_compatible (h : i.val % 2 = 0) (E : Upper S depth i)
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
  let uRaw := inverseCocycle S depth i h w
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
theorem two_run (_above : 2 ≤ i.val) (h : i.val % 2 = 0) (a b : Upper S depth i) :
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
theorem one_run (_above : 2 ≤ i.val) (h : i.val % 2 = 0) (a : Upper S depth i) :
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

/-- The coarse zero word follows from the actual RX factor-two inequality.
The actual correction at zero is retained, not assumed to vanish. -/
theorem zero_run_coarse (h : i.val % 2 = 0) : (run S depth i h 0).coarse.val = 0 := by
  apply (HammingWeight_eq_zero_iff _).mp
  have hw := BDL26RXDecoderAdapter.rxStepOutput_weight S depth i h (errorSyndrome S depth i 0)
  have hs : (errorSyndrome S depth i 0).val = 0 := by simp [errorSyndrome]
  rw [hs, HammingWeight_zero] at hw
  change 2 * HammingWeight (run S depth i h 0).coarse.val ≤ 0 at hw
  omega

/-- Even a non-normalized zero-run correction is an actual cocycle. -/
theorem zero_run_correction_cocycle (h : i.val % 2 = 0) :
    (indexedFamily S depth).coboundary1 i.succ (run S depth i h 0).correction = 0 := by
  rw [correction_delta, zero_run_coarse]
  simp [errorSyndrome]

/-- Direct zero-input pullback does not discard its selected correction. -/
theorem zero_run_pullback (above : 2 ≤ i.val) (h : i.val % 2 = 0) :
    ∃ (l : Lower S depth i) (p : Potential S depth i),
      ((indexedDecoderData S depth).selectedMap i).map1 l =
        (run S depth i h 0).correction + (indexedFamily S depth).coboundary0 i.succ p ∧
      (indexedFamily S depth).coboundary1 i.castSucc l = 0 ∧
      (indexedFamily S depth).coboundary1 i.succ (run S depth i h 0).correction = 0 ∧
      (indexedFamily S depth).coboundary1 i.succ
        ((indexedFamily S depth).coboundary0 i.succ p) = 0 := by
  obtain ⟨l,p,hl,hd,_,hp⟩ := one_run S depth i above h 0
  exact ⟨l,p,by simpa only [zero_add] using hl,
    by simpa only [zero_run_coarse] using hd,zero_run_correction_cocycle S depth i h,hp⟩

/-- The real selected RX degree-one lift of a complete lower error. -/
def liftError (a : Lower S depth i) : Upper S depth i :=
  ((indexedDecoderData S depth).rxMap i).map1 a

/-- The lift's actual syndrome is exactly the embedded lower coboundary. -/
theorem lift_errorSyndrome (h : i.val % 2 = 0) (a : Lower S depth i) :
    errorSyndrome S depth i (liftError S depth i a) =
      embeddedSyndrome S depth i h
        ⟨(indexedFamily S depth).coboundary1 i.castSucc a, ⟨a,rfl⟩⟩ := by
  apply Subtype.ext
  exact LinearMap.congr_fun (((indexedDecoderData S depth).rxMap i).commutes_coboundary1) a

/-- A genuine lifted error realizes the entire prescribed coarse syndrome. -/
theorem lifted_run_coarse (h : i.val % 2 = 0) (a : Lower S depth i) :
    (run S depth i h (liftError S depth i a)).coarse.val =
      (indexedFamily S depth).coboundary1 i.castSucc a := by
  rw [run, lift_errorSyndrome]
  exact embedded_coarse S depth i h _

/-- A zero comparison retains its correction while its coarse value vanishes. -/
theorem lifted_zero_coarseSum (h : i.val % 2 = 0) (a : Lower S depth i) :
    (coarseSum S depth i h (liftError S depth i a) 0).val =
      (indexedFamily S depth).coboundary1 i.castSucc a := by
  change (run S depth i h (liftError S depth i a)).coarse.val +
    (run S depth i h 0).coarse.val = _
  rw [lifted_run_coarse, zero_run_coarse, add_zero]

section History

variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)

/-- Identify the unique actual stopped-history snapshot with the same RX selector. -/
theorem snapshot_output_eq (h : (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.outputAt S n sigma k =
      BDL26RXDecoderAdapter.rxStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ) := by
  unfold BDL26CanonicalHistoryMarks.outputAt
  rw [actualStep_rx S (n + 2) (LevelTwoHistory.physicalStep k) h]

theorem snapshot_entry_eq (h : (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.entryAt S n sigma k.succ =
      CorrectionHistoryEntry.step k
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (n + 2)) k
          (BDL26RXDecoderAdapter.rxStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
            (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ))) := by
  rw [BDL26CanonicalHistoryMarks.entryAt_step, snapshot_output_eq S n sigma k h]

/-- Genuine history inputs supply source errors internally; the lower error and
full potential are then obtained from the actual two-run theorem. -/
theorem snapshot_two_run (sigmaB : BDL26CanonicalHistoryMarks.Input S n)
    (h : (LevelTwoHistory.physicalStep k).val % 2 = 0) :
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

end QEC.Coding.BDL26RXErrorPullback

import QEC.Coding.FiniteAlternatingConstruction.TransposedStoppedDecoder.Base
import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.History
import QEC.Coding.CSS.DaviesLocality
import QEC.Coding.CSS.Distance

/-!
# Actual transposed stopped decoder and physical two-sector consumers

The complete correction is the lifted sum of the literal C2-stopped history,
including its full base correction. The original X decoder is combined with
this dual Z decoder on the same physical carrier. All binary phases remain
explicit; no stability or projected-commutator premise occurs here.
-/

noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RZMap1CoordinateBridge MultiscaleDecoder
open PauliSymplectic BDL26CSSHamiltonian
open scoped Classical BigOperators

/-- The literal C2 lookup on the suffix family's actual base input. -/
def dualBase (S : OddScale) (n : Nat) :
    AuditedBaseDecoder (LevelTwoHistory.suffixData (dualDecoderData S (n + 2))) :=
  LevelTwoHistory.suffixBase _ (fun sigma => dualBaseDecode S sigma.val) (by
    intro sigma
    have hs : sigma.val ∈ LinearMap.range
        ((dualFamily S (n + 2)).coboundary1
          (LevelTwoHistory.physicalLevel (0 : LevelIndex n))) := sigma.property
    obtain ⟨w,hw⟩ := hs
    have hd := dualFamily_coboundary1 S (n + 2)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n))
    exact (LinearMap.congr_fun hd _).trans
      (dualBaseDecode_syndrome S sigma.val
        ⟨w,(LinearMap.congr_fun hd w).symm.trans hw⟩))

/-- No history or stopping certificate is supplied by a caller. -/
def dualHistory (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    CorrectionHistory (LevelTwoHistory.suffixData (dualDecoderData S (n + 2))) :=
  LevelTwoHistory.stoppedHistory _ (dualAboveTwoSteps S n) (dualBase S n) sigma

theorem dualHistory_length (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (dualHistory S n sigma).length = n + 1 :=
  LevelTwoHistory.stoppedHistory_length _ (dualAboveTwoSteps S n) (dualBase S n) sigma

theorem dualHistory_syndrome (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    (dualFamily S (n + 2)).coboundary1 (TopIndex (n + 2))
      (historyLiftedCorrection (LevelTwoHistory.suffixData (dualDecoderData S (n + 2)))
        (dualHistory S n sigma)) = sigma.val :=
  LevelTwoHistory.stoppedHistory_syndrome _ (dualAboveTwoSteps S n) (dualBase S n) sigma

/-- A zero syndrome preserves all zero inputs without erasing chosen local cycles. -/
theorem dualHistory_zero_inputs (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) (hs : sigma.val = 0) :
    ∀ e ∈ dualHistory S n sigma, e.inputSyndrome.2.val = 0 :=
  LevelTwoHistory.stoppedHistory_zero_inputs _ (dualAboveTwoSteps S n) (dualBase S n)
    (fun i _ sigma hz => dualStepOutput_zero_coarse S (n + 2) i sigma hz) sigma hs

theorem dualHistory_readout_below_two (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (i : LevelIndex (n + 2)) (hi : i.val < 2) :
    LevelTwoHistory.syndromeReadout (dualDecoderData S (n + 2)) (dualHistory S n sigma) i = 0 :=
  LevelTwoHistory.syndromeReadout_below_two _ _ i hi

theorem dualHistory_base_readout (S : OddScale) (n : Nat)
    (sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2))) :
    LevelTwoHistory.syndromeReadout (dualDecoderData S (n + 2)) (dualHistory S n sigma)
      (LevelTwoHistory.physicalLevel (0 : LevelIndex n)) =
      (terminalInput (LevelTwoHistory.suffixData (dualDecoderData S (n + 2)))
        (LevelTwoHistory.suffixSteps _ (dualAboveTwoSteps S n)) sigma).val :=
  LevelTwoHistory.stoppedHistory_base_readout _ (dualAboveTwoSteps S n) (dualBase S n) sigma

/-- The actual head step and the entire tail are retained. -/
theorem dualHistory_head (S : OddScale) (m : Nat)
    (sigma : (dualFamily S ((m + 1) + 2)).Syndrome (TopIndex ((m + 1) + 2))) :
    ∃ tail, dualHistory S (m + 1) sigma =
      CorrectionHistoryEntry.step (Fin.last m)
        (LevelTwoHistory.suffixOutput _ (Fin.last m)
          ((dualAboveTwoSteps S (m + 1)).step
            (LevelTwoHistory.physicalStep (Fin.last m)) (by simp [LevelTwoHistory.physicalStep]) sigma)) :: tail :=
  LevelTwoHistory.stoppedHistory_head m _ (dualAboveTwoSteps S (m + 1)) (dualBase S (m + 1)) sigma

/-- Genuine realizable original Z-check syndromes, with their actual carrier. -/
abbrev XSyndromeDomain (S : OddScale) (n : Nat) := LinearMap.range (zSyndrome S (n + 2))
/-- Genuine realizable original X-check syndromes, on the same physical word carrier. -/
abbrev ZSyndromeDomain (S : OddScale) (n : Nat) := LinearMap.range (xSyndrome S (n + 2))

/-- The existing original stopped correction, including its original C2 term. -/
def xCorrection (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    Word BDL26Field (Physical S (n + 2)) := by
  let sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)) := ⟨u.val,by
    change u.val ∈ LinearMap.range
      ((indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
    obtain ⟨w,hw⟩ := u.property
    exact ⟨w,(LinearMap.congr_fun
      (indexedFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans hw⟩⟩
  exact historyLiftedCorrection (LevelTwoHistory.suffixData (indexedDecoderData S (n + 2)))
    (BDL26OwnerIncidenceMasks.actualHistory S n sigma)

theorem xCorrection_syndrome (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    zSyndrome S (n + 2) (xCorrection S n u) = u.val := by
  unfold xCorrection
  have h := BDL26OwnerIncidenceMasks.actualHistory_syndrome S n
    (⟨u.val,by
      change u.val ∈ LinearMap.range
        ((indexedFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
      obtain ⟨w,hw⟩ := u.property
      exact ⟨w,(LinearMap.congr_fun
        (indexedFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans hw⟩⟩)
  exact (LinearMap.congr_fun
    (indexedFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) _).symm.trans h

/-- The full dual correction is computed from this very same stopped history. -/
def zCorrection (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n) :
    Word BDL26Field (Physical S (n + 2)) := by
  let sigma : (dualFamily S (n + 2)).Syndrome (TopIndex (n + 2)) := ⟨v.val,by
    change v.val ∈ LinearMap.range
      ((dualFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,((LinearMap.congr_fun
      (dualFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans
      (LinearMap.congr_fun (dual_coboundary1_xSyndrome S (n + 2)) w)).trans hw⟩⟩
  exact historyLiftedCorrection (LevelTwoHistory.suffixData (dualDecoderData S (n + 2)))
    (dualHistory S n sigma)

/-- Same physical carrier and literal original X-check syndrome, for every n>=0. -/
theorem zCorrection_syndrome (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n) :
    xSyndrome S (n + 2) (zCorrection S n v) = v.val := by
  unfold zCorrection
  have h := dualHistory_syndrome S n
    (⟨v.val,by
      change v.val ∈ LinearMap.range
        ((dualFamily S (n + 2)).coboundary1 (TopIndex (n + 2)))
      obtain ⟨w,hw⟩ := v.property
      exact ⟨w,((LinearMap.congr_fun
        (dualFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) w).trans
        (LinearMap.congr_fun (dual_coboundary1_xSyndrome S (n + 2)) w)).trans hw⟩⟩)
  exact ((LinearMap.congr_fun
    (dualFamily_coboundary1 S (n + 2) (TopIndex (n + 2))) _).trans
    (LinearMap.congr_fun (dual_coboundary1_xSyndrome S (n + 2)) _)).symm.trans h

/-- Source-even indices cover precisely the physical levels with k>=1. -/
theorem source_even_level (k : Nat) (hk : 1 ≤ k) : 2 * (k - 1) + 2 = 2 * k := by omega

/-- Physical C2 really stops immediately and retains the entire base correction. -/
theorem zCorrection_level_two (S : OddScale) (v : ZSyndromeDomain S 0) :
    zCorrection S 0 v = dualBaseDecode S v.val := by
  let sigma : (dualFamily S 2).Syndrome (TopIndex 2) := ⟨v.val,by
    change v.val ∈ LinearMap.range ((dualFamily S 2).coboundary1 (TopIndex 2))
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,((LinearMap.congr_fun (dualFamily_coboundary1 S 2 (TopIndex 2)) w).trans
      (LinearMap.congr_fun (dual_coboundary1_xSyndrome S 2) w)).trans hw⟩⟩
  let D := LevelTwoHistory.suffixData (dualDecoderData S 2)
  have hstop := buildCorrectionHistory_zero D
    (LevelTwoHistory.suffixSteps (dualDecoderData S 2) (dualAboveTwoSteps S 0))
    (dualBase S 0) sigma
  change historyLiftedCorrection D
    (buildCorrectionHistory D
      (LevelTwoHistory.suffixSteps (dualDecoderData S 2) (dualAboveTwoSteps S 0))
      (dualBase S 0) sigma) = dualBaseDecode S v.val
  apply (congrArg (historyLiftedCorrection D) hstop).trans
  simp only [historyLiftedCorrection,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,CorrectionHistoryEntry.correction]
  exact liftCorrection_top D ((dualBase S 0).decode sigma)

/-- Source-even physical correction; k=0 is not admitted as a C2 stop. -/
def zCorrectionEven (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (v : LinearMap.range (xSyndrome S (2 * k))) : Word BDL26Field (Physical S (2 * k)) :=
  cast (congrArg (fun m => Word BDL26Field (Physical S m)) (source_even_level k hk))
    (zCorrection S (2 * (k - 1))
      (cast (congrArg (fun m => ↥(LinearMap.range (xSyndrome S m)))
        (source_even_level k hk)).symm v))

/-- A physical error translates the original Z-check sector. -/
def translateX (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (a : Word BDL26Field (Physical S (n + 2))) : XSyndromeDomain S n :=
  ⟨u.val + zSyndrome S (n + 2) a,by
    obtain ⟨w,hw⟩ := u.property
    exact ⟨w+a,by rw [map_add,hw]⟩⟩

/-- The same physical error's Z word translates the original X-check sector. -/
def translateZ (S : OddScale) (n : Nat) (v : ZSyndromeDomain S n)
    (b : Word BDL26Field (Physical S (n + 2))) : ZSyndromeDomain S n :=
  ⟨v.val + xSyndrome S (n + 2) b,by
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w+b,by rw [map_add,hw]⟩⟩

/-- X then Z on the actual common physical carrier, retaining the stored phase. -/
def pairedCorrection (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) : Binary (Physical S (n + 2)) :=
  binaryMul (cssXCheck (xCorrection S n u)) (cssZCheck (zCorrection S n v))

@[simp] theorem pairedCorrection_phase (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) :
    (pairedCorrection S n u v).phase = 0 := by
  simp [pairedCorrection,binaryMul,binaryMulPhase]

/-- Both actual syndrome coordinates, without an abstract output chooser. -/
theorem pairedCorrection_syndromes (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) :
    zSyndrome S (n + 2) (pairedCorrection S n u v).vector.xPart = u.val ∧
    xSyndrome S (n + 2) (pairedCorrection S n u v).vector.zPart = v.val := by
  simpa [pairedCorrection,binaryMul] using
    And.intro (xCorrection_syndrome S n u) (zCorrection_syndrome S n v)

/-- The actual binary composite before any phase is forgotten. -/
def pairedResidual (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) : Binary (Physical S (n + 2)) :=
  binaryMul (pairedCorrection S n (translateX S n u E.vector.xPart)
      (translateZ S n v E.vector.zPart)) (binaryMul E (pairedCorrection S n u v))

/-- Full X residual, including both independently computed background corrections. -/
theorem pairedResidual_xPart (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    (pairedResidual S n u v E).vector.xPart =
      xCorrection S n (translateX S n u E.vector.xPart) + E.vector.xPart + xCorrection S n u := by
  simp [pairedResidual,pairedCorrection,binaryMul,add_assoc]

/-- Full Z residual on that very same physical carrier. -/
theorem pairedResidual_zPart (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    (pairedResidual S n u v E).vector.zPart =
      zCorrection S n (translateZ S n v E.vector.zPart) + E.vector.zPart + zCorrection S n v := by
  simp [pairedResidual,pairedCorrection,binaryMul,add_assoc]

/-- The stored binary sign includes the nonzero-background overlap term. -/
theorem pairedResidual_phase (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    (pairedResidual S n u v E).phase = E.phase +
      (∑ q, xCorrection S n u q * E.vector.zPart q) +
      ∑ q, (E.vector.xPart q + xCorrection S n u q) *
        zCorrection S n (translateZ S n v E.vector.zPart) q := by
  simp [pairedResidual,pairedCorrection,binaryMul,binaryMulPhase,add_assoc]

/-- Correctness proves both residuals closed; it does not prove either is a boundary. -/
theorem pairedResidual_closed (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2))) :
    zSyndrome S (n + 2) (pairedResidual S n u v E).vector.xPart = 0 ∧
    xSyndrome S (n + 2) (pairedResidual S n u v E).vector.zPart = 0 := by
  constructor
  · rw [pairedResidual_xPart,map_add,map_add,xCorrection_syndrome,xCorrection_syndrome]
    funext z
    change (u.val z + zSyndrome S (n + 2) E.vector.xPart z) +
      zSyndrome S (n + 2) E.vector.xPart z + u.val z = 0
    calc
      _ = (u.val z + u.val z) +
          (zSyndrome S (n + 2) E.vector.xPart z + zSyndrome S (n + 2) E.vector.xPart z) := by abel
      _ = 0 := by simp [ZModModule.add_self]
  · rw [pairedResidual_zPart,map_add,map_add,zCorrection_syndrome,zCorrection_syndrome]
    funext x
    change (v.val x + xSyndrome S (n + 2) E.vector.zPart x) +
      xSyndrome S (n + 2) E.vector.zPart x + v.val x = 0
    calc
      _ = (v.val x + v.val x) +
          (xSyndrome S (n + 2) E.vector.zPart x + xSyndrome S (n + 2) E.vector.zPart x) := by abel
      _ = 0 := by simp [ZModModule.add_self]

/-- Ordinary actual row-boundary premises imply group membership up to sign.
The stored phase remains present and no exact generatedGroup conclusion is asserted. -/
theorem pairedResidual_inGeneratedGroupUpToSign_of_boundaries (S : OddScale) (n : Nat)
    (u : XSyndromeDomain S n) (v : ZSyndromeDomain S n) (E : Binary (Physical S (n + 2)))
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (pairedResidual S n u v E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (pairedResidual S n u v E).vector.zPart) :
    (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S (n + 2)) (xSyndrome S (n + 2))
      (row_orthogonal S (n + 2))).InGeneratedGroupUpToSign (pairedResidual S n u v E) := by
  apply (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff _ _ _ _).mpr
  exact ⟨hx,hz⟩

/-- Actual Y changes both sectors. Its Hermitian operator retains i*(X*Z). -/
theorem actual_Y_operator (S : OddScale) (n : Nat) (q : Physical S (n + 2)) :
    CSSDaviesLocality.coupling q .y = Complex.I •
      (Semantics.Qubit.localX q * Semantics.Qubit.localZ q) :=
  CSSDaviesLocality.coupling_y q

private theorem rightInverse_cast (S : OddScale) {m r : Nat} (h : m = r)
    (f : LinearMap.range (xSyndrome S m) → Word BDL26Field (Physical S m))
    (hf : ∀ v, xSyndrome S m (f v) = v.val)
    (v : LinearMap.range (xSyndrome S r)) :
    xSyndrome S r (cast (congrArg (fun l => Word BDL26Field (Physical S l)) h)
      (f (cast (congrArg (fun l => ↥(LinearMap.range (xSyndrome S l))) h).symm v))) = v.val := by
  cases h
  exact hf v

/-- The source-even wrapper has the literal physical syndrome for every k>=1. -/
theorem zCorrectionEven_syndrome (S : OddScale) (k : Nat) (hk : 1 ≤ k)
    (v : LinearMap.range (xSyndrome S (2 * k))) :
    xSyndrome S (2 * k) (zCorrectionEven S k hk v) = v.val :=
  rightInverse_cast S (source_even_level k hk) (zCorrection S (2 * (k - 1)))
    (zCorrection_syndrome S (2 * (k - 1))) v

/-- Both translated sectors are read from the actual singleton Pauli word. -/
def basisTranslations (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (q : Physical S (n + 2)) (a : CSSDaviesLocality.Axis) :=
  (translateX S n u (CSSDaviesLocality.singlePauli q a).vector.xPart,
    translateZ S n v (CSSDaviesLocality.singlePauli q a).vector.zPart)

theorem basisTranslations_X (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (q : Physical S (n + 2)) :
    (basisTranslations S n u v q .x).1.val = u.val + zSyndrome S (n + 2) (Pi.single q 1) ∧
    (basisTranslations S n u v q .x).2.val = v.val := by
  simp [basisTranslations,CSSDaviesLocality.singlePauli,translateX,translateZ]

theorem basisTranslations_Y (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (q : Physical S (n + 2)) :
    (basisTranslations S n u v q .y).1.val = u.val + zSyndrome S (n + 2) (Pi.single q 1) ∧
    (basisTranslations S n u v q .y).2.val = v.val + xSyndrome S (n + 2) (Pi.single q 1) := by
  exact ⟨rfl,rfl⟩

theorem basisTranslations_Z (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (v : ZSyndromeDomain S n) (q : Physical S (n + 2)) :
    (basisTranslations S n u v q .z).1.val = u.val ∧
    (basisTranslations S n u v q .z).2.val = v.val + xSyndrome S (n + 2) (Pi.single q 1) := by
  simp [basisTranslations,CSSDaviesLocality.singlePauli,translateX,translateZ]

/-- The raw binary Y representative is XZ, whereas its Hermitian operator has phase i. -/
theorem actual_Y_binary (S : OddScale) (n : Nat) (q : Physical S (n + 2)) :
    CSSDaviesLocality.singlePauli q .y =
      binaryMul (cssXCheck (Pi.single q 1)) (cssZCheck (Pi.single q 1)) := by
  simp [CSSDaviesLocality.singlePauli,binaryMul,binaryMulPhase]

/-- An actual incident check evaluates a singleton word to one. -/
private theorem singleton_incident_coboundary (P : TannerSquarePresentation)
    (q : P.Q) (z : P.Z) (hqz : P.qz q z = true) :
    tannerCoboundary1 P (Pi.single q (1 : BDL26Field)) z = 1 := by
  change (∑ r : P.Q, (Pi.single q (1 : BDL26Field) : Word BDL26Field P.Q) r *
    (if P.qz r z = true then (1 : BDL26Field) else 0)) = (1 : BDL26Field)
  rw [Fintype.sum_eq_single q]
  · simp only [Pi.single_eq_same,hqz,if_true,mul_one]
  · intro r hr
    rw [Pi.single_eq_of_ne hr,zero_mul]

/-- Every actual physical singleton has a nonzero original Z-check syndrome. -/
theorem singleton_zSyndrome_ne_zero (S : OddScale) (n : Nat) (q : Physical S n) :
    zSyndrome S n (Pi.single q 1) ≠ 0 := by
  let A := (state S n).admissible.toTannerSquareAdmissible
  intro h
  have hz := congrFun h (A.qzRoot q).val
  have hone : zSyndrome S n (Pi.single q 1) (A.qzRoot q).val = 1 := by
    exact singleton_incident_coboundary (state S n).presentation q
      (A.qzRoot q).val (A.qzRoot q).property
  rw [hone] at hz
  exact one_ne_zero hz

/-- Every actual physical singleton also has a nonzero original X-check syndrome. -/
theorem singleton_xSyndrome_ne_zero (S : OddScale) (n : Nat) (q : Physical S n) :
    xSyndrome S n (Pi.single q 1) ≠ 0 := by
  let A := (state S n).admissible.toTannerSquareAdmissible
  intro h
  have hx := congrFun h (A.xqRoot q).val
  have hone : xSyndrome S n (Pi.single q 1) (A.xqRoot q).val = 1 := by
    have hd := LinearMap.congr_fun (xSyndrome_transposed S n) (Pi.single q 1)
    exact (congrFun hd (A.xqRoot q).val).trans
      (singleton_incident_coboundary (transposePresentation (state S n).presentation)
        q (A.xqRoot q).val (A.xqRoot q).property)
  rw [hone] at hx
  exact one_ne_zero hx

end QEC.Coding.BDL26TransposedStoppedDecoder
end

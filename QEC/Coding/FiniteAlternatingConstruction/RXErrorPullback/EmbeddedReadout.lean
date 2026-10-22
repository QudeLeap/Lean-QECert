import QEC.Coding.FiniteAlternatingConstruction.RXDecoderAdapter

/-! # Actual RX readout on a lifted lower syndrome

Local selectors depend only on their actual input restrictions. A map2 image
has zero X/Q input, so its selected correction agrees with the actual zero
run. That correction may be a nonzero cycle; its coboundary still vanishes.
-/
noncomputable section
namespace QEC.Coding.BDL26RXErrorPullback
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

private abbrev Data := rxData S depth i h

private theorem cx_total_eq_of_x_eq
    (sigma tau : (indexedFamily S depth).Cochain2 i.succ)
    (hx : ∀ x, restrictWordLinear ((rxLx S depth i h).syndromeRegion x) sigma =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion x) tau) :
    cxCorrectionTotal (Data S depth i h) sigma = cxCorrectionTotal (Data S depth i h) tau := by
  let chooseX (x : (state S i.val).presentation.X)
      (v : Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).syndromeRegion x))) :
      (indexedFamily S depth).Correction i.succ :=
    if hv : v ∈ LinearMap.range ((Data S depth i h).contract.rx_local_complexes.cxDelta1 x) then
      extendWordLinear ((rxLx S depth i h).correctionRegion x)
        (Classical.choose ((Data S depth i h).contract.local_boundary_weight_budgets.cx x v hv))
    else 0
  change (∑ x, chooseX x (restrictWordLinear ((rxLx S depth i h).syndromeRegion x) sigma)) =
    ∑ x, chooseX x (restrictWordLinear ((rxLx S depth i h).syndromeRegion x) tau)
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg (chooseX x) (hx x)

private theorem cq_total_eq_of_cleaned_q_eq
    (sigma tau : (indexedFamily S depth).Cochain2 i.succ)
    (hq : ∀ q, restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
        (rxSigmaAfterCx (Data S depth i h) sigma) =
      restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
        (rxSigmaAfterCx (Data S depth i h) tau)) :
    cqCorrectionTotal (Data S depth i h) sigma = cqCorrectionTotal (Data S depth i h) tau := by
  let chooseQ (q : (state S i.val).presentation.Q)
      (v : Word BDL26Field (LocalRegionIndex ((rxLq S depth i h).syndromeRegion q))) :
      (indexedFamily S depth).Correction i.succ :=
    if hv : v ∈ LinearMap.range ((Data S depth i h).contract.rx_local_complexes.cqDelta1 q) then
      extendWordLinear ((rxLq S depth i h).correctionRegion q)
        (Classical.choose ((Data S depth i h).contract.local_boundary_weight_budgets.cq q v hv))
    else 0
  change (∑ q, chooseQ q (restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (rxSigmaAfterCx (Data S depth i h) sigma))) =
    ∑ q, chooseQ q (restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (rxSigmaAfterCx (Data S depth i h) tau))
  apply Finset.sum_congr rfl
  intro q _
  exact congrArg (chooseQ q) (hq q)

private theorem map2_restrict_x_zero
    (s : (indexedFamily S depth).Cochain2 i.castSucc) (x : (state S i.val).presentation.X) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
      (((indexedDecoderData S depth).rxMap i).map2 s) = 0 := by
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.1) _ hz
  rw [(Data S depth i h).xSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.property⟩

private theorem map2_restrict_q_zero
    (s : (indexedFamily S depth).Cochain2 i.castSucc) (q : (state S i.val).presentation.Q) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (((indexedDecoderData S depth).rxMap i).map2 s) = 0 := by
  funext p
  apply (Data S depth i h).induced.map2_auxiliary_zero
  rw [← (Data S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (Data S depth i h).sectors_pairwise_disjoint.2.2) _ hz
  rw [(Data S depth i h).qSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, p.property⟩

/-- The literal map2 lift does not change the chosen correction from the zero run.
This states equality of actual selectors, not additivity of a decoder. -/
theorem embedded_correction_eq_zero_input
    (s : (indexedFamily S depth).Cochain2 i.castSucc) :
    rxCorrectionTotal (Data S depth i h) (((indexedDecoderData S depth).rxMap i).map2 s) =
      rxCorrectionTotal (Data S depth i h) 0 := by
  have hx := cx_total_eq_of_x_eq S depth i h
    (((indexedDecoderData S depth).rxMap i).map2 s) 0 (fun x => by
      rw [map2_restrict_x_zero, map_zero])
  have hq := cq_total_eq_of_cleaned_q_eq S depth i h
    (((indexedDecoderData S depth).rxMap i).map2 s) 0 (fun q => by
      simp only [rxSigmaAfterCx, map_add, hx, map2_restrict_q_zero, map_zero])
  rw [rxCorrectionTotal, rxCorrectionTotal, hx, hq]

/-- Validity of the lifted lower syndrome is derived from its real error preimage. -/
def embeddedSyndrome (h : i.val % 2 = 0)
    (tau : (indexedFamily S depth).Syndrome i.castSucc) :
    (indexedFamily S depth).Syndrome i.succ :=
  ⟨((indexedDecoderData S depth).rxMap i).map2 tau.val, by
    obtain ⟨a,ha⟩ := tau.property
    refine ⟨((indexedDecoderData S depth).rxMap i).map1 a, ?_⟩
    have hc := LinearMap.congr_fun (((indexedDecoderData S depth).rxMap i).commutes_coboundary1) a
    change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).rxMap i).map1 a) =
      ((indexedDecoderData S depth).rxMap i).map2
        ((indexedFamily S depth).coboundary1 i.castSucc a) at hc
    rw [ha] at hc
    exact hc⟩

/-- Canonical actual RX readout recovers every genuine embedded coarse syndrome. -/
theorem embedded_coarse (tau : (indexedFamily S depth).Syndrome i.castSucc) :
    (rxStepOutput S depth i h (embeddedSyndrome S depth i h tau)).coarse.val = tau.val := by
  let sigma0 : (indexedFamily S depth).Syndrome i.succ := ⟨0, ⟨0, map_zero _⟩⟩
  have hc : (rxStepOutput S depth i h (embeddedSyndrome S depth i h tau)).correction =
      (rxStepOutput S depth i h sigma0).correction := by
    rw [rxStepOutput_correction, rxStepOutput_correction]
    exact embedded_correction_eq_zero_input S depth i h tau.val
  have hz : (rxStepOutput S depth i h sigma0).coarse.val = 0 := by
    apply (HammingWeight_eq_zero_iff _).mp
    have hw := rxStepOutput_weight S depth i h sigma0
    have hs0 : sigma0.val = 0 := rfl
    rw [hs0, HammingWeight_zero] at hw
    omega
  have hr0 := rxStepOutput_relation S depth i h sigma0
  change (0 : (indexedFamily S depth).Cochain2 i.succ) = _ at hr0
  rw [hz, map_zero, add_zero] at hr0
  have hr := rxStepOutput_relation S depth i h (embeddedSyndrome S depth i h tau)
  rw [hc, ← hr0, zero_add] at hr
  have hsel : (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
    rw [selectedMap_eq]
    rfl
  rw [hsel] at hr
  change ((indexedDecoderData S depth).rxMap i).map2 tau.val = _ at hr
  funext z
  have he := congrFun hr ((Data S depth i h).induced.zPairEquiv (z,0)).val
  rw [(Data S depth i h).induced.map2_diagonal, (Data S depth i h).induced.map2_diagonal] at he
  exact he.symm

end QEC.Coding.BDL26RXErrorPullback

import QEC.Coding.FiniteAlternatingConstruction.OwnerIncidenceMasks.UniformRXTail.Input

/-! # Actual local kernel coordinates used by RX tail normalization -/
namespace QEC.Coding.BDL26UniformRXTail

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators

/-- Constant translation is real freedom of the local CQ equation. -/
theorem local_q_translate_one
    (P : TannerSquarePresentation) (S : OddScale) (q : P.Q)
    (g : Word BDL26Field (QDoubleCylinderVertex P q S)) :
    wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) (fun v => g v + 1) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 P q S) g :=
  qLocalCoboundary_add_constant P q S g 1

open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

abbrev tailIndex (j : Nat) : StepIndex (2 * j + 4) := ⟨2 * j + 2, by omega⟩

theorem tailIndex_even (j : Nat) : (tailIndex j).val % 2 = 0 := by simp [tailIndex]

noncomputable abbrev tailData (S : OddScale) (j : Nat) :=
  rxData S (2 * j + 4) (tailIndex j) (tailIndex_even j)

noncomputable def errorAfterX (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).Correction (tailIndex j).succ :=
  fun p => lowerError S j p + cxCorrectionTotal (tailData S j) (lowerSyndrome S j).val p

theorem errorAfterX_boundary (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ (errorAfterX S j) =
      rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val := by
  exact ((indexedFamily S (2*j+4)).coboundary1 (tailIndex j).succ).map_add
    (lowerError S j) (cxCorrectionTotal (tailData S j) (lowerSyndrome S j).val)

theorem errorAfterX_local_cocycle (S : OddScale) (j : Nat)
    (x : (state S (2 * j + 2)).presentation.X) :
    (tailData S j).contract.rx_local_complexes.cxDelta1 x
      (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (errorAfterX S j)) = 0 := by
  have hr : restrictWordLinear
      ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).syndromeRegion x)
      ((indexedFamily S (2*j+4)).coboundary1 (tailIndex j).succ (errorAfterX S j)) =
      (tailData S j).contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
          (errorAfterX S j)) :=
    (tailData S j).contract.support_decomposition.cxDelta1_restriction_global x (errorAfterX S j)
  rw [← hr, errorAfterX_boundary]
  have hclean := (cx_cleaning_explicit (tailData S j) (lowerSyndrome S j)).2
  have htotal := cxCorrectionTotal_eq_explicit (tailData S j) (lowerSyndrome S j).val
    ((tailData S j).contract.cx_local_ranges_of_syndrome (lowerSyndrome S j))
  funext p
  change rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val p.1 = 0
  rw [rxSigmaAfterCx, htotal]
  apply hclean
  apply xSector_mem_of_region
  exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, p.2⟩

/-- Actual F06 constructs the potential before any selection is made. -/
theorem actualPotential_exists (S : OddScale) (j : Nat)
    (x : (state S (2*j+2)).presentation.X) :
    ∃ a : Word BDL26Field (DoubleCylinderVertex (state S (2*j+2)).presentation x S),
      (tailData S j).contract.rx_local_complexes.cxDelta0 x a =
      restrictWordLinear ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (errorAfterX S j) := by
  have hm := errorAfterX_local_cocycle S j x
  change _ ∈ LinearMap.ker ((tailData S j).contract.rx_local_complexes.cxDelta1 x) at hm
  rw [(tailData S j).contract.rx_local_cohomology.cx_h1_ker_eq_range x] at hm
  exact hm

noncomputable def actualPotential (S : OddScale) (j : Nat)
    (x : (state S (2*j+2)).presentation.X) :
    Word BDL26Field (DoubleCylinderVertex (state S (2*j+2)).presentation x S) :=
  Classical.choose (actualPotential_exists S j x)

theorem actualPotential_boundary (S : OddScale) (j : Nat)
    (x : (state S (2*j+2)).presentation.X) :
    (tailData S j).contract.rx_local_complexes.cxDelta0 x (actualPotential S j x) =
      restrictWordLinear ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (errorAfterX S j) := Classical.choose_spec (actualPotential_exists S j x)

noncomputable def actualLift (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).Cochain0 (tailIndex j).succ :=
  ∑ x, (tailData S j).contract.support_decomposition.cxLift0 x (actualPotential S j x)

noncomputable def cleanedError (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).Correction (tailIndex j).succ :=
  errorAfterX S j + (indexedFamily S (2 * j + 4)).coboundary0 (tailIndex j).succ (actualLift S j)

theorem cleanedError_x_zero (S : OddScale) (j : Nat)
    (x : (state S (2 * j + 2)).presentation.X) :
    restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
      (cleanedError S j) = 0 := by
  have hl : restrictWordLinear
      ((rxLx S (2*j+4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
      ((indexedFamily S (2*j+4)).coboundary0 (tailIndex j).succ (actualLift S j)) =
      (tailData S j).contract.rx_local_complexes.cxDelta0 x (actualPotential S j x) :=
    (tailData S j).contract.support_decomposition.cxDelta0_sum_decomposition (actualPotential S j) x
  rw [cleanedError, map_add, hl, actualPotential_boundary]
  ext p
  exact ZModModule.add_self _

theorem cleanedError_boundary (S : OddScale) (j : Nat) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ (cleanedError S j) =
      rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val := by
  rw [cleanedError, map_add, errorAfterX_boundary]
  have hz := LinearMap.congr_fun (BDL26CochainFamily.coboundary1_comp_coboundary0
    (indexedFamily S (2 * j + 4)) (tailIndex j).succ) (actualLift S j)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, add_zero]

/-- Range recovery uses zero X ERROR restrictions of the constructed error. -/
theorem actual_cq_range (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    CqLocalRangeAt (tailData S j) (lowerSyndrome S j).val q := by
  have h : restrictWordLinear
      ((rxLq S (2*j+4) (tailIndex j) (tailIndex_even j)).syndromeRegion q)
      ((indexedFamily S (2*j+4)).coboundary1 (tailIndex j).succ (cleanedError S j)) ∈
      LinearMap.range ((tailData S j).contract.rx_local_complexes.cqDelta1 q) :=
    (tailData S j).contract.cq_local_ranges_of_error
      (cleanedError S j) (cleanedError_x_zero S j) q
  rw [cleanedError_boundary] at h
  exact h

noncomputable def actualQWord (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :=
  restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
    (cleanedError S j)

theorem actualQWord_boundary (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    (tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q) =
      restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).syndromeRegion q)
        (rxSigmaAfterCx (tailData S j) (lowerSyndrome S j).val) := by
  rw [← cleanedError_boundary]
  exact ((tailData S j).contract.support_decomposition.cqDelta1_restriction_global
    q (cleanedError S j) (cleanedError_x_zero S j)).symm

/-- The actual CQ choice satisfies its full outgoing budget, with no supplied witness. -/
theorem actual_cq_budget (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    HammingWeight ((tailData S j).contract.support_decomposition.cqFlow q
      (restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (cqComponentTotal (tailData S j) (lowerSyndrome S j).val q))) ≤
      HammingWeight ((tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q)) := by
  rw [actualQWord_boundary]
  exact cqComponentTotal_local_flow_weight _ _ _ (actual_cq_range S j q)

theorem cleanedError_q_supported (S : OddScale) (j : Nat) :
    SupportedOn (tailData S j).qCorrectionSector (cleanedError S j) := by
  intro p hp
  have hc := (tailData S j).correction_sectors_cover
  have hm : p ∈ correctionRegionUnion (rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)) ∪
      (tailData S j).qCorrectionSector := by rw [hc]; exact Finset.mem_univ p
  rcases Finset.mem_union.mp hm with hx | hq
  · obtain ⟨x, _, hpx⟩ := Finset.mem_biUnion.mp hx
    exact congrFun (cleanedError_x_zero S j x) ⟨p, hpx⟩
  · exact (hp hq).elim

theorem cleanedError_q_decomposition (S : OddScale) (j : Nat) :
    cleanedError S j = ∑ q, extendWordLinear
      ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (actualQWord S j q) := by
  unfold actualQWord
  rw [extend_restrict_sum_eq_mask _ (tailData S j).cq_correction_regions_pairwise_disjoint]
  funext p
  by_cases hp : p ∈ correctionRegionUnion (rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j))
  · change cleanedError S j p = if p ∈ correctionRegionUnion _ then cleanedError S j p else 0
    rw [if_pos hp]
  · change cleanedError S j p = if p ∈ correctionRegionUnion _ then cleanedError S j p else 0
    rw [if_neg hp]
    apply cleanedError_q_supported S j p
    simpa [(tailData S j).qCorrectionSector_eq_regions] using hp

theorem actual_cx_budget (S : OddScale) (j : Nat)
    (x : (state S (2 * j + 2)).presentation.X) :
    HammingWeight ((tailData S j).contract.support_decomposition.cxFlow x
      (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
        (cxComponentTotal (tailData S j) (lowerSyndrome S j).val x))) ≤
      HammingWeight ((tailData S j).contract.rx_local_complexes.cxDelta1 x
        (restrictWordLinear ((rxLx S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion x)
          (lowerError S j))) := by
  rw [← (tailData S j).contract.support_decomposition.cxDelta1_restriction_global]
  exact cxComponentTotal_local_flow_weight _ _ _
    ((tailData S j).contract.cx_local_ranges_of_syndrome (lowerSyndrome S j) x)


noncomputable def actualQCorrection (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :=
  restrictWordLinear ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
    (cqComponentTotal (tailData S j) (lowerSyndrome S j).val q)

/-- Explicit constants are values of the ACTUAL correction/error difference at root0. -/
noncomputable def actualConstants (S : OddScale) (j : Nat) :
    Word BDL26Field (state S (2 * j + 2)).presentation.Q := fun q =>
  let root := rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q
    (0, Sum.inl (Sum.inl ()))
  actualQCorrection S j q root + actualQWord S j q root

theorem actual_q_difference_cocycle (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    (tailData S j).contract.rx_local_complexes.cqDelta1 q
      (actualQCorrection S j q + actualQWord S j q) = 0 := by
  rw [map_add, actualQWord_boundary]
  have hg := cqComponentTotal_local_delta (tailData S j) (lowerSyndrome S j).val q
    (actual_cq_range S j q)
  rw [show (tailData S j).contract.rx_local_complexes.cqDelta1 q
    (actualQCorrection S j q) = _ from hg]
  exact ZModModule.add_self _

/-- Includes both copies of every actual Q-cylinder vertex. -/
theorem actual_q_difference_value (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q)
    (v : QDoubleCylinderVertex (state S (2 * j + 2)).presentation q S) :
    let p := rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q v
    actualQCorrection S j q p + actualQWord S j q p = actualConstants S j q :=
  rxQ_kernel_constant S (2 * j + 4) (tailIndex j) (tailIndex_even j) q
    (actualQCorrection S j q + actualQWord S j q) (actual_q_difference_cocycle S j q) v

private theorem restrict_extend_identity {I : Type} [Fintype I] [DecidableEq I]
    (region : Finset I) (w : Word BDL26Field (LocalRegionIndex region)) :
    restrictWordLinear region (extendWordLinear region w) = w := by
  ext p
  change extendLocalSignal region w p.1 = w p
  simp [extendLocalSignal, p.property]

theorem actual_cq_correction_decomposition (S : OddScale) (j : Nat) :
    cqCorrectionTotal (tailData S j) (lowerSyndrome S j).val =
      ∑ q, extendWordLinear
        ((rxLq S (2 * j + 4) (tailIndex j) (tailIndex_even j)).correctionRegion q)
        (actualQCorrection S j q) := by
  change (∑ q, cqComponentTotal (tailData S j) (lowerSyndrome S j).val q) = _
  apply Finset.sum_congr rfl
  intro q _
  unfold actualQCorrection
  rw [cqComponentTotal_eq_explicit _ _ _ (actual_cq_range S j q), restrict_extend_identity]

/-- A literal error identity, stronger than existence of an unspecified coarse preimage. -/
theorem actual_cleaned_error_map1 (S : OddScale) (j : Nat) :
    cleanedError S j + cqCorrectionTotal (tailData S j) (lowerSyndrome S j).val =
      ((indexedDecoderData S (2 * j + 4)).rxMap (tailIndex j)).map1 (actualConstants S j) := by
  rw [cleanedError_q_decomposition, actual_cq_correction_decomposition,
    rxMap1_constant_Q S (2 * j + 4) (tailIndex j) (tailIndex_even j),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← map_add]
  congr 1
  funext p
  obtain ⟨v, rfl⟩ := (rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q).surjective p
  exact (add_comm _ _).trans (actual_q_difference_value S j q v)

/-- The complete residual, including all auxiliary sectors, is the actual selected map2. -/
theorem actual_residual_map2 (S : OddScale) (j : Nat) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val =
      ((indexedDecoderData S (2 * j + 4)).rxMap (tailIndex j)).map2
        ((indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j)) := by
  have hc := LinearMap.congr_fun
    ((indexedDecoderData S (2 * j + 4)).rxMap (tailIndex j)).commutes_coboundary1
    (actualConstants S j)
  simp only [LinearMap.comp_apply] at hc
  change (indexedFamily S (2*j+4)).coboundary1 (tailIndex j).succ
    (((indexedDecoderData S (2*j+4)).rxMap (tailIndex j)).map1 (actualConstants S j)) =
    ((indexedDecoderData S (2*j+4)).rxMap (tailIndex j)).map2
      ((indexedFamily S (2*j+4)).coboundary1 (tailIndex j).castSucc (actualConstants S j)) at hc
  rw [← actual_cleaned_error_map1, map_add, cleanedError_boundary] at hc
  exact hc

/-- No hypotheses beyond S,j: all selected local equations have been discharged. -/
theorem actual_coarse_equation (S : OddScale) (j : Nat) :
    (rxStepOutput S (2 * j + 4) (tailIndex j) (tailIndex_even j) (lowerSyndrome S j)).coarse.val =
      (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j) := by
  rw [rxStepOutput_coarse, rxCoarseWord]
  exact coarseProjection_eq_of_map2 (tailData S j) _ _ (actual_residual_map2 S j).symm

theorem actual_coarse_weight (S : OddScale) (j : Nat) :
    2 * HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
      (tailIndex j).castSucc (actualConstants S j)) ≤ HammingWeight (lowerSyndrome S j).val := by
  rw [← actual_coarse_equation]
  exact rxStepOutput_weight S (2 * j + 4) (tailIndex j) (tailIndex_even j) (lowerSyndrome S j)


/-- Measured bound, with the explicit actual constant word retained. -/
theorem actual_coarse_weight_le_four (S : OddScale) (j : Nat) :
    2 * HammingWeight ((indexedFamily S (2 * j + 4)).coboundary1
      (tailIndex j).castSucc (actualConstants S j)) ≤ 4 :=
  (actual_coarse_weight S j).trans (lower_syndrome_weight_le_four S j)


/-- The fixed radial input has no Z endpoint syndrome. -/
theorem lower_syndrome_z_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (lowerSyndrome S j).val ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by
  exact rxTransport_boundary_z_zero S (2*j+4) (tailIndex j) (tailIndex_even j)
    (lowerErrorRaw S (2*j+2)) (lower_input_raw_z_zero S (2*j+2)) z b

/-- CX cleaning does not change either Z endpoint. -/
theorem actual_cx_boundary_z_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ
      (cxCorrectionTotal (tailData S j) (lowerSyndrome S j).val)
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by
  change (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ
    (∑ x, cxComponentTotal (tailData S j) (lowerSyndrome S j).val x) _ = 0
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  rw [cxComponentTotal_eq_explicit _ _ _
    ((tailData S j).contract.cx_local_ranges_of_syndrome (lowerSyndrome S j) x)]
  exact rxX_boundary_z_zero S (2 * j + 4) (tailIndex j) (tailIndex_even j) x _ z b

theorem cleanedError_boundary_z_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ (cleanedError S j)
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by
  rw [cleanedError_boundary]
  change (lowerSyndrome S j).val _ +
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ
      (cxCorrectionTotal (tailData S j) (lowerSyndrome S j).val) _ = 0
  rw [lower_syndrome_z_zero, actual_cx_boundary_z_zero, zero_add]

/-- Aggregate outgoing cancellation, retaining every Q owner and both copies. -/
theorem actual_q_outgoing_sum_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (∑ q, (tailData S j).contract.support_decomposition.cqFlow q (actualQWord S j q))
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by
  have hz := cleanedError_boundary_z_zero S j z b
  rw [cleanedError_q_decomposition, map_sum] at hz
  simp only [Finset.sum_apply] at hz ⊢
  convert hz using 1
  apply Finset.sum_congr rfl
  intro q _
  exact (rxQ_boundary_z_flow S (2 * j + 4) (tailIndex j) (tailIndex_even j)
    q (actualQWord S j q) z b).symm


theorem actual_residual_endpoint (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val
      ((tailData S j).induced.zPairEquiv (z,b)).val =
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).castSucc (actualConstants S j) z := by
  rw [actual_residual_map2]
  exact (tailData S j).induced.map2_diagonal _ z b

theorem actual_residual_auxiliary (S : OddScale) (j : Nat)
    (p : FamilyZ S (2 * j + 4) (tailIndex j).succ)
    (hp : p ∉ (tailData S j).induced.zSector) :
    rxSigmaAfterCq (tailData S j) (lowerSyndrome S j).val p = 0 := by
  rw [actual_residual_map2]
  exact (tailData S j).induced.map2_auxiliary_zero _ p hp

/-- The CQ budget is the budget of the explicit h-plus-constant correction. -/
theorem actual_q_correction_constant (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    actualQCorrection S j q = actualQWord S j q + (fun _ => actualConstants S j q) := by
  funext p
  obtain ⟨v,rfl⟩ := (rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q).surjective p
  have hv := actual_q_difference_value S j q v
  have ht := congrArg (fun t => t + actualQWord S j q
    (rxQVertexEquiv S (2 * j + 4) (tailIndex j) (tailIndex_even j) q v)) hv
  rw [add_assoc, ZModModule.add_self, add_zero] at ht
  exact ht.trans (add_comm _ _)

theorem actual_cq_constant_budget (S : OddScale) (j : Nat)
    (q : (state S (2 * j + 2)).presentation.Q) :
    HammingWeight ((tailData S j).contract.support_decomposition.cqFlow q
      (actualQWord S j q + (fun _ => actualConstants S j q))) ≤
    HammingWeight ((tailData S j).contract.rx_local_complexes.cqDelta1 q (actualQWord S j q)) := by
  rw [← actual_q_correction_constant]
  exact actual_cq_budget S j q

end QEC.Coding.BDL26UniformRXTail

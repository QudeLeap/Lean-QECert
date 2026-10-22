import QEC.Coding.FiniteAlternatingConstruction.XLocalRadialParity

/-!
# Exact X-local syndrome-cleaning certificate

The correction combines a zero-output radial gauge with the independently
proved four-region cleanup. The gauge is derived from an actual coboundary
preimage, and the layer choice is made from the original region parities.
-/

namespace QEC.Coding.BDL26RXLocalReplacement

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators

private theorem xLocalRegionParity_add
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (s t : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) (region : Two ⊕ Two) :
    xLocalRegionParity P x S (s + t) face region =
      xLocalRegionParity P x S s face region + xLocalRegionParity P x S t face region := by
  cases region with
  | inl copy =>
      change totalParity (xLocalLayerWord P x S s face copy +
        xLocalLayerWord P x S t face copy) = _
      exact map_add _ _ _
  | inr side =>
      change totalParity (xLocalStripWord P x S s face side +
        xLocalStripWord P x S t face side) = _
      exact map_add _ _ _

/-- The radial gauge changes exactly the selected layer's piece parity. -/
theorem xLocal_gauge_layer_parity
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) :
    xLocalRegionParity P x S
        (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
          (radialGauge P A x S selected alpha)) face (Sum.inl copy) =
      if copy = selected then alpha (faceNeighbor P x face 0) +
        alpha (faceNeighbor P x face 1) else 0 := by
  classical
  change (∑ ij : GridVertex S.half,
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S selected alpha) (Sum.inl (copy, face, ij))) = _
  rw [Fintype.sum_prod_type]
  simp_rw [radialGauge_layer_coboundary]
  let origin : Fin S.half := ⟨0, S.half_pos⟩
  have ho : ∀ i : Fin S.half, i.val = 0 ↔ i = origin := by
    intro i
    simp [Fin.ext_iff, origin]
  by_cases hc : copy = selected
  · simp only [hc, if_true, true_and, ho]
    rw [Fintype.sum_eq_single origin]
    · simp
    · intro i hi
      simp [hi]
  · simp [hc]

/-- The radial gauge changes neither boundary-strip parity. -/
theorem xLocal_gauge_strip_parity
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (side : Two) :
    xLocalRegionParity P x S
        (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
          (radialGauge P A x S selected alpha)) face (Sum.inr side) = 0 := by
  change (∑ i : StripVertex S.half,
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S selected alpha)
      (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) i))) = 0
  simp only [radialGauge_strip_coboundary, Finset.sum_const_zero]

private theorem gaugeFourBits_even
    (a b l r t : Field) (selected : Two)
    (h : a + b + l + r + t = 0) :
    (a + if (0 : Two) = selected then t else 0) +
      (b + if (1 : Two) = selected then t else 0) + (l + 0) + (r + 0) = 0 := by
  fin_cases selected <;> simp [Fin.ext_iff] <;> linear_combination h

/-- The interface parities of the given preimage make every updated piece even. -/
theorem xLocal_gauge_makes_pieces_even
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : Word Field (DoubleCylinderEdge P x S))
    (selected : Two) (face : XStarFace P x) :
    let D := wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
    let tau := D e + D (radialGauge P A x S selected (interfaceParity P A x S e))
    xLocalRegionParity P x S tau face (Sum.inl 0) +
      xLocalRegionParity P x S tau face (Sum.inl 1) +
      xLocalRegionParity P x S tau face (Sum.inr 0) +
      xLocalRegionParity P x S tau face (Sum.inr 1) = 0 := by
  dsimp only
  have h := piece_parity_coboundary P A x S e face
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two] at h
  let alpha := interfaceParity P A x S e
  let p := xLocalRegionParity P x S
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face
  have hp : p (Sum.inl 0) + p (Sum.inl 1) + p (Sum.inr 0) + p (Sum.inr 1) =
      alpha (faceNeighbor P x face 0) + alpha (faceNeighbor P x face 1) := by
    simpa only [p, alpha, add_assoc] using h
  have hz : p (Sum.inl 0) + p (Sum.inl 1) + p (Sum.inr 0) + p (Sum.inr 1) +
      (alpha (faceNeighbor P x face 0) + alpha (faceNeighbor P x face 1)) = 0 := by
    rw [hp]
    exact ZModModule.add_self _
  simp only [xLocalRegionParity_add, xLocal_gauge_layer_parity, xLocal_gauge_strip_parity]
  exact gaugeFourBits_even (p (Sum.inl 0)) (p (Sum.inl 1))
    (p (Sum.inr 0)) (p (Sum.inr 1))
    (alpha (faceNeighbor P x face 0) + alpha (faceNeighbor P x face 1)) selected hz

private noncomputable def xLocalCrossingBudget
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (s : Word Field (DoubleCylinderFace P x S)) : Nat :=
  ∑ face : XStarFace P x, pieceCrossingCost
    (xLocalRegionParity P x S s face (Sum.inl 0))
    (xLocalRegionParity P x S s face (Sum.inl 1))
    (xLocalRegionParity P x S s face (Sum.inr 0))
    (xLocalRegionParity P x S s face (Sum.inr 1))

/-- The chosen layer pays the crossing cost using the original syndrome budget. -/
private theorem xLocal_choose_gauge_budget
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (s : Word Field (DoubleCylinderFace P x S))
    (alpha : Neighbor P x → Field) :
    ∃ selected : Two,
      xLocalCrossingBudget P x S
        (s + wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
          (radialGauge P A x S selected alpha)) ≤ HammingWeight s := by
  classical
  let p := fun face region => xLocalRegionParity P x S s face region
  have horig := xLocal_region_parity_budget P A4 R x S s
  by_cases hLayer : (∑ face, bitWeight (p face (Sum.inl 1))) ≤
      ∑ face, bitWeight (p face (Sum.inl 0))
  · refine ⟨0, ?_⟩
    let tau := s + wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S 0 alpha)
    have h1 : ∀ face, xLocalRegionParity P x S tau face (Sum.inl 1) = p face (Sum.inl 1) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_layer_parity]
    have hl : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 0) = p face (Sum.inr 0) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hr : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 1) = p face (Sum.inr 1) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hcost := sum_pieceCrossingCost_le_of_second_layer
      (fun face => p face (Sum.inl 0)) (fun face => p face (Sum.inl 1))
      (fun face => xLocalRegionParity P x S tau face (Sum.inl 0))
      (fun face => p face (Sum.inr 0)) (fun face => p face (Sum.inr 1)) hLayer
    change xLocalCrossingBudget P x S tau ≤ HammingWeight s
    unfold xLocalCrossingBudget
    simp_rw [h1, hl, hr]
    exact hcost.trans horig
  · refine ⟨1, ?_⟩
    have hLayer' : (∑ face, bitWeight (p face (Sum.inl 0))) ≤
        ∑ face, bitWeight (p face (Sum.inl 1)) := by omega
    let tau := s + wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S 1 alpha)
    have h0 : ∀ face, xLocalRegionParity P x S tau face (Sum.inl 0) = p face (Sum.inl 0) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_layer_parity]
    have hl : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 0) = p face (Sum.inr 0) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hr : ∀ face, xLocalRegionParity P x S tau face (Sum.inr 1) = p face (Sum.inr 1) := by
      intro face
      simp [tau, p, xLocalRegionParity_add, xLocal_gauge_strip_parity]
    have hcost := sum_pieceCrossingCost_le_of_first_layer
      (fun face => p face (Sum.inl 0)) (fun face => p face (Sum.inl 1))
      (fun face => xLocalRegionParity P x S tau face (Sum.inl 1))
      (fun face => p face (Sum.inr 0)) (fun face => p face (Sum.inr 1)) hLayer'
    change xLocalCrossingBudget P x S tau ≤ HammingWeight s
    unfold xLocalCrossingBudget
    simp_rw [h0, hl, hr]
    exact hcost.trans horig

private theorem xLocalCertificate_connectingWeight_add_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f g : Word Field (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S (f + g) ≤
      connectingWeight P A x S f + connectingWeight P A x S g := by
  unfold connectingWeight
  simp only [map_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => HammingWeight_add_le _ _)

/-- F12 X-local syndrome cleaning: the exact local preimage and its actual
summed X-to-Q connecting-map budget are both theorem-derived. -/
theorem rxCx_exists_local_weight_le
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S))) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      connectingWeight P A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible x S f ≤
        HammingWeight syndrome := by
  classical
  obtain ⟨e, rfl⟩ := hs
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let D := wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
  let alpha := interfaceParity P A x S e
  obtain ⟨selected, hbudget⟩ := xLocal_choose_gauge_budget P A A4 R x S (D e) alpha
  let gauge := radialGauge P A x S selected alpha
  let tau := D e + D gauge
  have heven := fun face => xLocal_gauge_makes_pieces_even P A x S e selected face
  obtain ⟨cleanup, hcleanup, hweight⟩ :=
    xLocal_even_pieces_cleanup P A A4 R x S tau heven
  refine ⟨gauge + cleanup, ?_, ?_⟩
  · change D (gauge + cleanup) = D e
    rw [map_add, hcleanup]
    change D gauge + (D e + D gauge) = D e
    rw [add_left_comm, ZModModule.add_self, add_zero]
  · have hsum := xLocalCertificate_connectingWeight_add_le P A x S gauge cleanup
    have hzero : connectingWeight P A x S gauge = 0 :=
      radialGauge_connectingWeight_zero P A x S selected alpha
    change connectingWeight P A x S cleanup ≤ xLocalCrossingBudget P x S tau at hweight
    change xLocalCrossingBudget P x S tau ≤ HammingWeight (D e) at hbudget
    change connectingWeight P A x S (gauge + cleanup) ≤ HammingWeight (D e)
    omega

/-- F12 stated over every old Q block, with nonincident blocks contributing zero. -/
theorem rxCx_exists_local_weight_le_all_q
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (hs : syndrome ∈ LinearMap.range (wordLinearMapTranspose (doubleCylinderBoundary2 P x S))) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      (∑ q : P.Q, if hq : P.xq x q = true then
        HammingWeight (rxXQDegreeOne P
          A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible q x hq S f) else 0) ≤
        HammingWeight syndrome := by
  classical
  obtain ⟨f, hf, hw⟩ := rxCx_exists_local_weight_le P A4 R x S syndrome hs
  refine ⟨f, hf, ?_⟩
  let A := A4.toTannerSquareAdmissibleV2.toTannerSquareAdmissible
  let term := fun q : P.Q => if hq : P.xq x q = true then
    HammingWeight (rxXQDegreeOne P A q x hq S f) else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun q : P.Q => P.xq x q = true) term
  have hpos : (∑ q : {q : P.Q // P.xq x q = true}, term q.val) =
      connectingWeight P A x S f := by
    apply Finset.sum_congr rfl
    intro q _
    exact dif_pos q.property
  have hneg : (∑ q : {q : P.Q // ¬ P.xq x q = true}, term q.val) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    exact dif_neg q.property
  have hsum : (∑ q : P.Q, term q) = connectingWeight P A x S f := by
    calc
      _ = (∑ q : {q : P.Q // P.xq x q = true}, term q.val) +
          (∑ q : {q : P.Q // ¬ P.xq x q = true}, term q.val) := hsplit.symm
      _ = _ := by rw [hpos, hneg, add_zero]
  change (∑ q : P.Q, term q) ≤ HammingWeight syndrome
  rw [hsum]
  exact hw

end QEC.Coding.BDL26RXLocalReplacement

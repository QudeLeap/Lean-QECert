import QEC.Coding.FiniteAlternatingConstruction.XLocalWeight

/-!
# Radial parity gauge for RX pieces

The piece parity of an actual local coboundary is determined by the radial
interfaces. These identities provide the zero-connecting-cost first step of
the X-local syndrome cleaning construction.
-/

namespace QEC.Coding.BDL26XLocalRadialParity

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26XLocalConnectingWeight BDL26XLocalWeightParity
open scoped BigOperators Classical

abbrev Field := ZMod 2
abbrev Two := Fin 2

/-- Binary cancellation along every adjacent pair of a finite interval. -/
theorem sum_adjacent (n : ℕ) (f : Fin (n + 1) → Field) :
    (∑ i : Fin n, (f i.castSucc + f i.succ)) = f 0 + f (Fin.last n) := by
  induction n with
  | zero =>
      change 0 = f 0 + f 0
      exact (ZModModule.add_self (f 0)).symm
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      have h := ih (fun i => f i.castSucc)
      have hcast :
          (∑ i : Fin n, (f i.castSucc.castSucc + f i.castSucc.succ)) =
          f 0 + f (Fin.last n).castSucc := by
        simpa only [Fin.castSucc_succ, Fin.castSucc_zero] using h
      rw [hcast]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
      rw [hlast]
      have hcancel := ZModModule.add_self (f (Fin.last n).castSucc)
      linear_combination hcancel

/-- The actual copied-square coboundary is its four edge values. -/
theorem layer_coboundary_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) (copy : Two) (i j : Fin S.half) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e
        (Sum.inl (copy, face, i, j)) =
      e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i j.castSucc)) +
      e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.succ j)) +
      e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i j.succ)) +
      e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.castSucc j)) := by
  classical
  unfold doubleCylinderBoundary2
  rw [wordLinearMapTranspose_toLin'_apply]
  simp [doubleCylinderFaceEdgeMatrix, subdivisionFaceEdgeMatrix,
    Fintype.sum_sum_type, Fintype.sum_prod_type, mul_add,
    Finset.sum_add_distrib]
  rfl

/-- The actual rectangle coboundary has two copied and two vertical sides. -/
theorem strip_coboundary_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (edge : SubdivisionBoundaryEdge P x S) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e (Sum.inr edge) =
      e (Sum.inl (0, edge.val)) + e (Sum.inl (1, edge.val)) +
      e (Sum.inr (subdivisionBoundaryEdgeStart P x S edge)) +
      e (Sum.inr (subdivisionBoundaryEdgeEnd P x S edge)) := by
  classical
  letI : DecidableEq (SubdivisionBoundaryVertex P x S) := Subtype.instDecidableEq
  unfold doubleCylinderBoundary2
  rw [wordLinearMapTranspose_toLin'_apply]
  simp [doubleCylinderFaceEdgeMatrix, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fin.sum_univ_two, mul_add, Finset.sum_add_distrib,
    add_assoc] <;>
  exact congrArg₂ (fun a b : Field => a + b)
    (Finset.sum_ite_eq_of_mem' Finset.univ _ _ (Finset.mem_univ _))
    (Finset.sum_ite_eq_of_mem' Finset.univ _ _ (Finset.mem_univ _))

/-- Summing a copied grid cancels all internal edges. -/
theorem layer_parity_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) (copy : Two) :
    totalParity (xLocalLayerWord P x S
      (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face copy) =
      (∑ i : Fin S.half,
        e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i 0))) +
      (∑ i : Fin S.half,
        e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i (Fin.last S.half)))) +
      (∑ j : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face 0 j))) +
      (∑ j : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face (Fin.last S.half) j))) := by
  classical
  simp only [totalParity_apply, xLocalLayerWord, Fintype.sum_prod_type,
    layer_coboundary_apply]
  have hH (i : Fin S.half) := sum_adjacent S.half
    (fun j => e (Sum.inl (copy, subdivisionHorizontalEdge P x S face i j)))
  have hV (j : Fin S.half) := sum_adjacent S.half
    (fun i => e (Sum.inl (copy, subdivisionVerticalEdge P x S face i j)))
  have hHs := congrArg (fun f : Fin S.half → Field => ∑ i, f i) (funext hH)
  have hVs := congrArg (fun f : Fin S.half → Field => ∑ j, f j) (funext hV)
  simp only [Finset.sum_add_distrib] at hHs hVs ⊢
  have hswap0 :
      (∑ i : Fin S.half, ∑ j : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.castSucc j))) =
      ∑ j : Fin S.half, ∑ i : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.castSucc j)) :=
    Finset.sum_comm
  have hswap1 :
      (∑ i : Fin S.half, ∑ j : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.succ j))) =
      ∑ j : Fin S.half, ∑ i : Fin S.half,
        e (Sum.inl (copy, subdivisionVerticalEdge P x S face i.succ j)) :=
    Finset.sum_comm
  rw [← hswap0, ← hswap1] at hVs
  linear_combination hHs + hVs

/-- All vertices of one boundary arm, including its original endpoints. -/
def boundaryArmVertex (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (i : Fin (S.half + 1)) :
    SubdivisionBoundaryVertex P x S :=
  if hi0 : i.val = 0 then
    subdivisionOriginalBoundaryVertex P x S (xBoundaryEdgeStart P x edge)
  else if him : i.val = S.half then
    subdivisionOriginalBoundaryVertex P x S (xBoundaryEdgeEnd P x edge)
  else
    ⟨Sum.inr (Sum.inl (xStarBoundaryEdgeToStar P x edge,
      ⟨i.val - 1, by have := i.isLt; omega⟩)), edge.property⟩

theorem boundaryArmVertex_start
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (i : Fin S.half) :
    subdivisionBoundaryEdgeStart P x S (subdivisionOriginalBoundaryEdge P x S edge i) =
      boundaryArmVertex P x S edge i.castSucc := by
  apply Subtype.ext
  have hi : i.val ≠ S.half := Nat.ne_of_lt i.isLt
  simp [subdivisionBoundaryEdgeStart_value, subdivisionOriginalBoundaryEdge,
    subdivisionEdgeStart, subdivisionSegmentStart, boundaryArmVertex, hi,
    subdivisionOriginalBoundaryVertex]
  split_ifs <;> rfl

theorem boundaryArmVertex_end
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : XStarBoundaryEdge P x) (i : Fin S.half) :
    subdivisionBoundaryEdgeEnd P x S (subdivisionOriginalBoundaryEdge P x S edge i) =
      boundaryArmVertex P x S edge i.succ := by
  apply Subtype.ext
  simp [subdivisionBoundaryEdgeEnd_value, subdivisionOriginalBoundaryEdge,
    subdivisionEdgeEnd, subdivisionSegmentEnd, boundaryArmVertex,
    subdivisionOriginalBoundaryVertex]
  split_ifs <;> rfl

/-- Strip parity retains only the two copied arms and the original endpoints. -/
theorem strip_parity_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) (side : Two) :
    totalParity (xLocalStripWord P x S
      (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face side) =
      (∑ i : Fin S.half, e (Sum.inl (0,
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i).val))) +
      (∑ i : Fin S.half, e (Sum.inl (1,
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i).val))) +
      e (Sum.inr (subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face side)))) +
      e (Sum.inr (subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face side)))) := by
  classical
  simp only [totalParity_apply, xLocalStripWord, strip_coboundary_apply,
    boundaryArmVertex_start, boundaryArmVertex_end, Finset.sum_add_distrib]
  have h := sum_adjacent S.half (fun i => e (Sum.inr
    (boundaryArmVertex P x S (xStarFaceBoundaryEdge P x face side) i)))
  simp only [Finset.sum_add_distrib] at h
  have h0 : boundaryArmVertex P x S (xStarFaceBoundaryEdge P x face side) 0 =
      subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face side)) := by
    simp [boundaryArmVertex]
  have hm : boundaryArmVertex P x S (xStarFaceBoundaryEdge P x face side)
      (Fin.last S.half) = subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face side)) := by
    simp [boundaryArmVertex, S.half_pos.ne']
  rw [h0, hm] at h
  linear_combination h

def faceNeighbor (P : TannerSquarePresentation) (x : P.X)
    (face : XStarFace P x) (side : Two) : Neighbor P x :=
  ⟨P.faceQ face.val side, by
    have hx : P.faceX face.val = x := by simpa [xStarFaceMember] using face.property
    simpa [hx] using P.data.faceQ_xq face.val side⟩

def boundaryQ (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (q : Neighbor P x) : XStarBoundaryVertex P x :=
  qToXBoundaryVertex P A q.val x q.property (Sum.inl ())

def radialEdge (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (q : Neighbor P x) : XStarEdge P x :=
  rxOriginalXBoundaryRadialEdge P x q.val (boundaryQ P A x q).property

theorem radialEdge_faceNeighbor
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (face : XStarFace P x) (side : Two) :
    radialEdge P A x (faceNeighbor P x face side) = xStarFaceXQEdge P x face side := by
  apply Subtype.ext
  have hx : P.faceX face.val = x := by simpa [xStarFaceMember] using face.property
  simp [radialEdge, rxOriginalXBoundaryRadialEdge, faceNeighbor,
    xStarFaceXQEdge, faceXQEdge, hx]

theorem boundaryQ_faceNeighbor
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (face : XStarFace P x) (side : Two) :
    boundaryQ P A x (faceNeighbor P x face side) =
      xBoundaryEdgeStart P x (xStarFaceBoundaryEdge P x face side) := by
  apply Subtype.ext
  rfl

theorem face_boundary_end_eq
    (P : TannerSquarePresentation) (x : P.X) (face : XStarFace P x) :
    xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0) =
      xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 1) := by
  apply Subtype.ext
  rfl

/-- Parity of the two radial arms and their vertical Q connector. -/
def interfaceParity
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : Word Field (DoubleCylinderEdge P x S))
    (q : Neighbor P x) : Field :=
  (∑ i : Fin S.half, e (Sum.inl (0, Sum.inl (radialEdge P A x q, i)))) +
  (∑ i : Fin S.half, e (Sum.inl (1, Sum.inl (radialEdge P A x q, i)))) +
  e (Sum.inr (subdivisionOriginalBoundaryVertex P x S (boundaryQ P A x q)))

/-- Every genuine coboundary has the source's link-graph piece parity. -/
theorem piece_parity_coboundary
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (e : Word Field (DoubleCylinderEdge P x S))
    (face : XStarFace P x) :
    (∑ region : Two ⊕ Two, xLocalRegionParity P x S
      (wordLinearMapTranspose (doubleCylinderBoundary2 P x S) e) face region) =
      interfaceParity P A x S e (faceNeighbor P x face 0) +
      interfaceParity P A x S e (faceNeighbor P x face 1) := by
  classical
  have hL0 := layer_parity_boundary P x S e face 0
  have hL1 := layer_parity_boundary P x S e face 1
  have hS0 := strip_parity_boundary P x S e face 0
  have hS1 := strip_parity_boundary P x S e face 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, xLocalRegionParity]
  simp only [interfaceParity, radialEdge_faceNeighbor, boundaryQ_faceNeighbor]
  rw [face_boundary_end_eq P x face] at hS0
  simp [subdivisionHorizontalEdge, subdivisionVerticalEdge, S.half_pos.ne',
    subdivisionOriginalBoundaryEdge, xStarFaceBoundaryEdge, xStarBoundaryEdgeToStar]
    at hL0 hL1 hS0 hS1 ⊢
  have htwo : (2 : Field) = 0 := by decide
  linear_combination (norm := (ring_nf; simp only [htwo, mul_zero, add_zero]))
    hL0 + hL1 + hS0 + hS1

theorem radialEdge_injective
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (x : P.X) :
    Function.Injective (radialEdge P A x) := by
  intro q r h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  have hp := Sum.inl.inj he
  exact congrArg (fun e : XQEdge P => e.val.2) hp

/-- The source's first correction uses only the first radial segment in one copy. -/
noncomputable def radialGauge
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field) :
    Word Field (DoubleCylinderEdge P x S) :=
  ∑ q : Neighbor P x,
    Pi.single (Sum.inl (selected, Sum.inl (radialEdge P A x q, rxRadialGridZero S))) (alpha q)

theorem radialGauge_connectingWeight_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field) :
    connectingWeight P A x S (radialGauge P A x S selected alpha) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold radialGauge
  apply (xLocal_connectingWeight_sum_le P A x S _).trans
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro q _
  exact connectingWeight_single_eq_zero_of_other P A x S _ rfl rfl _

theorem radialGauge_horizontal
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) (i : Fin S.half) (j : Fin (S.half + 1)) :
    radialGauge P A x S selected alpha
      (Sum.inl (copy, subdivisionHorizontalEdge P x S face i j)) =
      if copy = selected ∧ i.val = 0 ∧ j.val = 0 then
        alpha (faceNeighbor P x face 0) else 0 := by
  classical
  have hr := radialEdge_injective P A x
  by_cases hj : j.val = 0
  · have hedge : subdivisionHorizontalEdge P x S face i j =
        Sum.inl (radialEdge P A x (faceNeighbor P x face 0), i) := by
      rw [radialEdge_faceNeighbor]
      simp only [subdivisionHorizontalEdge, dif_pos hj]
    have hiz : (i = rxRadialGridZero S) ↔ i.val = 0 := by
      rw [Fin.ext_iff]
      rfl
    simp only [hedge, radialGauge, Finset.sum_apply, Pi.single_apply,
      Sum.inl.injEq, Prod.mk.injEq, hr.eq_iff, hiz, hj]
    by_cases hc : copy = selected <;> by_cases hi : i.val = 0 <;>
      simp only [hc, hi, and_true, and_false, true_and, false_and,
        ite_true, ite_false, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ]
  · by_cases hlast : j.val = S.half
    · simp [radialGauge, subdivisionHorizontalEdge, hj, hlast, Pi.single_apply,
        radialEdge, rxOriginalXBoundaryRadialEdge, xStarFaceQZEdge, faceQZEdge, S.half_pos.ne']
    · simp [radialGauge, subdivisionHorizontalEdge, hj, hlast, Pi.single_apply]

theorem radialGauge_vertical
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) (i : Fin (S.half + 1)) (j : Fin S.half) :
    radialGauge P A x S selected alpha
      (Sum.inl (copy, subdivisionVerticalEdge P x S face i j)) =
      if copy = selected ∧ i.val = 0 ∧ j.val = 0 then
        alpha (faceNeighbor P x face 1) else 0 := by
  classical
  have hr := radialEdge_injective P A x
  by_cases hi : i.val = 0
  · have hedge : subdivisionVerticalEdge P x S face i j =
        Sum.inl (radialEdge P A x (faceNeighbor P x face 1), j) := by
      rw [radialEdge_faceNeighbor]
      simp only [subdivisionVerticalEdge, dif_pos hi]
    have hjz : (j = rxRadialGridZero S) ↔ j.val = 0 := by
      rw [Fin.ext_iff]
      rfl
    simp only [hedge, radialGauge, Finset.sum_apply, Pi.single_apply,
      Sum.inl.injEq, Prod.mk.injEq, hr.eq_iff, hjz, hi]
    by_cases hc : copy = selected <;> by_cases hj : j.val = 0 <;>
      simp only [hc, hj, and_true, and_false, true_and, false_and,
        ite_true, ite_false, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.mem_univ]
  · by_cases hlast : i.val = S.half
    · simp [radialGauge, subdivisionVerticalEdge, hi, hlast, Pi.single_apply,
        radialEdge, rxOriginalXBoundaryRadialEdge, xStarFaceQZEdge, faceQZEdge, S.half_pos.ne']
    · simp [radialGauge, subdivisionVerticalEdge, hi, hlast, Pi.single_apply]

/-- The gauge changes only the origin square in the selected layer. -/
theorem radialGauge_layer_coboundary
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (copy : Two) (i j : Fin S.half) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S selected alpha) (Sum.inl (copy, face, i, j)) =
      if copy = selected ∧ i.val = 0 ∧ j.val = 0 then
        alpha (faceNeighbor P x face 0) + alpha (faceNeighbor P x face 1) else 0 := by
  rw [layer_coboundary_apply]
  simp only [radialGauge_horizontal, radialGauge_vertical, Fin.coe_castSucc, Fin.val_succ]
  by_cases hc : copy = selected <;> by_cases hi : i.val = 0 <;>
    by_cases hj : j.val = 0 <;> simp [hc, hi, hj]

theorem radialGauge_strip_coboundary
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (selected : Two) (alpha : Neighbor P x → Field)
    (face : XStarFace P x) (side : Two) (i : Fin S.half) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (radialGauge P A x S selected alpha)
      (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) i)) = 0 := by
  classical
  rw [strip_coboundary_apply]
  simp [radialGauge, Pi.single_apply, subdivisionOriginalBoundaryEdge,
    radialEdge, rxOriginalXBoundaryRadialEdge, xStarFaceBoundaryEdge,
    xStarBoundaryEdgeToStar, xStarFaceQZEdge, faceQZEdge]

end QEC.Coding.BDL26XLocalRadialParity

import QEC.Coding.FiniteAlternatingConstruction.RXLocalReplacement
import QEC.Coding.FiniteAlternatingConstruction.XLocalGridParity
import QEC.Coding.FiniteAlternatingConstruction.XLocalWeightParity
import QEC.Coding.FiniteAlternatingConstruction.XLocalConnectingWeight

/-!
# Geometric decomposition for X-local syndrome cleaning

The four regions of each old face are two subdivided square layers and two
boundary strips. The maps below retain the concrete Tanner cell tags.
-/

namespace QEC.Coding.BDL26RXLocalReplacement

open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

/-- A boundary Q-Z edge remembers exactly its old face and ordered side. -/
theorem xLocal_boundary_side_injective
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P) (x : P.X) :
    Function.Injective (fun p : XStarFace P x × Two =>
      xStarFaceBoundaryEdge P x p.1 p.2) := by
  rintro ⟨f, s⟩ ⟨g, t⟩ h
  have he : faceQZEdge P f.val s = faceQZEdge P g.val t := by
    exact Sum.inr.inj (congrArg Subtype.val h)
  have hq := congrArg (fun e : QZEdge P => e.val.1) he
  have hz := congrArg (fun e : QZEdge P => e.val.2) he
  have hfx : P.faceX f.val = x := by simpa [xStarFaceMember] using f.property
  have hgx : P.faceX g.val = x := by simpa [xStarFaceMember] using g.property
  have hfg : f = g := Subtype.ext (R.faceXZ_injective (Prod.ext (hfx.trans hgx.symm) hz))
  subst g
  have hst : s = t := P.faceQ_injective f.val hq
  subst t
  rfl

/-- The boundary-owner data exhaust every original Q-Z side of the X-star. -/
theorem xLocal_boundary_side_surjective
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P) (x : P.X) :
    Function.Surjective (fun p : XStarFace P x × Two =>
      xStarFaceBoundaryEdge P x p.1 p.2) := by
  rintro ⟨edge, hedge⟩
  rcases edge with radial | boundary
  · simp [xStarBoundaryEdgeMember] at hedge
  · let member := xStarBoundaryEdgeMember_to_star P x (Sum.inr boundary) hedge
    let owner := A4.xBoundaryFaceOwner x boundary member
    refine ⟨owner.val, ?_⟩
    apply Subtype.ext
    exact congrArg (fun e : XStarEdge P x => e.val) owner.property

/-- Exact face/side coordinates for original boundary edges. -/
noncomputable def xLocalBoundarySideEquiv
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) :
    (XStarFace P x × Two) ≃ XStarBoundaryEdge P x :=
  Equiv.ofBijective (fun p => xStarFaceBoundaryEdge P x p.1 p.2)
    ⟨xLocal_boundary_side_injective P R x, xLocal_boundary_side_surjective P A4 x⟩

/-- Subdivision boundary edges retain exactly the original side and segment. -/
theorem xLocal_boundary_segment_bijective
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Function.Bijective (fun p : XStarBoundaryEdge P x × Fin S.half =>
      subdivisionOriginalBoundaryEdge P x S p.1 p.2) := by
  constructor
  · rintro ⟨e, i⟩ ⟨f, j⟩ h
    have hp : (xStarBoundaryEdgeToStar P x e, i) =
        (xStarBoundaryEdgeToStar P x f, j) :=
      Sum.inl.inj (congrArg Subtype.val h)
    have hij := congrArg Prod.snd hp
    have hef : e = f := Subtype.ext
      (congrArg (fun e : XStarEdge P x => e.val) (congrArg Prod.fst hp))
    exact Prod.ext hef hij
  · rintro ⟨edge, hedge⟩
    rcases edge with original | interior
    · rcases original with ⟨edge, i⟩
      exact ⟨(⟨edge.val, hedge⟩, i), rfl⟩
    · simp [subdivisionBoundaryEdgeMember] at hedge

noncomputable def xLocalBoundarySegmentEquiv
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (XStarBoundaryEdge P x × Fin S.half) ≃ SubdivisionBoundaryEdge P x S :=
  Equiv.ofBijective (fun p => subdivisionOriginalBoundaryEdge P x S p.1 p.2)
    (xLocal_boundary_segment_bijective P x S)

/-- The two square layers and two one-dimensional strips of one old face. -/
abbrev XLocalPieceCell (S : OddScale) :=
  (Two × GridVertex S.half) ⊕ (Two × StripVertex S.half)

/-- Include an explicitly tagged piece cell into the actual local cylinder. -/
def xLocalPieceCellMap (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    XStarFace P x × XLocalPieceCell S → DoubleCylinderFace P x S
  | (face, Sum.inl (copy, i, j)) => Sum.inl (copy, face, i, j)
  | (face, Sum.inr (side, i)) => Sum.inr
      (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) i)

/-- No two face pieces or regions share a syndrome coordinate. -/
theorem xLocalPieceCellMap_injective
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) : Function.Injective (xLocalPieceCellMap P x S) := by
  rintro ⟨f, a | a⟩ ⟨g, b | b⟩ h
  · rcases a with ⟨c, i, j⟩
    rcases b with ⟨d, k, l⟩
    have hc := Sum.inl.inj h
    cases hc
    rfl
  · cases h
  · cases h
  · rcases a with ⟨s, i⟩
    rcases b with ⟨t, j⟩
    change Sum.inr (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x f s) i) =
      Sum.inr (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x g t) j) at h
    have he : subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x f s) i =
        subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x g t) j := Sum.inr.inj h
    have hp : (xStarFaceBoundaryEdge P x f s, i) =
        (xStarFaceBoundaryEdge P x g t, j) :=
      (xLocal_boundary_segment_bijective P x S).1 he
    have hij := congrArg Prod.snd hp
    have hfs : (f, s) = (g, t) :=
      xLocal_boundary_side_injective P R x (congrArg Prod.fst hp)
    cases hfs
    cases hij
    rfl

/-- Every local syndrome coordinate belongs to one of the four face regions. -/
theorem xLocalPieceCellMap_surjective
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (x : P.X) (S : OddScale) : Function.Surjective (xLocalPieceCellMap P x S) := by
  rintro (⟨copy, face, i, j⟩ | edge)
  · exact ⟨(face, Sum.inl (copy, i, j)), rfl⟩
  · obtain ⟨⟨boundary, i⟩, hi⟩ := (xLocal_boundary_segment_bijective P x S).2 edge
    obtain ⟨⟨face, side⟩, hside⟩ := xLocal_boundary_side_surjective P A4 x boundary
    subst boundary
    exact ⟨(face, Sum.inr (side, i)), congrArg Sum.inr hi⟩

/-- Exact four-region reindexing of the full X-local syndrome type. -/
noncomputable def xLocalPieceCellEquiv
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale) :
    (XStarFace P x × XLocalPieceCell S) ≃ DoubleCylinderFace P x S :=
  Equiv.ofBijective (xLocalPieceCellMap P x S)
    ⟨xLocalPieceCellMap_injective P R x S, xLocalPieceCellMap_surjective P A4 x S⟩

@[simp] theorem xLocalPieceCellEquiv_apply
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (p : XStarFace P x × XLocalPieceCell S) :
    xLocalPieceCellEquiv P A4 R x S p = xLocalPieceCellMap P x S p := rfl

/-- Original syndrome restricted to the square region of one face and copy. -/
def xLocalLayerWord (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) (copy : Two) : Word Field (GridVertex S.half) :=
  fun ij => syndrome (Sum.inl (copy, face, ij))

/-- Original syndrome restricted to one boundary strip. -/
def xLocalStripWord (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) (side : Two) : Word Field (StripVertex S.half) :=
  fun i => syndrome (Sum.inr (subdivisionOriginalBoundaryEdge P x S
    (xStarFaceBoundaryEdge P x face side) i))

/-- The four region parities, with layers before strips. -/
def xLocalRegionParity (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (face : XStarFace P x) : Two ⊕ Two → Field
  | Sum.inl copy => totalParity (xLocalLayerWord P x S syndrome face copy)
  | Sum.inr side => totalParity (xLocalStripWord P x S syndrome face side)

/-- An interior dual-grid step crosses a single concrete primal grid edge. -/
def xLocalGridDualEdge (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) : GridEdge S.half → DoubleCylinderEdge P x S
  | Sum.inl (i, j) => Sum.inl (copy, Sum.inr (Sum.inr (face, i, j)))
  | Sum.inr (i, j) => Sum.inl (copy, Sum.inr (Sum.inl (face, i, j)))

/-- A strip dual step crosses the vertical edge at a Q-Z path interior point. -/
def xLocalStripDualEdge (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) (i : StripEdge S.half) :
    DoubleCylinderEdge P x S :=
  Sum.inr ⟨Sum.inr (Sum.inl
    (xStarBoundaryEdgeToStar P x (xStarFaceBoundaryEdge P x face side), i)), by
      change xStarBoundaryEdgeMember P x (xStarFaceBoundaryEdge P x face side).val = true
      exact (xStarFaceBoundaryEdge P x face side).property⟩

private theorem xLocal_weight_eq_sum {I : Type} [Fintype I] (f : Word Field I) :
    HammingWeight f = ∑ i, bitWeight (f i) := by
  classical
  simp [HammingWeight, hammingSupport, Finset.card_filter, bitWeight]

private theorem xLocal_bitWeight_add_le (a b : Field) :
    bitWeight (a + b) ≤ bitWeight a + bitWeight b := by
  have h := bitWeight_le_add (a + b) b
  simpa only [add_assoc, ZModModule.add_self, add_zero] using h

/-- A region's binary parity has weight at most the number of its syndromes. -/
theorem xLocal_parity_weight_le {I : Type} [Fintype I] (f : Word Field I) :
    bitWeight (totalParity f) ≤ HammingWeight f := by
  classical
  rw [xLocal_weight_eq_sum, totalParity_apply]
  have hsum : ∀ s : Finset I, bitWeight (∑ i ∈ s, f i) ≤ ∑ i ∈ s, bitWeight (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [bitWeight]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (xLocal_bitWeight_add_le _ _).trans (Nat.add_le_add_left ih _)
  exact hsum Finset.univ

/-- The local syndrome weight is the sum over the four disjoint face regions. -/
theorem xLocal_weight_eq_regions
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    HammingWeight syndrome = ∑ face : XStarFace P x,
      (HammingWeight (xLocalLayerWord P x S syndrome face 0) +
        HammingWeight (xLocalLayerWord P x S syndrome face 1) +
        HammingWeight (xLocalStripWord P x S syndrome face 0) +
        HammingWeight (xLocalStripWord P x S syndrome face 1)) := by
  classical
  have h := (xLocalPieceCellEquiv P A4 R x S).sum_comp (fun c => bitWeight (syndrome c))
  rw [xLocal_weight_eq_sum]
  rw [← h]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro face _
  simp only [xLocal_weight_eq_sum]
  simp [xLocalPieceCellEquiv_apply, xLocalPieceCellMap, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    xLocalLayerWord, xLocalStripWord, Nat.add_assoc]

/-- The original four-region parity budget is bounded by the actual syndrome. -/
theorem xLocal_region_parity_budget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    (∑ face : XStarFace P x,
      (bitWeight (xLocalRegionParity P x S syndrome face (Sum.inl 0)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inl 1)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inr 0)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inr 1)))) ≤
      HammingWeight syndrome := by
  rw [xLocal_weight_eq_regions P A4 R x S]
  apply Finset.sum_le_sum
  intro face _
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (xLocal_parity_weight_le _) (xLocal_parity_weight_le _))
      (xLocal_parity_weight_le _)) (xLocal_parity_weight_le _)

/-- Coordinate formula for a singleton local correction. -/
theorem xLocalCoboundary_single_apply
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (edge : DoubleCylinderEdge P x S) (b : Field) (face : DoubleCylinderFace P x S) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S) (Pi.single edge b) face =
      b * doubleCylinderFaceEdgeMatrix P x S edge face := by
  classical
  unfold doubleCylinderBoundary2
  rw [wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_eq_single edge]
  · simp only [Pi.single_eq_same]
  · intro j hj
    rw [Pi.single_eq_of_ne hj, zero_mul]

private theorem xLocal_inner_horizontal_eq_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i a : Fin S.half) (j : Fin (S.half - 1))
    (b : Fin (S.half + 1)) :
    (Sum.inr (Sum.inl (f, i, j)) : SubdivisionEdge P x S) =
        subdivisionHorizontalEdge P x S g a b ↔
      f = g ∧ i = a ∧ j.val + 1 = b.val := by
  unfold subdivisionHorizontalEdge
  split_ifs with hb0 hbm
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ _ he
    omega
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ _ he
    have := j.isLt
    omega
  · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff]
    change (f = g ∧ i.val = a.val ∧ j.val = b.val - 1) ↔
      f = g ∧ i.val = a.val ∧ j.val + 1 = b.val
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf, hi, by omega⟩

private theorem xLocal_inner_vertical_eq_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i : Fin (S.half - 1)) (j b : Fin S.half)
    (a : Fin (S.half + 1)) :
    (Sum.inr (Sum.inr (f, i, j)) : SubdivisionEdge P x S) =
        subdivisionVerticalEdge P x S g a b ↔
      f = g ∧ i.val + 1 = a.val ∧ j = b := by
  unfold subdivisionVerticalEdge
  split_ifs with ha0 ham
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ he _
    omega
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ he _
    have := i.isLt
    omega
  · simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff]
    change (f = g ∧ i.val = a.val - 1 ∧ j.val = b.val) ↔
      f = g ∧ i.val + 1 = a.val ∧ j.val = b.val
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf, by omega, hj⟩

private theorem xLocal_inner_horizontal_ne_vertical
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i b : Fin S.half) (j : Fin (S.half - 1))
    (a : Fin (S.half + 1)) :
    (Sum.inr (Sum.inl (f, i, j)) : SubdivisionEdge P x S) ≠
      subdivisionVerticalEdge P x S g a b := by
  unfold subdivisionVerticalEdge
  split_ifs <;> simp

private theorem xLocal_inner_vertical_ne_horizontal
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (i : Fin (S.half - 1)) (j a : Fin S.half)
    (b : Fin (S.half + 1)) :
    (Sum.inr (Sum.inr (f, i, j)) : SubdivisionEdge P x S) ≠
      subdivisionHorizontalEdge P x S g a b := by
  unfold subdivisionHorizontalEdge
  split_ifs <;> simp

/-- An interior horizontal primal edge has exactly its two adjacent grid faces. -/
theorem xLocal_horizontal_dual_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i : Fin S.half) (j : Fin (S.half - 1))
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inl (f, i, j))) target =
      (if target = (f, i, stripStart S.half j) then 1 else 0) +
        (if target = (f, i, stripEnd S.half j) then 1 else 0) := by
  rcases target with ⟨g, a, b⟩
  have hstart : (f = g ∧ i = a ∧ j.val + 1 = b.val + 1) ↔
      (g, a, b) = (f, i, stripStart S.half j) := by
    simp only [Prod.mk.injEq, Fin.ext_iff, stripStart]
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf.symm, hi.symm, by omega⟩
  have hend : (f = g ∧ i = a ∧ j.val + 1 = b.val) ↔
      (g, a, b) = (f, i, stripEnd S.half j) := by
    simp only [Prod.mk.injEq, Fin.ext_iff, stripEnd]
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf.symm, hi.symm, by omega⟩
  simp only [subdivisionFaceEdgeMatrix, xLocal_inner_horizontal_eq_iff,
    xLocal_inner_horizontal_ne_vertical, ite_false, add_zero]
  change (if f = g ∧ i = a ∧ j.val + 1 = b.val then 1 else 0) +
      (if f = g ∧ i = a ∧ j.val + 1 = b.val + 1 then 1 else 0) = _
  simp only [hend, hstart, add_comm]

/-- An interior vertical primal edge has exactly its two adjacent grid faces. -/
theorem xLocal_vertical_dual_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) (i : Fin (S.half - 1)) (j : Fin S.half)
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S (Sum.inr (Sum.inr (f, i, j))) target =
      (if target = (f, stripStart S.half i, j) then 1 else 0) +
        (if target = (f, stripEnd S.half i, j) then 1 else 0) := by
  rcases target with ⟨g, a, b⟩
  have hstart : (f = g ∧ i.val + 1 = a.val + 1 ∧ j = b) ↔
      (g, a, b) = (f, stripStart S.half i, j) := by
    simp only [Prod.mk.injEq, Fin.ext_iff, stripStart]
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf.symm, by omega, hj.symm⟩
  have hend : (f = g ∧ i.val + 1 = a.val ∧ j = b) ↔
      (g, a, b) = (f, stripEnd S.half i, j) := by
    simp only [Prod.mk.injEq, Fin.ext_iff, stripEnd]
    constructor <;> rintro ⟨hf, hi, hj⟩ <;> exact ⟨hf.symm, by omega, hj.symm⟩
  simp only [subdivisionFaceEdgeMatrix, xLocal_inner_vertical_eq_iff,
    xLocal_inner_vertical_ne_horizontal, ite_false, zero_add, add_zero]
  change (if f = g ∧ i.val + 1 = a.val + 1 ∧ j = b then 1 else 0) +
      (if f = g ∧ i.val + 1 = a.val ∧ j = b then 1 else 0) = _
  simp only [hstart, hend]

/-- The concrete interior grid dual edge affects exactly its two mapped cells. -/
theorem xLocalGridDualEdge_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) (edge : GridEdge S.half)
    (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (xLocalGridDualEdge P x S face copy edge) target =
      (if target = Sum.inl (copy, face, gridStart S.half edge) then 1 else 0) +
        (if target = Sum.inl (copy, face, gridEnd S.half edge) then 1 else 0) := by
  rcases edge with ⟨i, j⟩ | ⟨i, j⟩
  all_goals rcases target with ⟨c, target⟩ | ⟨target, htarget⟩
  · by_cases hc : c = copy
    · subst c
      simpa [doubleCylinderFaceEdgeMatrix, xLocalGridDualEdge, gridStart, gridEnd]
        using xLocal_vertical_dual_incidence P x S face i j target
    · simp [doubleCylinderFaceEdgeMatrix, xLocalGridDualEdge, gridStart, gridEnd, hc,
        Ne.symm hc]
  · rcases target with original | interior
    · simp [doubleCylinderFaceEdgeMatrix, xLocalGridDualEdge]
    · simp [subdivisionBoundaryEdgeMember] at htarget

  · by_cases hc : c = copy
    · subst c
      simpa [doubleCylinderFaceEdgeMatrix, xLocalGridDualEdge, gridStart, gridEnd]
        using xLocal_horizontal_dual_incidence P x S face i j target
    · simp [doubleCylinderFaceEdgeMatrix, xLocalGridDualEdge, gridStart, gridEnd, hc,
        Ne.symm hc]
  · rcases target with original | interior
    · simp [doubleCylinderFaceEdgeMatrix, xLocalGridDualEdge]
    · simp [subdivisionBoundaryEdgeMember] at htarget

/-- Sum extension along a concrete finite coordinate map. -/
noncomputable def xLocalWordPush
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (embed : I → J) : Word Field I →ₗ[Field] Word Field J where
  toFun := fun f => ∑ i, Pi.single (embed i) (f i)
  map_add' := by
    intro f g
    simp [Pi.add_apply, Pi.single_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply funext
    intro j
    by_cases hj : j = embed i <;> simp [Pi.single_apply, hj, smul_eq_mul]

@[simp] theorem xLocalWordPush_single
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (embed : I → J) (i : I) (b : Field) :
    xLocalWordPush embed (Pi.single i b) = Pi.single (embed i) b := by
  classical
  change (∑ j, (Pi.single (embed j) ((Pi.single i b : Word Field I) j) : Word Field J)) = _
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    simp [Pi.single_eq_of_ne hj]

private theorem xLocal_linearMap_ext
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (D E : Word Field I →ₗ[Field] Word Field J)
    (h : ∀ i b, D (Pi.single i b) = E (Pi.single i b)) : D = E := by
  apply LinearMap.ext
  intro f
  rw [← word_eq_sum_single f]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact h i (f i)

private theorem xLocal_graphBoundary_single_coeff
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (start finish : I → J) (i : I) (b : Field) :
    graphBoundary start finish (Pi.single i b) =
      Pi.single (start i) b + Pi.single (finish i) b := by
  ext j
  change (∑ k, (Pi.single i b : Word Field I) k * graphEdgeBoundary start finish k j) = _
  rw [Fintype.sum_eq_single i]
  · simp [graphEdgeBoundary, Pi.single_apply, mul_add]
  · intro k hk
    rw [Pi.single_eq_of_ne hk, zero_mul]

/-- Lifting a proved endpoint profile commutes with the concrete coboundary. -/
theorem xLocal_lift_graphBoundary
    {V E C F : Type}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype C] [DecidableEq C] [Fintype F] [DecidableEq F]
    (D : Word Field C →ₗ[Field] Word Field F)
    (start finish : E → V) (cellMap : V → F) (edgeMap : E → C)
    (h : ∀ e b, D (Pi.single (edgeMap e) b) =
      Pi.single (cellMap (start e)) b + Pi.single (cellMap (finish e)) b) :
    D.comp (xLocalWordPush edgeMap) =
      (xLocalWordPush cellMap).comp (graphBoundary start finish) := by
  apply xLocal_linearMap_ext
  intro e b
  simp only [LinearMap.comp_apply, xLocalWordPush_single,
    xLocal_graphBoundary_single_coeff, map_add]
  simp only [xLocalWordPush_single, h]

/-- Every actual dual-grid basis correction has its two-cell endpoint syndrome. -/
theorem xLocalGridDualEdge_coboundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) (edge : GridEdge S.half) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalGridDualEdge P x S face copy edge) b) =
      Pi.single (Sum.inl (copy, face, gridStart S.half edge)) b +
        Pi.single (Sum.inl (copy, face, gridEnd S.half edge)) b := by
  ext target
  rw [xLocalCoboundary_single_apply, xLocalGridDualEdge_incidence]
  simp [Pi.single_apply, mul_add]

/-- Internal grid corrections commute with the actual X-local degree-one map. -/
theorem xLocalGridDualEdge_lift
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy : Two) :
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)).comp
        (xLocalWordPush (xLocalGridDualEdge P x S face copy)) =
      (xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (copy, face, ij))).comp
        (graphBoundary (gridStart S.half) (gridEnd S.half)) :=
  xLocal_lift_graphBoundary _ _ _ _ _ (xLocalGridDualEdge_coboundary P x S face copy)

private theorem xLocal_connectingWeight_add_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f g : Word Field (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S (f + g) ≤
      connectingWeight P A x S f + connectingWeight P A x S g := by
  unfold connectingWeight
  simp only [map_add, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => HammingWeight_add_le _ _)

/-- The actual connecting-map weight is subadditive under finite assembly. -/
theorem xLocal_connectingWeight_sum_le
    {I : Type} [Fintype I] (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (f : I → Word Field (DoubleCylinderEdge P x S)) :
    connectingWeight P A x S (∑ i, f i) ≤ ∑ i, connectingWeight P A x S (f i) := by
  classical
  have h : ∀ s : Finset I, connectingWeight P A x S (∑ i ∈ s, f i) ≤
      ∑ i ∈ s, connectingWeight P A x S (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [connectingWeight]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (xLocal_connectingWeight_add_le P A x S _ _).trans
          (Nat.add_le_add_left ih _)
  exact h Finset.univ

/-- Interior dual-grid corrections have no X-to-Q output. -/
theorem xLocalGridDualEdge_connectingWeight_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy : Two)
    (correction : Word Field (GridEdge S.half)) :
    connectingWeight P A x S
      (xLocalWordPush (xLocalGridDualEdge P x S face copy) correction) = 0 := by
  have h := xLocal_connectingWeight_sum_le P A x S
    (fun edge => Pi.single (xLocalGridDualEdge P x S face copy edge) (correction edge))
  have hzero : ∀ edge : GridEdge S.half,
      connectingWeight P A x S
        (Pi.single (xLocalGridDualEdge P x S face copy edge) (correction edge)) = 0 := by
    intro edge
    apply connectingWeight_single_eq_zero_of_other
    · cases edge <;> rfl
    · cases edge <;> rfl
  simp only [hzero, Finset.sum_const_zero] at h
  exact Nat.eq_zero_of_le_zero h

/-- An arbitrary syndrome inside one square region can be reduced to its
root parity using concrete cylinder edges with zero connecting-map cost. -/
theorem xLocal_grid_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy : Two)
    (root : GridVertex S.half) (syndrome : Word Field (GridVertex S.half)) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f =
        xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (copy, face, ij))
          (syndrome + Pi.single root (totalParity syndrome)) ∧
      connectingWeight P A x S f = 0 := by
  obtain ⟨correction, hc⟩ := grid_exists_boundary_eq_add_rootParity
    S.half S.half_pos root syndrome
  refine ⟨xLocalWordPush (xLocalGridDualEdge P x S face copy) correction, ?_,
    xLocalGridDualEdge_connectingWeight_zero P A x S face copy correction⟩
  have h := LinearMap.congr_fun (xLocalGridDualEdge_lift P x S face copy) correction
  simpa only [LinearMap.comp_apply, hc] using h

/-- A concrete vertical edge at an interior point of one original Q-Z side. -/
def xLocalBoundaryInteriorVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarBoundaryEdge P x) (i : Fin (S.half - 1)) :
    SubdivisionBoundaryVertex P x S :=
  ⟨Sum.inr (Sum.inl (xStarBoundaryEdgeToStar P x e, i)), e.property⟩

private theorem xLocal_strip_start_eq_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e f : XStarBoundaryEdge P x) (i : Fin (S.half - 1)) (k : Fin S.half) :
    xLocalBoundaryInteriorVertex P x S e i =
        subdivisionBoundaryEdgeStart P x S (subdivisionOriginalBoundaryEdge P x S f k) ↔
      e = f ∧ i.val + 1 = k.val := by
  rw [Subtype.ext_iff, subdivisionBoundaryEdgeStart_value]
  change (Sum.inr (Sum.inl (xStarBoundaryEdgeToStar P x e, i)) :
      SubdivisionVertex P x S) =
        subdivisionSegmentStart P x S (xStarBoundaryEdgeToStar P x f) k ↔ _
  unfold subdivisionSegmentStart
  split_ifs with hk
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ he
    omega
  · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Subtype.ext_iff, Fin.ext_iff]
    change (e.val = f.val ∧ i.val = k.val - 1) ↔ e.val = f.val ∧ i.val + 1 = k.val
    have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    constructor
    · rintro ⟨he, hi⟩
      exact ⟨he, by omega⟩
    · rintro ⟨he, hi⟩
      exact ⟨he, by omega⟩

private theorem xLocal_strip_end_eq_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e f : XStarBoundaryEdge P x) (i : Fin (S.half - 1)) (k : Fin S.half) :
    xLocalBoundaryInteriorVertex P x S e i =
        subdivisionBoundaryEdgeEnd P x S (subdivisionOriginalBoundaryEdge P x S f k) ↔
      e = f ∧ i.val = k.val := by
  rw [Subtype.ext_iff, subdivisionBoundaryEdgeEnd_value]
  change (Sum.inr (Sum.inl (xStarBoundaryEdgeToStar P x e, i)) :
      SubdivisionVertex P x S) =
        subdivisionSegmentEnd P x S (xStarBoundaryEdgeToStar P x f) k ↔ _
  unfold subdivisionSegmentEnd
  split_ifs with hk
  · simp only [Sum.inr_ne_inl, false_iff, not_and]
    intro _ he
    have := i.isLt
    omega
  · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Subtype.ext_iff, Fin.ext_iff]
    rfl

private theorem xLocal_boundary_segment_eq_iff
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e f : XStarBoundaryEdge P x) (i j : Fin S.half) :
    subdivisionOriginalBoundaryEdge P x S e i = subdivisionOriginalBoundaryEdge P x S f j ↔
      e = f ∧ i = j := by
  constructor
  · intro h
    exact Prod.mk.inj ((xLocal_boundary_segment_bijective P x S).1 h)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A strip-interior dual edge affects exactly its two adjacent rectangles. -/
theorem xLocalStripDualEdge_incidence
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) (i : StripEdge S.half)
    (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (xLocalStripDualEdge P x S face side i) target =
      (if target = Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripStart S.half i)) then 1 else 0) +
      (if target = Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripEnd S.half i)) then 1 else 0) := by
  rcases target with target | target
  · simp [doubleCylinderFaceEdgeMatrix, xLocalStripDualEdge]
  · obtain ⟨⟨e, k⟩, rfl⟩ := (xLocal_boundary_segment_bijective P x S).2 target
    change (if xLocalBoundaryInteriorVertex P x S (xStarFaceBoundaryEdge P x face side) i =
          subdivisionBoundaryEdgeStart P x S (subdivisionOriginalBoundaryEdge P x S e k)
        then 1 else 0) +
      (if xLocalBoundaryInteriorVertex P x S (xStarFaceBoundaryEdge P x face side) i =
          subdivisionBoundaryEdgeEnd P x S (subdivisionOriginalBoundaryEdge P x S e k)
        then 1 else 0) = _
    simp only [xLocal_strip_start_eq_iff, xLocal_strip_end_eq_iff,
      Sum.inr.injEq, xLocal_boundary_segment_eq_iff, Fin.ext_iff]
    change (if xStarFaceBoundaryEdge P x face side = e ∧ i.val + 1 = k.val then 1 else 0) +
      (if xStarFaceBoundaryEdge P x face side = e ∧ i.val = k.val then 1 else 0) =
      (if e = xStarFaceBoundaryEdge P x face side ∧ k.val = i.val then 1 else 0) +
      (if e = xStarFaceBoundaryEdge P x face side ∧ k.val = i.val + 1 then 1 else 0)
    rw [add_comm]
    congr 1 <;> congr 1 <;> exact propext (and_congr eq_comm eq_comm)

/-- Exact two-rectangle coboundary of an internal strip correction. -/
theorem xLocalStripDualEdge_coboundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) (edge : StripEdge S.half) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalStripDualEdge P x S face side edge) b) =
      Pi.single (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripStart S.half edge))) b +
      Pi.single (Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (stripEnd S.half edge))) b := by
  ext target
  rw [xLocalCoboundary_single_apply, xLocalStripDualEdge_incidence]
  simp [Pi.single_apply, mul_add]

/-- The strip correction lift commutes with the actual X-local coboundary. -/
theorem xLocalStripDualEdge_lift
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (side : Two) :
    (wordLinearMapTranspose (doubleCylinderBoundary2 P x S)).comp
        (xLocalWordPush (xLocalStripDualEdge P x S face side)) =
      (xLocalWordPush (fun i : StripVertex S.half => Sum.inr
        (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i))).comp
        (graphBoundary (stripStart S.half) (stripEnd S.half)) :=
  xLocal_lift_graphBoundary _ _ _ _ _ (xLocalStripDualEdge_coboundary P x S face side)

/-- Strip-interior corrections have zero actual X-to-Q weight. -/
theorem xLocalStripDualEdge_connectingWeight_zero
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (side : Two)
    (correction : Word Field (StripEdge S.half)) :
    connectingWeight P A x S
      (xLocalWordPush (xLocalStripDualEdge P x S face side) correction) = 0 := by
  have h := xLocal_connectingWeight_sum_le P A x S
    (fun edge => Pi.single (xLocalStripDualEdge P x S face side edge) (correction edge))
  have hzero : ∀ edge : StripEdge S.half,
      connectingWeight P A x S
        (Pi.single (xLocalStripDualEdge P x S face side edge) (correction edge)) = 0 := by
    intro edge
    exact connectingWeight_single_eq_zero_of_other P A x S _ rfl rfl _
  simp only [hzero, Finset.sum_const_zero] at h
  exact Nat.eq_zero_of_le_zero h

/-- Strip syndrome cleanup uses concrete internal vertical edges and no output budget. -/
theorem xLocal_strip_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (side : Two)
    (root : StripVertex S.half) (syndrome : Word Field (StripVertex S.half)) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f =
        xLocalWordPush (fun i : StripVertex S.half => Sum.inr
          (subdivisionOriginalBoundaryEdge P x S (xStarFaceBoundaryEdge P x face side) i))
          (syndrome + Pi.single root (totalParity syndrome)) ∧
      connectingWeight P A x S f = 0 := by
  obtain ⟨correction, hc⟩ := strip_exists_boundary_eq_add_rootParity
    S.half S.half_pos root syndrome
  refine ⟨xLocalWordPush (xLocalStripDualEdge P x S face side) correction, ?_,
    xLocalStripDualEdge_connectingWeight_zero P A x S face side correction⟩
  have h := LinearMap.congr_fun (xLocalStripDualEdge_lift P x S face side) correction
  simpa only [LinearMap.comp_apply, hc] using h

/-- The last syndrome coordinate in a nonempty subdivided arm. -/
def xLocalLast (S : OddScale) : Fin S.half := ⟨S.half - 1, by have := S.half_pos; omega⟩

/-- The square-region root next to the old Z corner. -/
def xLocalGridRoot (S : OddScale) : GridVertex S.half := (xLocalLast S, xLocalLast S)

/-- The four root syndrome coordinates of one piece. -/
def xLocalRegionRoot (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) : Two ⊕ Two → DoubleCylinderFace P x S
  | Sum.inl copy => Sum.inl (copy, face, xLocalGridRoot S)
  | Sum.inr side => Sum.inr (subdivisionOriginalBoundaryEdge P x S
      (xStarFaceBoundaryEdge P x face side) (xLocalLast S))

/-- One of the four copied boundary crossings adjacent to the old Z corner. -/
def xLocalLayerStripConnector (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (copy side : Two) : DoubleCylinderEdge P x S :=
  Sum.inl (copy, (subdivisionOriginalBoundaryEdge P x S
    (xStarFaceBoundaryEdge P x face side) (xLocalLast S)).val)

/-- The vertical old-Z corner shared by the two strips. -/
def xLocalStripStripConnector (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) : DoubleCylinderEdge P x S :=
  Sum.inr (subdivisionOriginalBoundaryVertex P x S
    (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0)))

private theorem xLocal_faceQZ_eq_iff
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (f g : XStarFace P x) (s t : Two) :
    xStarFaceQZEdge P x f s = xStarFaceQZEdge P x g t ↔ f = g ∧ s = t := by
  constructor
  · intro h
    have hb : xStarFaceBoundaryEdge P x f s = xStarFaceBoundaryEdge P x g t :=
      Subtype.ext (congrArg (fun e : XStarEdge P x => e.val) h)
    exact Prod.mk.inj (xLocal_boundary_side_injective P R x hb)
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem xLocal_boundary_horizontal_eq_iff
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (f g : XStarFace P x) (s : Two)
    (k a : Fin S.half) (b : Fin (S.half + 1)) :
    (Sum.inl (xStarFaceQZEdge P x f s, k) : SubdivisionEdge P x S) =
        subdivisionHorizontalEdge P x S g a b ↔
      f = g ∧ s = 1 ∧ k = a ∧ b.val = S.half := by
  unfold subdivisionHorizontalEdge
  split_ifs with hb0 hbm
  · have hm : b.val ≠ S.half := by have := S.half_pos; omega
    simp [xStarFaceQZEdge, xStarFaceXQEdge, hm]
  · simp [xLocal_faceQZ_eq_iff P R, hbm, and_assoc]
  · simp [hbm]

private theorem xLocal_boundary_vertical_eq_iff
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (f g : XStarFace P x) (s : Two)
    (k b : Fin S.half) (a : Fin (S.half + 1)) :
    (Sum.inl (xStarFaceQZEdge P x f s, k) : SubdivisionEdge P x S) =
        subdivisionVerticalEdge P x S g a b ↔
      f = g ∧ s = 0 ∧ k = b ∧ a.val = S.half := by
  unfold subdivisionVerticalEdge
  split_ifs with ha0 ham
  · have hm : a.val ≠ S.half := by have := S.half_pos; omega
    simp [xStarFaceQZEdge, xStarFaceXQEdge, hm]
  · simp [xLocal_faceQZ_eq_iff P R, ham, and_assoc]
  · simp [ham]

/-- Each terminal boundary segment has one adjacent terminal grid cell. -/
theorem xLocal_terminal_boundary_grid_incidence
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (side : Two)
    (target : SubdivisionFace P x S) :
    subdivisionFaceEdgeMatrix P x S
      (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (xLocalLast S)).val target =
      if target = (face, xLocalGridRoot S) then 1 else 0 := by
  rcases target with ⟨g, a, b⟩
  have ha : a.val ≠ S.half := Nat.ne_of_lt a.isLt
  have hb : b.val ≠ S.half := Nat.ne_of_lt b.isLt
  have hal : a.val + 1 = S.half ↔ a.val = S.half - 1 := by
    have := S.half_pos
    omega
  have hbl : b.val + 1 = S.half ↔ b.val = S.half - 1 := by
    have := S.half_pos
    omega
  change subdivisionFaceEdgeMatrix P x S
    (Sum.inl (xStarFaceQZEdge P x face side, xLocalLast S)) (g, a, b) = _
  fin_cases side
  · simp [subdivisionFaceEdgeMatrix, xLocal_boundary_horizontal_eq_iff P R,
      xLocal_boundary_vertical_eq_iff P R, xLocalLast, xLocalGridRoot,
      ha, hb, hal, hbl, Fin.ext_iff, eq_comm, and_assoc, and_left_comm, and_comm]
    change (if a.val = S.half - 1 ∧ b.val = S.half - 1 ∧ face = g then (1 : Field) else 0) =
      (if b.val = S.half - 1 ∧ S.half = a.val + 1 ∧ face = g then 1 else 0) +
      (if b.val = S.half - 1 ∧ S.half = a.val ∧ face = g then 1 else 0)
    simp [Ne.symm ha, ← hal, eq_comm, and_assoc, and_left_comm, and_comm]
  · simp [subdivisionFaceEdgeMatrix, xLocal_boundary_horizontal_eq_iff P R,
      xLocal_boundary_vertical_eq_iff P R, xLocalLast, xLocalGridRoot,
      ha, hb, hal, hbl, Fin.ext_iff, eq_comm, and_assoc, and_left_comm, and_comm]
    change (if a.val = S.half - 1 ∧ b.val = S.half - 1 ∧ face = g then (1 : Field) else 0) =
      (if a.val = S.half - 1 ∧ S.half = b.val ∧ face = g then 1 else 0) +
      (if a.val = S.half - 1 ∧ S.half = b.val + 1 ∧ face = g then 1 else 0)
    simp [Ne.symm hb, ← hbl, eq_comm, and_assoc, and_left_comm, and_comm]

/-- A copied boundary connector joins precisely one grid and one strip root. -/
theorem xLocalLayerStripConnector_incidence
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy side : Two)
    (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S
        (xLocalLayerStripConnector P x S face copy side) target =
      (if target = xLocalRegionRoot P x S face (Sum.inl copy) then 1 else 0) +
      (if target = xLocalRegionRoot P x S face (Sum.inr side) then 1 else 0) := by
  rcases target with ⟨c, target⟩ | target
  · by_cases hc : c = copy
    · subst c
      simpa [doubleCylinderFaceEdgeMatrix, xLocalLayerStripConnector, xLocalRegionRoot]
        using xLocal_terminal_boundary_grid_incidence P R x S face side target
    · simp [doubleCylinderFaceEdgeMatrix, xLocalLayerStripConnector, xLocalRegionRoot,
        hc, Ne.symm hc]
  · change (if (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face side) (xLocalLast S)).val = target.val
        then (1 : Field) else 0) =
      (if Sum.inr target = xLocalRegionRoot P x S face (Sum.inl copy) then 1 else 0) +
      (if Sum.inr target = xLocalRegionRoot P x S face (Sum.inr side) then 1 else 0)
    simp only [xLocalRegionRoot, Sum.inr_ne_inl, if_false, zero_add, Sum.inr.injEq]
    congr 1
    exact propext (Subtype.ext_iff.symm.trans eq_comm)

/-- Exact endpoint syndrome of each cost-one connector. -/
theorem xLocalLayerStripConnector_coboundary
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy side : Two) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalLayerStripConnector P x S face copy side) b) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inl copy)) b +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr side)) b := by
  ext target
  rw [xLocalCoboundary_single_apply, xLocalLayerStripConnector_incidence P R]
  simp [Pi.single_apply, mul_add]

/-- Each copied boundary connector contributes at most one output bit. -/
theorem xLocalLayerStripConnector_weight_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (x : P.X) (S : OddScale) (face : XStarFace P x) (copy side : Two) (b : Field) :
    connectingWeight P A x S (Pi.single (xLocalLayerStripConnector P x S face copy side) b) ≤
      bitWeight b :=
  connectingWeight_single_le_of_copied P A x S _ (P.faceQ face.val side) rfl b

/-- The vertical old-Z connector contributes at most two output bits. -/
theorem xLocalStripStripConnector_weight_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (b : Field) :
    connectingWeight P A x S (Pi.single (xLocalStripStripConnector P x S face) b) ≤
      2 * bitWeight b :=
  connectingWeight_single_le_of_vertical P A R x S _ (P.faceZ face.val) rfl b

private theorem xLocal_faceZ_eq_iff
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (f g : XStarFace P x) : P.faceZ f.val = P.faceZ g.val ↔ f = g := by
  constructor
  · intro hz
    have hfx : P.faceX f.val = x := by simpa [xStarFaceMember] using f.property
    have hgx : P.faceX g.val = x := by simpa [xStarFaceMember] using g.property
    exact Subtype.ext (R.faceXZ_injective (Prod.ext (hfx.trans hgx.symm) hz))
  · rintro rfl
    rfl

private theorem xLocal_boundary_side_eq_iff
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (f g : XStarFace P x) (s t : Two) :
    xStarFaceBoundaryEdge P x f s = xStarFaceBoundaryEdge P x g t ↔ f = g ∧ s = t :=
by
  constructor
  · intro h
    exact Prod.mk.inj (xLocal_boundary_side_injective P R x h)
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem xLocal_Z_corner_start_ne
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f g : XStarFace P x) (side : Two) (k : Fin S.half) :
    subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x f 0)) ≠
      subdivisionBoundaryEdgeStart P x S (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x g side) k) := by
  intro h
  have hv := congrArg Subtype.val h
  rw [subdivisionBoundaryEdgeStart_value] at hv
  change (Sum.inl (xStarFaceZVertex P x f) : SubdivisionVertex P x S) =
    subdivisionSegmentStart P x S (xStarFaceQZEdge P x g side) k at hv
  by_cases hk : k.val = 0
  · simp [subdivisionSegmentStart, hk, xStarEdgeStart, xStarFaceQZEdge,
      xStarFaceZVertex, Subtype.ext_iff] at hv
  · simp [subdivisionSegmentStart, hk] at hv

private theorem xLocal_Z_corner_end_eq_iff
    (P : TannerSquarePresentation) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (f g : XStarFace P x) (side : Two) (k : Fin S.half) :
    subdivisionOriginalBoundaryVertex P x S
        (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x f 0)) =
      subdivisionBoundaryEdgeEnd P x S (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x g side) k) ↔ f = g ∧ k.val + 1 = S.half := by
  rw [Subtype.ext_iff, subdivisionBoundaryEdgeEnd_value]
  change (Sum.inl (xStarFaceZVertex P x f) : SubdivisionVertex P x S) =
    subdivisionSegmentEnd P x S (xStarFaceQZEdge P x g side) k ↔ _
  by_cases hk : k.val + 1 = S.half
  · simp only [subdivisionSegmentEnd, dif_pos hk, Sum.inl.injEq]
    change xStarFaceZVertex P x f = xStarEdgeEnd P x (xStarFaceQZEdge P x g side) ↔ _
    have hend : xStarEdgeEnd P x (xStarFaceQZEdge P x g side) = xStarFaceZVertex P x g := rfl
    rw [hend]
    simpa only [xStarFaceZVertex, Subtype.mk.injEq, Vertex.z.injEq, hk, and_true]
      using xLocal_faceZ_eq_iff P R x f g
  · simp [subdivisionSegmentEnd, hk]

/-- The vertical Z-corner edge joins precisely the two strip roots of its piece. -/
theorem xLocalStripStripConnector_incidence
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (target : DoubleCylinderFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (xLocalStripStripConnector P x S face) target =
      (if target = xLocalRegionRoot P x S face (Sum.inr 0) then 1 else 0) +
        (if target = xLocalRegionRoot P x S face (Sum.inr 1) then 1 else 0) := by
  rcases target with target | target
  · simp [doubleCylinderFaceEdgeMatrix, xLocalStripStripConnector, xLocalRegionRoot]
  · obtain ⟨⟨boundary, k⟩, rfl⟩ := (xLocal_boundary_segment_bijective P x S).2 target
    obtain ⟨⟨g, side⟩, rfl⟩ := xLocal_boundary_side_surjective P A4 x boundary
    change (if subdivisionOriginalBoundaryVertex P x S
          (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0)) =
          subdivisionBoundaryEdgeStart P x S (subdivisionOriginalBoundaryEdge P x S
            (xStarFaceBoundaryEdge P x g side) k) then 1 else 0) +
      (if subdivisionOriginalBoundaryVertex P x S
          (xBoundaryEdgeEnd P x (xStarFaceBoundaryEdge P x face 0)) =
          subdivisionBoundaryEdgeEnd P x S (subdivisionOriginalBoundaryEdge P x S
            (xStarFaceBoundaryEdge P x g side) k) then 1 else 0) = _
    rw [if_neg (xLocal_Z_corner_start_ne P x S face g side k), zero_add]
    simp only [xLocal_Z_corner_end_eq_iff P R]
    have hkl : k.val + 1 = S.half ↔ k.val = S.half - 1 := by
      have := S.half_pos
      omega
    have hkLast : k = xLocalLast S ↔ k.val = S.half - 1 := Fin.ext_iff
    simp only [xLocalRegionRoot, Sum.inr.injEq, xLocal_boundary_segment_eq_iff,
      xLocal_boundary_side_eq_iff P R, hkl, hkLast]
    change (if face = g ∧ k.val = S.half - 1 then (1 : Field) else 0) =
      (if (g = face ∧ side = 0) ∧ k.val = S.half - 1 then 1 else 0) +
      (if (g = face ∧ side = 1) ∧ k.val = S.half - 1 then 1 else 0)
    by_cases hfg : face = g
    · subst g
      fin_cases side <;> simp [Fin.ext_iff]
    · simp only [hfg, Ne.symm hfg, false_and, if_false, zero_add]

/-- Exact endpoint syndrome of the cost-two connector. -/
theorem xLocalStripStripConnector_coboundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (b : Field) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (Pi.single (xLocalStripStripConnector P x S face) b) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inr 0)) b +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 1)) b := by
  ext target
  rw [xLocalCoboundary_single_apply, xLocalStripStripConnector_incidence P A4 R]
  simp [Pi.single_apply, mul_add]

/-- The five explicit connector corrections selected by the four region parities. -/
noncomputable def xLocalRootCorrection
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b l r : Field) : Word Field (DoubleCylinderEdge P x S) :=
  let c := pieceCrossingCoefficients a b l r
  Pi.single (xLocalLayerStripConnector P x S face 0 0) (c 0) +
    Pi.single (xLocalLayerStripConnector P x S face 0 1) (c 1) +
    Pi.single (xLocalLayerStripConnector P x S face 1 0) (c 2) +
    Pi.single (xLocalLayerStripConnector P x S face 1 1) (c 3) +
    Pi.single (xLocalStripStripConnector P x S face) (c 4)

/-- The finite connector construction has exactly the four desired root syndromes. -/
theorem xLocalRootCorrection_coboundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b l r : Field) (heven : a + b + l + r = 0) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (xLocalRootCorrection P x S face a b l r) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inl 0)) a +
        Pi.single (xLocalRegionRoot P x S face (Sum.inl 1)) b +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 0)) l +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 1)) r := by
  obtain ⟨ha, hb, hl, hr, _⟩ := pieceCrossingCoefficients_spec a b l r heven
  let c := pieceCrossingCoefficients a b l r
  have hsum : wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
      (xLocalRootCorrection P x S face a b l r) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inl 0)) (c 0 + c 1) +
        Pi.single (xLocalRegionRoot P x S face (Sum.inl 1)) (c 2 + c 3) +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 0)) (c 0 + c 2 + c 4) +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 1)) (c 1 + c 3 + c 4) := by
    simp only [xLocalRootCorrection, map_add, xLocalLayerStripConnector_coboundary P R,
      xLocalStripStripConnector_coboundary P A4 R, Pi.single_add]
    dsimp only [c]
    abel
  rw [hsum]
  simpa only [c, ha, hb, hl, hr]

/-- The connector construction obeys the exact four-region crossing budget. -/
theorem xLocalRootCorrection_weight_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b l r : Field) (heven : a + b + l + r = 0) :
    connectingWeight P A x S (xLocalRootCorrection P x S face a b l r) ≤
      pieceCrossingCost a b l r := by
  have hcoeff := (pieceCrossingCoefficients_spec a b l r heven).2.2.2.2
  let c := pieceCrossingCoefficients a b l r
  let f0 : Word Field (DoubleCylinderEdge P x S) := Pi.single (xLocalLayerStripConnector P x S face 0 0) (c 0)
  let f1 : Word Field (DoubleCylinderEdge P x S) := Pi.single (xLocalLayerStripConnector P x S face 0 1) (c 1)
  let f2 : Word Field (DoubleCylinderEdge P x S) := Pi.single (xLocalLayerStripConnector P x S face 1 0) (c 2)
  let f3 : Word Field (DoubleCylinderEdge P x S) := Pi.single (xLocalLayerStripConnector P x S face 1 1) (c 3)
  let f4 : Word Field (DoubleCylinderEdge P x S) := Pi.single (xLocalStripStripConnector P x S face) (c 4)
  have h01 := xLocal_connectingWeight_add_le P A x S f0 f1
  have h012 := xLocal_connectingWeight_add_le P A x S (f0 + f1) f2
  have h0123 := xLocal_connectingWeight_add_le P A x S (f0 + f1 + f2) f3
  have h01234 := xLocal_connectingWeight_add_le P A x S (f0 + f1 + f2 + f3) f4
  have h0 : connectingWeight P A x S f0 ≤ bitWeight (c 0) :=
    xLocalLayerStripConnector_weight_le P A x S face 0 0 (c 0)
  have h1 : connectingWeight P A x S f1 ≤ bitWeight (c 1) :=
    xLocalLayerStripConnector_weight_le P A x S face 0 1 (c 1)
  have h2 : connectingWeight P A x S f2 ≤ bitWeight (c 2) :=
    xLocalLayerStripConnector_weight_le P A x S face 1 0 (c 2)
  have h3 : connectingWeight P A x S f3 ≤ bitWeight (c 3) :=
    xLocalLayerStripConnector_weight_le P A x S face 1 1 (c 3)
  have h4 : connectingWeight P A x S f4 ≤ 2 * bitWeight (c 4) :=
    xLocalStripStripConnector_weight_le P A R x S face (c 4)
  change connectingWeight P A x S (f0 + f1 + f2 + f3 + f4) ≤ _
  change bitWeight (c 0) + bitWeight (c 1) + bitWeight (c 2) +
    bitWeight (c 3) + 2 * bitWeight (c 4) ≤ pieceCrossingCost a b l r at hcoeff
  omega

/-- Extension of one piece's four-region syndrome into the actual cylinder. -/
def xLocalPieceWord (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (syndrome : Word Field (DoubleCylinderFace P x S)) :
    Word Field (XLocalPieceCell S) := fun cell => syndrome (xLocalPieceCellMap P x S (face, cell))

/-- Region extension decomposes as its two grid words and two strip words. -/
theorem xLocalPieceWord_push_eq_regions
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (syndrome : Word Field (DoubleCylinderFace P x S)) :
    xLocalWordPush (fun cell => xLocalPieceCellMap P x S (face, cell))
        (xLocalPieceWord P x S face syndrome) =
      xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (0, face, ij))
        (xLocalLayerWord P x S syndrome face 0) +
      xLocalWordPush (fun ij : GridVertex S.half => Sum.inl (1, face, ij))
        (xLocalLayerWord P x S syndrome face 1) +
      xLocalWordPush (fun i : StripVertex S.half => Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face 0) i)) (xLocalStripWord P x S syndrome face 0) +
      xLocalWordPush (fun i : StripVertex S.half => Sum.inr (subdivisionOriginalBoundaryEdge P x S
        (xStarFaceBoundaryEdge P x face 1) i)) (xLocalStripWord P x S syndrome face 1) := by
  classical
  change (∑ cell, (Pi.single (xLocalPieceCellMap P x S (face, cell))
    (xLocalPieceWord P x S face syndrome cell) : Word Field (DoubleCylinderFace P x S))) = _
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    xLocalPieceWord, xLocalPieceCellMap, xLocalWordPush, xLocalLayerWord,
    xLocalStripWord, add_assoc]

/-- Each even-parity piece has a concrete correction with the exact crossing budget. -/
theorem xLocal_piece_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (face : XStarFace P x)
    (syndrome : Word Field (DoubleCylinderFace P x S))
    (heven : xLocalRegionParity P x S syndrome face (Sum.inl 0) +
      xLocalRegionParity P x S syndrome face (Sum.inl 1) +
      xLocalRegionParity P x S syndrome face (Sum.inr 0) +
      xLocalRegionParity P x S syndrome face (Sum.inr 1) = 0) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f =
        xLocalWordPush (fun cell => xLocalPieceCellMap P x S (face, cell))
          (xLocalPieceWord P x S face syndrome) ∧
      connectingWeight P A x S f ≤ pieceCrossingCost
        (xLocalRegionParity P x S syndrome face (Sum.inl 0))
        (xLocalRegionParity P x S syndrome face (Sum.inl 1))
        (xLocalRegionParity P x S syndrome face (Sum.inr 0))
        (xLocalRegionParity P x S syndrome face (Sum.inr 1)) := by
  let a := xLocalRegionParity P x S syndrome face (Sum.inl 0)
  let b := xLocalRegionParity P x S syndrome face (Sum.inl 1)
  let l := xLocalRegionParity P x S syndrome face (Sum.inr 0)
  let r := xLocalRegionParity P x S syndrome face (Sum.inr 1)
  obtain ⟨f0, hf0, hw0⟩ := xLocal_grid_cleanup P A x S face 0 (xLocalGridRoot S)
    (xLocalLayerWord P x S syndrome face 0)
  obtain ⟨f1, hf1, hw1⟩ := xLocal_grid_cleanup P A x S face 1 (xLocalGridRoot S)
    (xLocalLayerWord P x S syndrome face 1)
  obtain ⟨fl, hfl, hwl⟩ := xLocal_strip_cleanup P A x S face 0 (xLocalLast S)
    (xLocalStripWord P x S syndrome face 0)
  obtain ⟨fr, hfr, hwr⟩ := xLocal_strip_cleanup P A x S face 1 (xLocalLast S)
    (xLocalStripWord P x S syndrome face 1)
  let fc := xLocalRootCorrection P x S face a b l r
  have hfc := xLocalRootCorrection_coboundary P A4 R x S face a b l r heven
  have hwc := xLocalRootCorrection_weight_le P A R x S face a b l r heven
  refine ⟨f0 + f1 + fl + fr + fc, ?_, ?_⟩
  · rw [xLocalPieceWord_push_eq_regions]
    simp only [map_add, hf0, hf1, hfl, hfr, fc, hfc, xLocalWordPush_single]
    dsimp only [a, b, l, r, xLocalRegionParity, xLocalRegionRoot]
    have hcancel : ∀ w : Word Field (DoubleCylinderFace P x S), w + w = 0 :=
      fun w => ZModModule.add_self w
    abel_nf
    have htwo : ∀ w : Word Field (DoubleCylinderFace P x S), (2 : ℤ) • w = 0 := by
      intro w
      rw [show (2 : ℤ) = 1 + 1 by rfl, add_zsmul, one_zsmul]
      exact hcancel w
    simp only [htwo, add_zero, zero_add]
  · have h01 := xLocal_connectingWeight_add_le P A x S f0 f1
    have h01l := xLocal_connectingWeight_add_le P A x S (f0 + f1) fl
    have h01lr := xLocal_connectingWeight_add_le P A x S (f0 + f1 + fl) fr
    have htotal := xLocal_connectingWeight_add_le P A x S (f0 + f1 + fl + fr) fc
    change connectingWeight P A x S fc ≤ pieceCrossingCost a b l r at hwc
    change connectingWeight P A x S (f0 + f1 + fl + fr + fc) ≤ pieceCrossingCost a b l r
    omega

/-- Reassembling every disjoint piece recovers the original syndrome exactly. -/
theorem xLocalPieceWord_sum_push
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    (∑ face : XStarFace P x,
      xLocalWordPush (fun cell => xLocalPieceCellMap P x S (face, cell))
        (xLocalPieceWord P x S face syndrome)) = syndrome := by
  classical
  have h := (xLocalPieceCellEquiv P A4 R x S).sum_comp
    (fun target => Pi.single target (syndrome target))
  simp only [xLocalPieceCellEquiv_apply] at h
  rw [word_eq_sum_single syndrome] at h
  simpa only [Fintype.sum_prod_type, xLocalWordPush, LinearMap.coe_mk, AddHom.coe_mk,
    xLocalPieceWord, xLocalPieceCellEquiv, Equiv.ofBijective_apply] using h

/-- A syndrome even on every face piece has a concrete correction bounded by
the sum of its four-region crossing budgets. -/
theorem xLocal_even_pieces_cleanup
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (A4 : TannerSquareAdmissibleV4 P) (R : TannerSquareCellularRegular P)
    (x : P.X) (S : OddScale) (syndrome : Word Field (DoubleCylinderFace P x S))
    (heven : ∀ face : XStarFace P x,
      xLocalRegionParity P x S syndrome face (Sum.inl 0) +
      xLocalRegionParity P x S syndrome face (Sum.inl 1) +
      xLocalRegionParity P x S syndrome face (Sum.inr 0) +
      xLocalRegionParity P x S syndrome face (Sum.inr 1) = 0) :
    ∃ f : Word Field (DoubleCylinderEdge P x S),
      wordLinearMapTranspose (doubleCylinderBoundary2 P x S) f = syndrome ∧
      connectingWeight P A x S f ≤ ∑ face : XStarFace P x, pieceCrossingCost
        (xLocalRegionParity P x S syndrome face (Sum.inl 0))
        (xLocalRegionParity P x S syndrome face (Sum.inl 1))
        (xLocalRegionParity P x S syndrome face (Sum.inr 0))
        (xLocalRegionParity P x S syndrome face (Sum.inr 1)) := by
  classical
  choose f hf hw using fun face => xLocal_piece_cleanup P A A4 R x S face syndrome (heven face)
  refine ⟨∑ face, f face, ?_, ?_⟩
  · simp only [map_sum, hf]
    exact xLocalPieceWord_sum_push P A4 R x S syndrome
  · exact (xLocal_connectingWeight_sum_le P A x S f).trans
      (Finset.sum_le_sum (fun face _ => hw face))

end QEC.Coding.BDL26RXLocalReplacement

import QEC.Coding.FiniteAlternatingConstruction.RXQBlockTransport

/-!
# Actual incident-X stars and their boundary geometry

Project-derived internal mathematics for BDL26 `paper.tex:3136–3185,3455–3481`.
The X and Q correction regions below are the original decoder's regions.
The degree-zero chart and its connecting boundary come from the actual RX
successor, not a supplied coordinate identification or support certificate.
-/
noncomputable section
namespace QEC.Coding.BDL26RXXStarTransport

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

abbrev XCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.X
abbrev QCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Q
abbrev ZCoord (S : OddScale) {depth : Nat} (i : StepIndex depth) :=
  (state S i.val).presentation.Z
abbrev LocalPotential (S : OddScale) {depth : Nat} (i : StepIndex depth)
    (x : XCoord S i) := Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)

variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)

def incidentQ (x : XCoord S i) : Finset (QCoord S i) :=
  Finset.univ.filter fun q => (state S i.val).presentation.xq x q=true

def starQ (x : XCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (incidentQ S depth i x).biUnion ((rxLq S depth i h).correctionRegion)

def star1 (x : XCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (rxLx S depth i h).correctionRegion x ∪ starQ S depth i h x

def incidentZ (x : XCoord S i) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => ∃ q ∈ incidentQ S depth i x,
    (state S i.val).presentation.qz q z=true

/-- The actual degree-zero X cylinder, with every vertex and both copy tags. -/
def degreeZeroBlock (x : XCoord S i) : Finset (FamilyX S depth i.succ) :=
  Finset.univ.image fun v => rxDegreeZeroEquiv S depth i h ⟨x,v⟩

@[simp] theorem mem_incidentQ (x : XCoord S i) (q : QCoord S i) :
    q ∈ incidentQ S depth i x ↔ (state S i.val).presentation.xq x q=true := by
  simp [incidentQ]

@[simp] theorem mem_starQ (x : XCoord S i) (p : FamilyQ S depth i.succ) :
    p ∈ starQ S depth i h x ↔ ∃ q ∈ incidentQ S depth i x,
      p ∈ (rxLq S depth i h).correctionRegion q := by
  simp [starQ]

theorem word_add_self {ι : Type*} (w : Word BDL26Field ι) : w+w=0 := by
  funext p
  exact CharTwo.add_self_eq_zero (w p)

theorem eq_of_word_add_zero {ι : Type*} (u v : Word BDL26Field ι)
    (hh : u+v=0) : u=v := by
  have he := congrArg (fun t => u+t) hh
  rw [← add_assoc, word_add_self, zero_add, add_zero] at he
  exact he.symm

theorem zero_off_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Word BDL26Field ι) (Y : Finset ι) (hw : hammingSupport w ⊆ Y)
    (p : ι) (hp : p ∉ Y) : w p=0 := by
  by_contra hn
  exact hp (hw (by simpa [hammingSupport] using hn))

theorem support_of_zero_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Word BDL26Field ι) (Y : Finset ι)
    (hw : ∀ p, p ∉ Y → w p=0) : hammingSupport w ⊆ Y := by
  intro p hp
  by_contra hout
  exact (show w p ≠ 0 by simpa [hammingSupport] using hp) (hw p hout)

private theorem extend_restrict_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : Finset ι) (w : Word BDL26Field ι) (hw : hammingSupport w ⊆ Y) :
    extendWordLinear Y (restrictWordLinear Y w)=w := by
  funext p
  change extendLocalSignal Y (restrictWordLinear Y w) p=w p
  by_cases hp : p ∈ Y
  · rw [extendLocalSignal,dif_pos hp]
    rfl
  · rw [extendLocalSignal,dif_neg hp,zero_off_support w Y hw p hp]

theorem selected_rx :
    (indexedDecoderData S depth).selectedMap i = (indexedDecoderData S depth).rxMap i := by
  rw [selectedMap_eq]
  rfl

theorem actual_contract : (rxData S depth i h).contract = rxContract S depth i h := rfl

theorem actual_coboundary1 (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary1 j =
      (indexedFamily S depth).coboundary1 j := rfl

/-- An X block cannot meet any actual Q error block. -/
theorem x_q_disjoint (x : XCoord S i) (q : QCoord S i) :
    Disjoint ((rxLx S depth i h).correctionRegion x)
      ((rxLq S depth i h).correctionRegion q) := by
  apply Finset.disjoint_left.mpr
  intro p hpx hpq
  apply (Finset.disjoint_left.mp (rxData S depth i h).correction_sectors_disjoint)
  · exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hpx⟩
  · rw [(rxData S depth i h).qCorrectionSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,hpq⟩

theorem error_other_x_zero (x y : XCoord S i) (hy : y≠x)
    (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion y) e=0 := by
  funext p
  apply zero_off_support e _ he p.val
  intro hp
  exact (Finset.disjoint_left.mp
    ((rxData S depth i h).cx_correction_regions_pairwise_disjoint y x hy)) p.property hp

theorem error_q_zero (x : XCoord S i) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x)
    (q : QCoord S i) : restrictWordLinear ((rxLq S depth i h).correctionRegion q) e=0 := by
  funext p
  exact zero_off_support e _ he p.val
    (fun hp => (Finset.disjoint_left.mp (x_q_disjoint S depth i h x q)) hp p.property)

/-- Auxiliary map2 zeroes are proved for the actual selected map. -/
theorem map2_x_zero (tau : (indexedFamily S depth).Cochain2 i.castSucc)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
      (((indexedDecoderData S depth).selectedMap i).map2 tau)=0 := by
  rw [selected_rx]
  funext p
  apply (rxData S depth i h).induced.map2_auxiliary_zero
  rw [← (rxData S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (rxData S depth i h).sectors_pairwise_disjoint.2.1) _ hz
  rw [(rxData S depth i h).xSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,p.property⟩

theorem map2_q_zero (tau : (indexedFamily S depth).Cochain2 i.castSucc)
    (q : QCoord S i) : restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      (((indexedDecoderData S depth).selectedMap i).map2 tau)=0 := by
  rw [selected_rx]
  funext p
  apply (rxData S depth i h).induced.map2_auxiliary_zero
  rw [← (rxData S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (rxData S depth i h).sectors_pairwise_disjoint.2.2) _ hz
  rw [(rxData S depth i h).qSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ _,p.property⟩

/-- A nonincident Q has no outgoing X-flow contribution. This uses the original
directed graph, and does not apply the staged Q formula to a nonzero X error. -/
theorem x_flow_nonincident_q (x : XCoord S i) (q : QCoord S i)
    (hxq : q ∉ incidentQ S depth i x)
    (f : Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).correctionRegion x))) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      ((rxContract S depth i h).support_decomposition.cxFlow x f)=0 := by
  funext p
  by_contra hn
  have hd := (rxData S depth i h).cxFlow_radius_one x f p.val hn
  rw [((rxData S depth i h).topCenter_q_iff q p.val).mp p.property] at hd
  rcases (distance_le_one_iff _ _ _).mp hd with he | he
  · cases he
  · rw [rxData_graph_edge S depth i h, tannerLevel_edge] at he
    apply hxq
    apply (mem_incidentQ S depth i x q).mpr
    simpa [vertexEquiv,tannerDirected] using he

theorem x_error_nonincident_q_syndrome (x : XCoord S i) (q : QCoord S i)
    (hq : q ∉ incidentQ S depth i x) (e : Upper S depth i)
    (he : hammingSupport e ⊆ (rxLx S depth i h).correctionRegion x) :
    restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
      ((indexedFamily S depth).coboundary1 i.succ e)=0 := by
  change restrictWordLinear ((rxLq S depth i h).syndromeRegion q)
    ((indexedDecoderData S depth).family.coboundary1 i.succ e)=0
  have hext := extend_restrict_of_support ((rxLx S depth i h).correctionRegion x) e he
  rw [← hext, (rxContract S depth i h).support_decomposition.cxDelta1_decomposition, map_add,
    x_flow_nonincident_q S depth i h x q hq, add_zero]
  apply region_restrict_extend_disjoint
  apply Finset.disjoint_left.mpr
  intro p hpx hpq
  have hcx := ((rxData S depth i h).topCenter_x_iff x p).mp hpx
  have hcq := ((rxData S depth i h).topCenter_q_iff q p).mp hpq
  rw [hcx] at hcq
  cases hcq

/-- Literal degree-zero support, obtained from the actual total coordinate chart. -/
theorem lift_supported (x : XCoord S i) (s : LocalPotential S i x) :
    hammingSupport ((rxContract S depth i h).support_decomposition.cxLift0 x s) ⊆
      degreeZeroBlock S depth i h x := by
  apply support_of_zero_off
  intro p hp
  obtain ⟨⟨y,v⟩,rfl⟩ := (rxDegreeZeroEquiv S depth i h).surjective p
  have hy : y≠x := by
    intro he
    subst y
    exact hp (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  exact rxXLift_other S depth i h x y hy s v

/-- The full boundary of an X-local potential may spill into incident Q blocks. -/
theorem lift_boundary_supported (x : XCoord S i) (s : LocalPotential S i x) :
    hammingSupport ((indexedFamily S depth).coboundary0 i.succ
      ((rxContract S depth i h).support_decomposition.cxLift0 x s)) ⊆ star1 S depth i h x := by
  apply support_of_zero_off
  intro p hp
  have hc := (rxData S depth i h).correction_sectors_cover
  have hpall : p ∈ correctionRegionUnion (rxLx S depth i h) ∪
      (rxData S depth i h).qCorrectionSector := by rw [hc]; exact Finset.mem_univ _
  rcases Finset.mem_union.mp hpall with hpx | hpq
  · obtain ⟨y,_,hy⟩ := Finset.mem_biUnion.mp hpx
    have hne : y≠x := by
      intro he
      subst y
      exact hp (Finset.mem_union_left _ hy)
    exact congrFun (rxXLift_boundary_other_x S depth i h x y hne s) ⟨p,hy⟩
  · rw [(rxData S depth i h).qCorrectionSector_eq_regions] at hpq
    obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hpq
    have hn : q ∉ incidentQ S depth i x := by
      intro hn
      exact hp (Finset.mem_union_right _ ((mem_starQ S depth i h x p).mpr ⟨q,hn,hq⟩))
    exact congrFun (rxXLift_boundary_nonincident_q S depth i h x q
      (by simpa only [mem_incidentQ] using hn) s) ⟨p,hq⟩

/-- An admissible, actual boundary vertex at every X owner, including the first edge. -/
def boundaryVertex (x : XCoord S i) :
    SubdivisionBoundaryVertex (state S i.val).presentation x S :=
  subdivisionOriginalBoundaryVertex (state S i.val).presentation x S
    ((state S i.val).admissible.toTannerSquareAdmissible.xBoundaryRoot x)

/-- Copy zero is selected only for this explicit witness; the gradient sees both copies. -/
def boundarySingleton (x : XCoord S i) : LocalPotential S i x :=
  Pi.single (0,(boundaryVertex S depth i x).val) 1

theorem boundarySingleton_vertical (x : XCoord S i) :
    wordLinearMapTranspose (doubleCylinderBoundary1 (state S i.val).presentation x S)
      (boundarySingleton S depth i x) (Sum.inr (boundaryVertex S depth i x)) = 1 := by
  rw [doubleCylinderBoundary1,wordLinearMapTranspose_toLin'_apply]
  rw [Fintype.sum_eq_single (0,(boundaryVertex S depth i x).val)]
  · simp [boundarySingleton,doubleCylinder_vertical_edge_boundary]
  · intro v hv
    have hz : boundarySingleton S depth i x v=0 := by
      simp [boundarySingleton,Pi.single_apply,hv]
    rw [hz,zero_mul]

def boundaryGradient (x : XCoord S i) :
    Word BDL26Field (LocalRegionIndex ((rxLx S depth i h).correctionRegion x)) :=
  (rxContract S depth i h).rx_local_complexes.cxDelta0 x (boundarySingleton S depth i x)

theorem boundaryGradient_nonzero (x : XCoord S i) : boundaryGradient S depth i h x ≠ 0 := by
  intro hz
  have hr := (rxCxDelta0_eq_zero_iff_raw S depth i h x (boundarySingleton S depth i x)).mp hz
  have he := congrFun hr (Sum.inr (boundaryVertex S depth i x))
  rw [boundarySingleton_vertical] at he
  exact one_ne_zero he

theorem boundaryGradient_kernel (x : XCoord S i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta1 x
      (boundaryGradient S depth i h x)=0 := by
  have hm : boundaryGradient S depth i h x ∈
      LinearMap.range ((rxContract S depth i h).rx_local_complexes.cxDelta0 x) :=
    ⟨boundarySingleton S depth i x,rfl⟩
  rw [← (rxContract S depth i h).rx_local_cohomology.cx_h1_ker_eq_range x] at hm
  exact hm

/-- Extend only the local gradient ERROR, not its global potential boundary. -/
def gradientError (x : XCoord S i) : Upper S depth i :=
  extendWordLinear ((rxLx S depth i h).correctionRegion x) (boundaryGradient S depth i h x)

theorem gradientError_restriction (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x) (gradientError S depth i h x) =
      boundaryGradient S depth i h x := region_restrict_extend _ _

theorem gradientError_supported (x : XCoord S i) :
    hammingSupport (gradientError S depth i h x) ⊆ (rxLx S depth i h).correctionRegion x := by
  apply support_of_zero_off
  intro p hp
  exact dif_neg hp

theorem gradientError_nonzero (x : XCoord S i) : gradientError S depth i h x ≠ 0 := by
  intro hz
  have he := gradientError_restriction S depth i h x
  rw [hz,map_zero] at he
  exact boundaryGradient_nonzero S depth i h x he.symm

end QEC.Coding.BDL26RXXStarTransport

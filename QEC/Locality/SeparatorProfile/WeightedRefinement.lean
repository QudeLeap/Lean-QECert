import QEC.Locality.SeparatorProfile.StoppedRecursion
import QEC.Locality.SeparatorProfile.Weighted
/-!
# Weighted local refinement for profile-separator edge divisions

This module turns a marked separator spine into an exact three-way edge split.
The split follows oriented-edge ownership rather than a false vertex
partition: each edge is assigned to the first light side it touches, and the
remaining edges belong to the third side plus the accumulated separator.
-/

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private def touches (side : Finset ι) (edge : ι × ι) : Prop :=
  edge.1 ∈ side ∨ edge.2 ∈ side

/-- Edges touching the exposed light side. -/
private noncomputable def weightedSpineFirstEdges
    (edges : Finset (ι × ι)) (first : Finset ι) : Finset (ι × ι) :=
  by
    classical
    exact edges.filter (touches first)

/-- Edges not in the first class and touching the first terminal side. -/
private noncomputable def weightedSpineSecondEdges
    (edges : Finset (ι × ι)) (first second : Finset ι) : Finset (ι × ι) :=
  by
    classical
    exact edges.filter fun edge => ¬ touches first edge ∧ touches second edge

/-- The complementary third edge class. -/
private noncomputable def weightedSpineThirdEdges
    (edges : Finset (ι × ι)) (first second : Finset ι) : Finset (ι × ι) :=
  by
    classical
    exact edges.filter fun edge => ¬ touches first edge ∧ ¬ touches second edge

private theorem weightedSpineFirstEdges_reverse
    (edges : Finset (ι × ι)) (first : Finset ι)
    (hsymmetric : ReverseSymmetricEdgeSet edges) (x y : ι) :
    (x, y) ∈ weightedSpineFirstEdges edges first ↔
      (y, x) ∈ weightedSpineFirstEdges edges first := by
  simp only [weightedSpineFirstEdges, Finset.mem_filter, touches]
  rw [hsymmetric]
  tauto

private theorem weightedSpineSecondEdges_reverse
    (edges : Finset (ι × ι)) (first second : Finset ι)
    (hsymmetric : ReverseSymmetricEdgeSet edges) (x y : ι) :
    (x, y) ∈ weightedSpineSecondEdges edges first second ↔
      (y, x) ∈ weightedSpineSecondEdges edges first second := by
  classical
  unfold weightedSpineSecondEdges
  erw [Finset.mem_filter, Finset.mem_filter]
  simp only [touches]
  rw [hsymmetric]
  tauto

private theorem weightedSpineThirdEdges_reverse
    (edges : Finset (ι × ι)) (first second : Finset ι)
    (hsymmetric : ReverseSymmetricEdgeSet edges) (x y : ι) :
    (x, y) ∈ weightedSpineThirdEdges edges first second ↔
      (y, x) ∈ weightedSpineThirdEdges edges first second := by
  classical
  unfold weightedSpineThirdEdges
  erw [Finset.mem_filter, Finset.mem_filter]
  simp only [touches]
  rw [hsymmetric]
  tauto

private theorem weightedSpineEdges_exact_cover
    (edges : Finset (ι × ι)) (first second : Finset ι) :
    weightedSpineFirstEdges edges first ∪
        (weightedSpineSecondEdges edges first second ∪
          weightedSpineThirdEdges edges first second) = edges := by
  ext edge
  simp only [weightedSpineFirstEdges, weightedSpineSecondEdges, weightedSpineThirdEdges,
    Finset.mem_union, Finset.mem_filter]
  simp only [touches]
  tauto

private theorem weightedSpineEdges_pairwiseDisjoint
    (edges : Finset (ι × ι)) (first second : Finset ι) :
    Disjoint (weightedSpineFirstEdges edges first)
        (weightedSpineSecondEdges edges first second) ∧
      Disjoint (weightedSpineFirstEdges edges first)
        (weightedSpineThirdEdges edges first second) ∧
      Disjoint (weightedSpineSecondEdges edges first second)
        (weightedSpineThirdEdges edges first second) := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro edge hfirst hsecond
    exact (Finset.mem_filter.mp hsecond).2.1 (Finset.mem_filter.mp hfirst).2
  constructor
  · apply Finset.disjoint_left.mpr
    intro edge hfirst hthird
    exact (Finset.mem_filter.mp hthird).2.1 (Finset.mem_filter.mp hfirst).2
  · apply Finset.disjoint_left.mpr
    intro edge hsecond hthird
    exact (Finset.mem_filter.mp hthird).2.2 (Finset.mem_filter.mp hsecond).2.2

private theorem edgeRestricted_adjacent_of_mem
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)}
    (hsubset : edges ⊆ directedEdgeFinset G) {x y : ι}
    (hxy : (x, y) ∈ edges) : (edgeRestrictedGraph G edges).adjacent x y := by
  exact ⟨(mem_directedEdgeFinset_iff G x y).1 (hsubset hxy), Or.inl hxy⟩

private theorem endpoint_in_threeSide_or_separator
    {H : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine H marked vertices) {x : ι} (hx : x ∈ vertices) :
    x ∈ spine.exposedSide ∨ x ∈ spine.stopSides.1 ∨
      x ∈ spine.stopSides.2 ∨ x ∈ markedSpineSeparatorUnion spine := by
  have hx' : x ∈ spine.exposedSide ∪ spine.stopSides.1 ∪ spine.stopSides.2 ∪
      markedSpineSeparatorUnion spine := by
    rw [spine.exposed_stopSides_separatorUnion]
    exact hx
  rcases Finset.mem_union.mp hx' with hxthree | hxseparator
  · rcases Finset.mem_union.mp hxthree with hxtwo | hxthird
    · rcases Finset.mem_union.mp hxtwo with hxfirst | hxsecond
      · exact Or.inl hxfirst
      · exact Or.inr (Or.inl hxsecond)
    · exact Or.inr (Or.inr (Or.inl hxthird))
  · exact Or.inr (Or.inr (Or.inr hxseparator))

private theorem weightedSpineFirstEdges_incident_subset
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices) :
    edgeIncidentVertices (weightedSpineFirstEdges edges spine.exposedSide) ⊆
      spine.exposedSide ∪ markedSpineSeparatorUnion spine := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hxendpoint⟩
  have hedgeParent := (Finset.mem_filter.mp hedge).1
  have htouch := (Finset.mem_filter.mp hedge).2
  have hadj := edgeRestricted_adjacent_of_mem G hsubset hedgeParent
  have hxvertices : x ∈ vertices := by
    exact hincident ((mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hedgeParent, hxendpoint⟩)
  rcases endpoint_in_threeSide_or_separator spine hxvertices with
    hxfirst | hxsecond | hxthird | hxseparator
  · exact Finset.mem_union_left _ hxfirst
  · rcases hxendpoint with rfl | rfl
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.1) hxfirst hxsecond)
      · exact False.elim ((spine.threeSides_noEdge.1 hyfirst hxsecond)
            ((edgeRestrictedGraph G edges).symmetric hadj))
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((spine.threeSides_noEdge.1 hxfirst hxsecond) hadj)
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.1) hyfirst hxsecond)
  · rcases hxendpoint with rfl | rfl
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.2) hxfirst hxthird)
      · exact False.elim ((spine.threeSides_noEdge.2.1 hyfirst hxthird)
            ((edgeRestrictedGraph G edges).symmetric hadj))
    · rcases htouch with hxfirst | hyfirst
      · exact False.elim ((spine.threeSides_noEdge.2.1 hxfirst hxthird) hadj)
      · exact False.elim ((Finset.disjoint_left.mp
            spine.exposedSide_disjoint_stopSides.2) hyfirst hxthird)
  · exact Finset.mem_union_right _ hxseparator

private theorem weightedSpineSecondEdges_incident_subset
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices) :
    edgeIncidentVertices
        (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1) ⊆
      spine.stopSides.1 ∪ markedSpineSeparatorUnion spine := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hxendpoint⟩
  have hedgeData := (Finset.mem_filter.mp hedge).2
  have hedgeParent := (Finset.mem_filter.mp hedge).1
  have hadj := edgeRestricted_adjacent_of_mem G hsubset hedgeParent
  have hxvertices : x ∈ vertices := by
    exact hincident ((mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hedgeParent, hxendpoint⟩)
  rcases endpoint_in_threeSide_or_separator spine hxvertices with
    hxfirst | hxsecond | hxthird | hxseparator
  · rcases hxendpoint with rfl | rfl
    · exact False.elim (hedgeData.1 (Or.inl hxfirst))
    · exact False.elim (hedgeData.1 (Or.inr hxfirst))
  · exact Finset.mem_union_left _ hxsecond
  · rcases hxendpoint with rfl | rfl
    · rcases hedgeData.2 with hxsecond | hysecond
      · exact False.elim ((Finset.disjoint_left.mp spine.stopSides_disjoint)
            hxsecond hxthird)
      · exact False.elim ((spine.threeSides_noEdge.2.2 hysecond hxthird)
            ((edgeRestrictedGraph G edges).symmetric hadj))
    · rcases hedgeData.2 with hxsecond | hysecond
      · exact False.elim ((spine.threeSides_noEdge.2.2 hxsecond hxthird) hadj)
      · exact False.elim ((Finset.disjoint_left.mp spine.stopSides_disjoint)
            hysecond hxthird)
  · exact Finset.mem_union_right _ hxseparator

private theorem weightedSpineThirdEdges_incident_subset
    (G : ConnectivityGraph ι) {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices) :
    edgeIncidentVertices
        (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1) ⊆
      spine.stopSides.2 ∪ markedSpineSeparatorUnion spine := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hxendpoint⟩
  have hedgeData := (Finset.mem_filter.mp hedge).2
  have hedgeParent := (Finset.mem_filter.mp hedge).1
  have hxvertices : x ∈ vertices := by
    exact hincident ((mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hedgeParent, hxendpoint⟩)
  rcases endpoint_in_threeSide_or_separator spine hxvertices with
    hxfirst | hxsecond | hxthird | hxseparator
  · rcases hxendpoint with rfl | rfl
    · exact False.elim (hedgeData.1 (Or.inl hxfirst))
    · exact False.elim (hedgeData.1 (Or.inr hxfirst))
  · rcases hxendpoint with rfl | rfl
    · exact False.elim (hedgeData.2 (Or.inl hxsecond))
    · exact False.elim (hedgeData.2 (Or.inr hxsecond))
  · exact Finset.mem_union_left _ hxthird
  · exact Finset.mem_union_right _ hxseparator

/-- Carrier retained by one light side of a weighted spine split. -/
private noncomputable def weightedSpineChildCarrier
    (side separatorUnion : Finset ι) : Finset ι :=
  side ∪ separatorUnion

/-- Inherited boundary of one light side after a weighted spine split. -/
private noncomputable def weightedSpineChildBoundary
    (boundary side separatorUnion : Finset ι) : Finset ι :=
  separatorUnion ∪ (boundary ∩ weightedSpineChildCarrier side separatorUnion)

private theorem weightedSpineChildBoundary_subset_carrier
    (boundary side separatorUnion : Finset ι) :
    weightedSpineChildBoundary boundary side separatorUnion ⊆
      weightedSpineChildCarrier side separatorUnion := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxseparator | hxboundary
  · exact Finset.mem_union_right _ hxseparator
  · exact (Finset.mem_inter.mp hxboundary).2

private theorem weightedSpineChildBoundary_card_le
    (boundary side separatorUnion : Finset ι) :
    (weightedSpineChildBoundary boundary side separatorUnion).card ≤
      separatorUnion.card + (boundary ∩ side).card := by
  have hsubset : weightedSpineChildBoundary boundary side separatorUnion ⊆
      separatorUnion ∪ (boundary ∩ side) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxseparator | hxboundary
    · exact Finset.mem_union_left _ hxseparator
    · rcases Finset.mem_inter.mp hxboundary with ⟨hxmarked, hxcarrier⟩
      rcases Finset.mem_union.mp hxcarrier with hxside | hxseparator
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxmarked, hxside⟩)
      · exact Finset.mem_union_left _ hxseparator
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

private theorem weightedSpineChildBoundary_card_lt
    (boundary side separatorUnion : Finset ι) {spineBudget : Nat}
    (hside : 3 * (boundary ∩ side).card ≤ 2 * boundary.card)
    (hseparator : separatorUnion.card ≤ spineBudget)
    (hlarge : 6 * spineBudget < boundary.card) :
    (weightedSpineChildBoundary boundary side separatorUnion).card < boundary.card := by
  have hcard := weightedSpineChildBoundary_card_le boundary side separatorUnion
  omega

private theorem MarkedSeparatorSpine.separatorUnion_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    markedSpineSeparatorUnion spine ⊆ vertices := by
  intro x hx
  rw [← spine.exposed_stopSides_separatorUnion]
  exact Finset.mem_union_right _ hx

private theorem MarkedSeparatorSpine.stopSides_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.stopSides.1 ⊆ vertices ∧ spine.stopSides.2 ⊆ vertices := by
  have hsides := spine.stopSides_subset_terminalCarrier
  exact ⟨hsides.1.trans spine.terminalCarrier_subset,
    hsides.2.trans spine.terminalCarrier_subset⟩

private theorem MarkedSeparatorSpine.childCarriers_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine) ⊆ vertices ∧
      weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine) ⊆ vertices ∧
      weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine) ⊆ vertices := by
  exact ⟨Finset.union_subset spine.exposedSide_subset spine.separatorUnion_subset,
    Finset.union_subset spine.stopSides_subset.1 spine.separatorUnion_subset,
    Finset.union_subset spine.stopSides_subset.2 spine.separatorUnion_subset⟩

/--
Boundary-only refinement of one size-bounded edge region.  Every branch is an
explicit weighted-spine three-way edge allocation and recursion descends on
the inherited boundary cardinality.
-/
inductive WeightedBoundaryEdgeRecursion
    (G : ConnectivityGraph ι) (r spineBudget : Nat) :
    Finset (ι × ι) → Finset ι → Finset ι → Type u
  | leaf {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hboundary : boundary ⊆ vertices)
      (hcard : vertices.card ≤ r)
      (hboundaryCard : boundary.card ≤ 6 * spineBudget) :
      WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary
  | split {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hboundary : boundary ⊆ vertices)
      (hcard : vertices.card ≤ r)
      (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
      (hseparatorCard : (markedSpineSeparatorUnion spine).card ≤ spineBudget)
      (hboundaryLarge : 6 * spineBudget < boundary.card)
      (firstTree : WeightedBoundaryEdgeRecursion G r spineBudget
        (weightedSpineFirstEdges edges spine.exposedSide)
        (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
        (weightedSpineChildBoundary boundary spine.exposedSide
          (markedSpineSeparatorUnion spine)))
      (secondTree : WeightedBoundaryEdgeRecursion G r spineBudget
        (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
        (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
        (weightedSpineChildBoundary boundary spine.stopSides.1
          (markedSpineSeparatorUnion spine)))
      (thirdTree : WeightedBoundaryEdgeRecursion G r spineBudget
        (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
        (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
        (weightedSpineChildBoundary boundary spine.stopSides.2
          (markedSpineSeparatorUnion spine))) :
      WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary

/-- Construct the weighted local refinement by strict inherited-boundary descent. -/
noncomputable def buildWeightedBoundaryEdgeRecursion
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (r : Nat) (edges : Finset (ι × ι)) (vertices boundary : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hboundary : boundary ⊆ vertices)
    (hcard : vertices.card ≤ r) :
    WeightedBoundaryEdgeRecursion G r (weightedSpineSeparatorBudget beta exponent r)
      edges vertices boundary := by
  classical
  let spineBudget := weightedSpineSeparatorBudget beta exponent r
  by_cases hleaf : boundary.card ≤ 6 * spineBudget
  · exact .leaf hsubset hsymmetric hincident hboundary hcard hleaf
  · let H := edgeRestrictedGraph G edges
    let spine := buildMarkedSeparatorSpine H boundary vertices
    let separatorUnion := markedSpineSeparatorUnion spine
    let first := spine.exposedSide
    let second := spine.stopSides.1
    let third := spine.stopSides.2
    have hboundaryLarge : 6 * spineBudget < boundary.card := Nat.lt_of_not_ge hleaf
    have hvertices : 1 ≤ vertices.card := by
      have hboundaryPositive : 0 < boundary.card := by omega
      exact hboundaryPositive.trans_le (Finset.card_le_card hboundary)
    have hprofileH : AssumedBGKLMeasuredProfilePowerUpperBound H beta exponent :=
      hProfile.edgeRestricted G beta exponent edges
    have hseparator : separatorUnion.card ≤ spineBudget := by
      exact spine.separatorUnion_card_le_weightedSpineSeparatorBudget
        hprofileH hvertices hcard
    have hfirstLight : 3 * (boundary ∩ first).card ≤ 2 * boundary.card :=
      spine.exposedSide_marked_light
    have hstopLight := spine.stopSides_marked_light
    have hsecondLight : 3 * (boundary ∩ second).card ≤ 2 * boundary.card :=
      hstopLight.1
    have hthirdLight : 3 * (boundary ∩ third).card ≤ 2 * boundary.card :=
      hstopLight.2
    have hfirstStrict :
        (weightedSpineChildBoundary boundary first separatorUnion).card < boundary.card :=
      weightedSpineChildBoundary_card_lt boundary first separatorUnion
        hfirstLight hseparator hboundaryLarge
    have hsecondStrict :
        (weightedSpineChildBoundary boundary second separatorUnion).card < boundary.card :=
      weightedSpineChildBoundary_card_lt boundary second separatorUnion
        hsecondLight hseparator hboundaryLarge
    have hthirdStrict :
        (weightedSpineChildBoundary boundary third separatorUnion).card < boundary.card :=
      weightedSpineChildBoundary_card_lt boundary third separatorUnion
        hthirdLight hseparator hboundaryLarge
    have hcarriers := spine.childCarriers_subset
    refine .split hsubset hsymmetric hincident hboundary hcard spine hseparator hboundaryLarge
      ?_ ?_ ?_
    · exact buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
        (weightedSpineFirstEdges edges first)
        (weightedSpineChildCarrier first separatorUnion)
        (weightedSpineChildBoundary boundary first separatorUnion)
        ((Finset.filter_subset _ _).trans hsubset)
        (weightedSpineFirstEdges_reverse edges first hsymmetric)
        (weightedSpineFirstEdges_incident_subset G hsubset hincident spine)
        (weightedSpineChildBoundary_subset_carrier boundary first separatorUnion)
        ((Finset.card_le_card hcarriers.1).trans hcard)
    · exact buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
        (weightedSpineSecondEdges edges first second)
        (weightedSpineChildCarrier second separatorUnion)
        (weightedSpineChildBoundary boundary second separatorUnion)
        ((Finset.filter_subset _ _).trans hsubset)
        (weightedSpineSecondEdges_reverse edges first second hsymmetric)
        (weightedSpineSecondEdges_incident_subset G hsubset hincident spine)
        (weightedSpineChildBoundary_subset_carrier boundary second separatorUnion)
        ((Finset.card_le_card hcarriers.2.1).trans hcard)
    · exact buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
        (weightedSpineThirdEdges edges first second)
        (weightedSpineChildCarrier third separatorUnion)
        (weightedSpineChildBoundary boundary third separatorUnion)
        ((Finset.filter_subset _ _).trans hsubset)
        (weightedSpineThirdEdges_reverse edges first second hsymmetric)
        (weightedSpineThirdEdges_incident_subset G hincident spine)
        (weightedSpineChildBoundary_subset_carrier boundary third separatorUnion)
        ((Finset.card_le_card hcarriers.2.2).trans hcard)
termination_by boundary.card
decreasing_by
  · exact hfirstStrict
  · exact hsecondStrict
  · exact hthirdStrict

/-- Terminal owner indices of a weighted three-way boundary refinement. -/
def WeightedBoundaryEdgeRecursion.edgeOwnerType
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary → Type
  | .leaf _ _ _ _ _ _ => Unit
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree =>
      Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType)

noncomputable instance WeightedBoundaryEdgeRecursion.edgeOwnerFintype
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    Fintype tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ _ _ =>
      change Fintype Unit
      infer_instance
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      change Fintype
        (Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType))
      letI := ihFirst
      letI := ihSecond
      letI := ihThird
      infer_instance

noncomputable instance WeightedBoundaryEdgeRecursion.edgeOwnerDecidableEq
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    DecidableEq tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ _ _ =>
      change DecidableEq Unit
      infer_instance
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      change DecidableEq
        (Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType))
      letI := ihFirst
      letI := ihSecond
      letI := ihThird
      infer_instance

/-- The terminal edge region allocated to one weighted-refinement owner. -/
noncomputable def WeightedBoundaryEdgeRecursion.edgeRegion
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) →
      tree.edgeOwnerType → Finset (ι × ι)
  | .leaf (edges := edges) _ _ _ _ _ _, _ => edges
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree, owner =>
      match owner with
      | Sum.inl owner => firstTree.edgeRegion owner
      | Sum.inr (Sum.inl owner) => secondTree.edgeRegion owner
      | Sum.inr (Sum.inr owner) => thirdTree.edgeRegion owner

/-- Only nonempty terminal edge regions are active. -/
noncomputable def WeightedBoundaryEdgeRecursion.edgeActive
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    Finset tree.edgeOwnerType := by
  classical
  exact Finset.univ.filter fun owner => (tree.edgeRegion owner).Nonempty

/-- Boundary resource retained at one terminal weighted-refinement owner. -/
noncomputable def WeightedBoundaryEdgeRecursion.ownerBoundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) →
      tree.edgeOwnerType → Finset ι
  | .leaf (boundary := boundary) _ _ _ _ _ _, _ => boundary
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree, owner =>
      match owner with
      | Sum.inl owner => firstTree.ownerBoundary owner
      | Sum.inr (Sum.inl owner) => secondTree.ownerBoundary owner
      | Sum.inr (Sum.inr owner) => thirdTree.ownerBoundary owner

theorem WeightedBoundaryEdgeRecursion.edgeRegion_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) : tree.edgeRegion owner ⊆ edges := by
  classical
  induction tree with
  | leaf _ _ _ _ _ _ => simpa [edgeRegion]
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact (ihFirst owner).trans (Finset.filter_subset _ _)
      | inr owner =>
          cases owner with
          | inl owner => exact (ihSecond owner).trans (Finset.filter_subset _ _)
          | inr owner => exact (ihThird owner).trans (Finset.filter_subset _ _)

theorem WeightedBoundaryEdgeRecursion.edgeRegion_reverse
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) (x y : ι) :
    (x, y) ∈ tree.edgeRegion owner ↔ (y, x) ∈ tree.edgeRegion owner := by
  induction tree with
  | leaf _ hsymmetric _ _ _ _ => exact hsymmetric x y
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact ihFirst owner
      | inr owner =>
          cases owner with
          | inl owner => exact ihSecond owner
          | inr owner => exact ihThird owner

theorem WeightedBoundaryEdgeRecursion.edgeRegion_incident_card_le
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)).card ≤ r := by
  induction tree with
  | leaf _ _ hincident _ hcard _ =>
      exact (Finset.card_le_card hincident).trans hcard
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact ihFirst owner
      | inr owner =>
          cases owner with
          | inl owner => exact ihSecond owner
          | inr owner => exact ihThird owner

theorem WeightedBoundaryEdgeRecursion.ownerBoundary_card_le
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    (tree.ownerBoundary owner).card ≤ 6 * spineBudget := by
  induction tree with
  | leaf _ _ _ _ _ hboundaryCard => exact hboundaryCard
  | split _ _ _ _ _ spine _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner => exact ihFirst owner
      | inr owner =>
          cases owner with
          | inl owner => exact ihSecond owner
          | inr owner => exact ihThird owner

theorem WeightedBoundaryEdgeRecursion.existsUnique_edgeOwner
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.edgeOwnerType, edge ∈ tree.edgeRegion owner := by
  classical
  induction tree generalizing edge with
  | leaf _ _ _ _ _ _ =>
      refine ⟨Unit.unit, by simpa [edgeRegion] using hedge, ?_⟩
      intro owner _
      simpa [edgeOwnerType] using (Subsingleton.elim (α := Unit) owner Unit.unit)
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge
      firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      let firstEdges := weightedSpineFirstEdges edges spine.exposedSide
      let secondEdges := weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1
      let thirdEdges := weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1
      by_cases hfirst : edge ∈ firstEdges
      · rcases ihFirst edge hfirst with ⟨owner, howner, hunique⟩
        refine ⟨Sum.inl owner, by simpa [edgeRegion] using howner, ?_⟩
        intro candidate hcandidate
        cases candidate with
        | inl candidate =>
            exact congrArg Sum.inl (hunique candidate (by simpa [edgeRegion] using hcandidate))
        | inr candidate =>
            cases candidate with
            | inl candidate =>
                have hsecond : edge ∈ secondEdges :=
                  secondTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                exact False.elim
                  ((Finset.disjoint_left.mp
                    (weightedSpineEdges_pairwiseDisjoint edges spine.exposedSide
                      spine.stopSides.1).1) hfirst hsecond)
            | inr candidate =>
                have hthird : edge ∈ thirdEdges :=
                  thirdTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                exact False.elim
                  ((Finset.disjoint_left.mp
                    (weightedSpineEdges_pairwiseDisjoint edges spine.exposedSide
                      spine.stopSides.1).2.1) hfirst hthird)
      · by_cases hsecond : edge ∈ secondEdges
        · rcases ihSecond edge hsecond with ⟨owner, howner, hunique⟩
          refine ⟨Sum.inr (Sum.inl owner), by simpa [edgeRegion] using howner, ?_⟩
          intro candidate hcandidate
          cases candidate with
          | inl candidate =>
              have hfirst' : edge ∈ firstEdges :=
                firstTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
              exact False.elim (hfirst hfirst')
          | inr candidate =>
              cases candidate with
              | inl candidate =>
                  exact congrArg (fun x => Sum.inr (Sum.inl x))
                    (hunique candidate (by simpa [edgeRegion] using hcandidate))
              | inr candidate =>
                  have hthird : edge ∈ thirdEdges :=
                    thirdTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                  exact False.elim
                    ((Finset.disjoint_left.mp
                      (weightedSpineEdges_pairwiseDisjoint edges spine.exposedSide
                        spine.stopSides.1).2.2) hsecond hthird)
        · have hthird : edge ∈ thirdEdges := by
            have hcover := Finset.ext_iff.mp
              (weightedSpineEdges_exact_cover edges spine.exposedSide spine.stopSides.1) edge
            have : edge ∈ firstEdges ∪ (secondEdges ∪ thirdEdges) := hcover.mpr hedge
            rcases Finset.mem_union.mp this with hfirst' | hrest
            · exact False.elim (hfirst hfirst')
            · rcases Finset.mem_union.mp hrest with hsecond' | hthird'
              · exact False.elim (hsecond hsecond')
              · exact hthird'
          rcases ihThird edge hthird with ⟨owner, howner, hunique⟩
          refine ⟨Sum.inr (Sum.inr owner), by simpa [edgeRegion] using howner, ?_⟩
          intro candidate hcandidate
          cases candidate with
          | inl candidate =>
              have hfirst' : edge ∈ firstEdges :=
                firstTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
              exact False.elim (hfirst hfirst')
          | inr candidate =>
              cases candidate with
              | inl candidate =>
                  have hsecond' : edge ∈ secondEdges :=
                    secondTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                  exact False.elim (hsecond hsecond')
              | inr candidate =>
                  exact congrArg (fun x => Sum.inr (Sum.inr x))
                    (hunique candidate (by simpa [edgeRegion] using hcandidate))

theorem WeightedBoundaryEdgeRecursion.edgeRegions_isEdgeDivision
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (hroot : edges = directedEdgeFinset G) :
    IsEdgeDivision G tree.edgeRegion tree.edgeActive := by
  refine ⟨?_, ?_, ?_⟩
  · intro owner _ edge hedge
    rw [← hroot]
    exact tree.edgeRegion_subset owner hedge
  · intro owner _ x y
    exact tree.edgeRegion_reverse owner x y
  · intro edge hedge
    have hedgeRoot : edge ∈ edges := by simpa [hroot] using hedge
    rcases tree.existsUnique_edgeOwner edge hedgeRoot with ⟨owner, howner, hunique⟩
    refine ⟨owner, ⟨?_, howner⟩, ?_⟩
    · simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨edge, howner⟩
    · intro candidate hcandidate
      exact hunique candidate hcandidate.2

private theorem weighted_first_terminal_incident_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineFirstEdges edges spine.exposedSide)
      (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)))
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆
      weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine) := by
  apply (edgeIncidentVertices_mono (tree.edgeRegion_subset owner)).trans
  exact weightedSpineFirstEdges_incident_subset G hsubset hincident spine

private theorem weighted_second_terminal_incident_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)))
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆
      weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine) := by
  apply (edgeIncidentVertices_mono (tree.edgeRegion_subset owner)).trans
  exact weightedSpineSecondEdges_incident_subset G hsubset hincident spine

private theorem weighted_third_terminal_incident_subset
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)))
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆
      weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine) := by
  apply (edgeIncidentVertices_mono (tree.edgeRegion_subset owner)).trans
  exact weightedSpineThirdEdges_incident_subset G hincident spine

private theorem childCarriers_inter_subset_separator
    {first second separator : Finset ι} (hdisjoint : Disjoint first second) :
    (weightedSpineChildCarrier first separator) ∩
        (weightedSpineChildCarrier second separator) ⊆ separator := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hxFirstCarrier, hxSecondCarrier⟩
  rcases Finset.mem_union.mp hxFirstCarrier with hxFirst | hxSeparator
  · rcases Finset.mem_union.mp hxSecondCarrier with hxSecond | hxSeparator
    · exact False.elim ((Finset.disjoint_left.mp hdisjoint) hxFirst hxSecond)
    · exact hxSeparator
  · exact hxSeparator

private theorem weighted_first_second_terminal_inter_subset_separator
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (firstTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineFirstEdges edges spine.exposedSide)
      (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)))
    (secondTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)))
    (firstOwner : firstTree.edgeOwnerType) (secondOwner : secondTree.edgeOwnerType) :
    edgeIncidentVertices (firstTree.edgeRegion firstOwner) ∩
        edgeIncidentVertices (secondTree.edgeRegion secondOwner) ⊆
      markedSpineSeparatorUnion spine := by
  apply (Finset.inter_subset_inter
    (weighted_first_terminal_incident_subset hsubset hincident spine firstTree firstOwner)
    (weighted_second_terminal_incident_subset hsubset hincident spine secondTree secondOwner)).trans
  exact childCarriers_inter_subset_separator spine.exposedSide_disjoint_stopSides.1

private theorem weighted_first_third_terminal_inter_subset_separator
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (firstTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineFirstEdges edges spine.exposedSide)
      (weightedSpineChildCarrier spine.exposedSide (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)))
    (thirdTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)))
    (firstOwner : firstTree.edgeOwnerType) (thirdOwner : thirdTree.edgeOwnerType) :
    edgeIncidentVertices (firstTree.edgeRegion firstOwner) ∩
        edgeIncidentVertices (thirdTree.edgeRegion thirdOwner) ⊆
      markedSpineSeparatorUnion spine := by
  apply (Finset.inter_subset_inter
    (weighted_first_terminal_incident_subset hsubset hincident spine firstTree firstOwner)
    (weighted_third_terminal_incident_subset hincident spine thirdTree thirdOwner)).trans
  exact childCarriers_inter_subset_separator spine.exposedSide_disjoint_stopSides.2

private theorem weighted_second_third_terminal_inter_subset_separator
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (spine : MarkedSeparatorSpine (edgeRestrictedGraph G edges) boundary vertices)
    (secondTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.1 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)))
    (thirdTree : WeightedBoundaryEdgeRecursion G r spineBudget
      (weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1)
      (weightedSpineChildCarrier spine.stopSides.2 (markedSpineSeparatorUnion spine))
      (weightedSpineChildBoundary boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)))
    (secondOwner : secondTree.edgeOwnerType) (thirdOwner : thirdTree.edgeOwnerType) :
    edgeIncidentVertices (secondTree.edgeRegion secondOwner) ∩
        edgeIncidentVertices (thirdTree.edgeRegion thirdOwner) ⊆
      markedSpineSeparatorUnion spine := by
  apply (Finset.inter_subset_inter
    (weighted_second_terminal_incident_subset hsubset hincident spine secondTree secondOwner)
    (weighted_third_terminal_incident_subset hincident spine thirdTree thirdOwner)).trans
  exact childCarriers_inter_subset_separator spine.stopSides_disjoint

/-- An inherited boundary vertex that remains incident is retained to the leaf. -/
theorem WeightedBoundaryEdgeRecursion.initialBoundary_incident_subset_ownerBoundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    boundary ∩ edgeIncidentVertices (tree.edgeRegion owner) ⊆ tree.ownerBoundary owner := by
  induction tree with
  | leaf _ _ _ _ _ _ =>
      intro x hx
      simpa [ownerBoundary] using (Finset.mem_inter.mp hx).1
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge
      firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      cases owner with
      | inl owner =>
          intro x hx
          have hxInitial := (Finset.mem_inter.mp hx).1
          have hxIncident : x ∈ edgeIncidentVertices (firstTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
          have hxCarrier := weighted_first_terminal_incident_subset hsubset hincident spine
            firstTree owner hxIncident
          have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary spine.exposedSide
              (markedSpineSeparatorUnion spine) :=
            Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxInitial, hxCarrier⟩)
          simpa [ownerBoundary] using
            (ihFirst owner (Finset.mem_inter.mpr ⟨hxChildBoundary, hxIncident⟩))
      | inr owner =>
          cases owner with
          | inl owner =>
              intro x hx
              have hxInitial := (Finset.mem_inter.mp hx).1
              have hxIncident : x ∈ edgeIncidentVertices (secondTree.edgeRegion owner) := by
                simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
              have hxCarrier := weighted_second_terminal_incident_subset hsubset hincident spine
                secondTree owner hxIncident
              have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary spine.stopSides.1
                  (markedSpineSeparatorUnion spine) :=
                Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxInitial, hxCarrier⟩)
              simpa [ownerBoundary] using
                (ihSecond owner (Finset.mem_inter.mpr ⟨hxChildBoundary, hxIncident⟩))
          | inr owner =>
              intro x hx
              have hxInitial := (Finset.mem_inter.mp hx).1
              have hxIncident : x ∈ edgeIncidentVertices (thirdTree.edgeRegion owner) := by
                simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
              have hxCarrier := weighted_third_terminal_incident_subset hincident spine
                thirdTree owner hxIncident
              have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary spine.stopSides.2
                  (markedSpineSeparatorUnion spine) :=
                Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxInitial, hxCarrier⟩)
              simpa [ownerBoundary] using
                (ihThird owner (Finset.mem_inter.mpr ⟨hxChildBoundary, hxIncident⟩))

/-- Every shared vertex incident to a terminal region is charged to its leaf boundary. -/
theorem WeightedBoundaryEdgeRecursion.localSharedBoundary_subset_ownerBoundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ∩
        edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive ⊆
      tree.ownerBoundary owner := by
  classical
  induction tree with
  | leaf _ _ _ _ _ _ =>
      intro x hx
      rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
        ⟨i, hi, j, hj, hij, hxi, hxj⟩
      have : i = j := by
        simpa [edgeOwnerType] using (Subsingleton.elim (α := Unit) i j)
      exact False.elim (hij this)
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge
      firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      let root := WeightedBoundaryEdgeRecursion.split hsubset hsymmetric hincident hboundary hcard
        spine hseparatorCard hboundaryLarge firstTree secondTree thirdTree
      cases owner with
      | inl owner =>
          intro x hx
          have hxOwner : x ∈ edgeIncidentVertices (firstTree.edgeRegion owner) := by
            simpa [root, edgeRegion] using (Finset.mem_inter.mp hx).1
          have hownerActive : owner ∈ firstTree.edgeActive := by
            simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
            exact ⟨edge, hedge⟩
          rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1
              (Finset.mem_inter.mp hx).2 with ⟨i, hi, j, hj, hij, hxi, hxj⟩
          have hcandidate : ∃ candidate : root.edgeOwnerType,
              candidate ≠ Sum.inl owner ∧ candidate ∈ root.edgeActive ∧
                x ∈ edgeIncidentVertices (root.edgeRegion candidate) := by
            by_cases hiOwner : i = Sum.inl owner
            · refine ⟨j, ?_, hj, hxj⟩
              intro hjOwner
              exact hij (hiOwner.trans hjOwner.symm)
            · exact ⟨i, hiOwner, hi, hxi⟩
          rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
          cases candidate with
          | inl candidate =>
              have hcandidateActive : candidate ∈ firstTree.edgeActive := by
                have hnonempty := (@Finset.mem_filter _ _
                  (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_univ _, hnonempty.2⟩
              have hxcandidate' : x ∈ edgeIncidentVertices (firstTree.edgeRegion candidate) := by
                simpa [root, edgeRegion] using hxcandidate
              have hxShared : x ∈ edgeDivisionSharedBoundary
                  firstTree.edgeRegion firstTree.edgeActive := by
                apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                  hxcandidate'⟩
                intro heq
                exact hne (congrArg Sum.inl heq.symm)
              simpa [root, ownerBoundary] using
                (ihFirst owner (Finset.mem_inter.mpr ⟨hxOwner, hxShared⟩))
          | inr candidate =>
              cases candidate with
              | inl candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (secondTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_second_terminal_inter_subset_separator hsubset hincident spine
                      firstTree secondTree owner candidate
                      (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.exposedSide (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (firstTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
              | inr candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (thirdTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_third_terminal_inter_subset_separator hsubset hincident spine
                      firstTree thirdTree owner candidate
                      (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.exposedSide (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (firstTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
      | inr owner =>
          cases owner with
          | inl owner =>
              intro x hx
              have hxOwner : x ∈ edgeIncidentVertices (secondTree.edgeRegion owner) := by
                simpa [root, edgeRegion] using (Finset.mem_inter.mp hx).1
              have hownerActive : owner ∈ secondTree.edgeActive := by
                simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
                exact ⟨edge, hedge⟩
              rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1
                  (Finset.mem_inter.mp hx).2 with ⟨i, hi, j, hj, hij, hxi, hxj⟩
              have hcandidate : ∃ candidate : root.edgeOwnerType,
                  candidate ≠ Sum.inr (Sum.inl owner) ∧ candidate ∈ root.edgeActive ∧
                    x ∈ edgeIncidentVertices (root.edgeRegion candidate) := by
                by_cases hiOwner : i = Sum.inr (Sum.inl owner)
                · refine ⟨j, ?_, hj, hxj⟩
                  intro hjOwner
                  exact hij (hiOwner.trans hjOwner.symm)
                · exact ⟨i, hiOwner, hi, hxi⟩
              rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
              cases candidate with
              | inl candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (firstTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_second_terminal_inter_subset_separator hsubset hincident spine
                      firstTree secondTree candidate owner
                      (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.stopSides.1 (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (secondTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
              | inr candidate =>
                  cases candidate with
                  | inl candidate =>
                      have hcandidateActive : candidate ∈ secondTree.edgeActive := by
                        have hnonempty := (@Finset.mem_filter _ _
                          (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                        apply Finset.mem_filter.mpr
                        exact ⟨Finset.mem_univ _, hnonempty.2⟩
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (secondTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxShared : x ∈ edgeDivisionSharedBoundary
                          secondTree.edgeRegion secondTree.edgeActive := by
                        apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                        refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                          hxcandidate'⟩
                        intro heq
                        exact hne (congrArg (fun z => Sum.inr (Sum.inl z)) heq.symm)
                      simpa [root, ownerBoundary] using
                        (ihSecond owner (Finset.mem_inter.mpr ⟨hxOwner, hxShared⟩))
                  | inr candidate =>
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (thirdTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                        weighted_second_third_terminal_inter_subset_separator hsubset hincident
                          spine secondTree thirdTree owner candidate
                          (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩)
                      have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                          spine.stopSides.1 (markedSpineSeparatorUnion spine) :=
                        Finset.mem_union_left _ hxSeparator
                      simpa [root, ownerBoundary] using
                        (secondTree.initialBoundary_incident_subset_ownerBoundary owner
                          (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
          | inr owner =>
              intro x hx
              have hxOwner : x ∈ edgeIncidentVertices (thirdTree.edgeRegion owner) := by
                simpa [root, edgeRegion] using (Finset.mem_inter.mp hx).1
              have hownerActive : owner ∈ thirdTree.edgeActive := by
                simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
                rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
                exact ⟨edge, hedge⟩
              rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1
                  (Finset.mem_inter.mp hx).2 with ⟨i, hi, j, hj, hij, hxi, hxj⟩
              have hcandidate : ∃ candidate : root.edgeOwnerType,
                  candidate ≠ Sum.inr (Sum.inr owner) ∧ candidate ∈ root.edgeActive ∧
                    x ∈ edgeIncidentVertices (root.edgeRegion candidate) := by
                by_cases hiOwner : i = Sum.inr (Sum.inr owner)
                · refine ⟨j, ?_, hj, hxj⟩
                  intro hjOwner
                  exact hij (hiOwner.trans hjOwner.symm)
                · exact ⟨i, hiOwner, hi, hxi⟩
              rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
              cases candidate with
              | inl candidate =>
                  have hxcandidate' : x ∈ edgeIncidentVertices
                      (firstTree.edgeRegion candidate) := by
                    simpa [root, edgeRegion] using hxcandidate
                  have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                    weighted_first_third_terminal_inter_subset_separator hsubset hincident spine
                      firstTree thirdTree candidate owner
                      (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩)
                  have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                      spine.stopSides.2 (markedSpineSeparatorUnion spine) :=
                    Finset.mem_union_left _ hxSeparator
                  simpa [root, ownerBoundary] using
                    (thirdTree.initialBoundary_incident_subset_ownerBoundary owner
                      (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
              | inr candidate =>
                  cases candidate with
                  | inl candidate =>
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (secondTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxSeparator : x ∈ markedSpineSeparatorUnion spine :=
                        weighted_second_third_terminal_inter_subset_separator hsubset hincident
                          spine secondTree thirdTree candidate owner
                          (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩)
                      have hxChildBoundary : x ∈ weightedSpineChildBoundary boundary
                          spine.stopSides.2 (markedSpineSeparatorUnion spine) :=
                        Finset.mem_union_left _ hxSeparator
                      simpa [root, ownerBoundary] using
                        (thirdTree.initialBoundary_incident_subset_ownerBoundary owner
                          (Finset.mem_inter.mpr ⟨hxChildBoundary, hxOwner⟩))
                  | inr candidate =>
                      have hcandidateActive : candidate ∈ thirdTree.edgeActive := by
                        have hnonempty := (@Finset.mem_filter _ _
                          (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                        apply Finset.mem_filter.mpr
                        exact ⟨Finset.mem_univ _, hnonempty.2⟩
                      have hxcandidate' : x ∈ edgeIncidentVertices
                          (thirdTree.edgeRegion candidate) := by
                        simpa [root, edgeRegion] using hxcandidate
                      have hxShared : x ∈ edgeDivisionSharedBoundary
                          thirdTree.edgeRegion thirdTree.edgeActive := by
                        apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                        refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                          hxcandidate'⟩
                        intro heq
                        exact hne (congrArg (fun z => Sum.inr (Sum.inr z)) heq.symm)
                      simpa [root, ownerBoundary] using
                        (ihThird owner (Finset.mem_inter.mpr ⟨hxOwner, hxShared⟩))

/-- Number of terminal owners, including harmless empty edge regions. -/
noncomputable def WeightedBoundaryEdgeRecursion.terminalOwnerCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary → Nat
  | .leaf _ _ _ _ _ _ => 1
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree =>
      firstTree.terminalOwnerCount + secondTree.terminalOwnerCount +
        thirdTree.terminalOwnerCount

/-- Number of internal weighted-spine rebalancing operations. -/
private noncomputable def WeightedBoundaryEdgeRecursion.splitCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι} :
    WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary → Nat
  | .leaf _ _ _ _ _ _ => 0
  | .split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree =>
      1 + firstTree.splitCount + secondTree.splitCount + thirdTree.splitCount

theorem WeightedBoundaryEdgeRecursion.edgeOwnerType_card_eq_terminalOwnerCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    Fintype.card tree.edgeOwnerType = tree.terminalOwnerCount := by
  induction tree with
  | leaf _ _ _ _ _ _ => simp [edgeOwnerType, terminalOwnerCount]
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      change Fintype.card
          (Sum firstTree.edgeOwnerType (Sum secondTree.edgeOwnerType thirdTree.edgeOwnerType)) = _
      simp [Fintype.card_sum, ihFirst, ihSecond, ihThird, terminalOwnerCount,
        Nat.add_assoc]

/-- A full ternary tree has exactly two more leaves per internal node. -/
private theorem WeightedBoundaryEdgeRecursion.terminalOwnerCount_eq_one_add_two_mul_splitCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.terminalOwnerCount = 1 + 2 * tree.splitCount := by
  induction tree with
  | leaf _ _ _ _ _ _ => rfl
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      simp only [terminalOwnerCount, splitCount]
      omega

private theorem three_inter_card_sum_le
    (boundary first second third : Finset ι)
    (hfirstSecond : Disjoint first second) (hfirstThird : Disjoint first third)
    (hsecondThird : Disjoint second third) :
    (boundary ∩ first).card + (boundary ∩ second).card + (boundary ∩ third).card ≤
      boundary.card := by
  let firstPart := boundary ∩ first
  let secondPart := boundary ∩ second
  let thirdPart := boundary ∩ third
  have h12 : Disjoint firstPart secondPart := by
    apply Finset.disjoint_left.mpr
    intro x hxFirst hxSecond
    exact (Finset.disjoint_left.mp hfirstSecond)
      (Finset.mem_inter.mp hxFirst).2 (Finset.mem_inter.mp hxSecond).2
  have h13 : Disjoint firstPart thirdPart := by
    apply Finset.disjoint_left.mpr
    intro x hxFirst hxThird
    exact (Finset.disjoint_left.mp hfirstThird)
      (Finset.mem_inter.mp hxFirst).2 (Finset.mem_inter.mp hxThird).2
  have h23 : Disjoint secondPart thirdPart := by
    apply Finset.disjoint_left.mpr
    intro x hxSecond hxThird
    exact (Finset.disjoint_left.mp hsecondThird)
      (Finset.mem_inter.mp hxSecond).2 (Finset.mem_inter.mp hxThird).2
  have hunionDisjoint : Disjoint (firstPart ∪ secondPart) thirdPart :=
    Finset.disjoint_union_left.mpr ⟨h13, h23⟩
  have hunionSubset : firstPart ∪ secondPart ∪ thirdPart ⊆ boundary := by
    exact Finset.union_subset (Finset.union_subset Finset.inter_subset_left
      Finset.inter_subset_left) Finset.inter_subset_left
  calc
    firstPart.card + secondPart.card + thirdPart.card =
        (firstPart ∪ secondPart ∪ thirdPart).card := by
      symm
      rw [Finset.card_union_of_disjoint hunionDisjoint,
        Finset.card_union_of_disjoint h12]
    _ ≤ boundary.card := Finset.card_le_card hunionSubset

/--
Every continuing weighted subtree spends three boundary-budget units.  The
three possible continuing children are paid for by disjoint marked sides; the
single-child case additionally uses the exact two-thirds marked-light bound.
-/
private theorem WeightedBoundaryEdgeRecursion.splitCount_zero_or_mul_add_three_le_boundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.splitCount = 0 ∨ (tree.splitCount + 3) * spineBudget ≤ boundary.card := by
  induction tree with
  | leaf _ _ _ _ _ _ => exact Or.inl rfl
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge firstTree secondTree thirdTree
      ihFirst ihSecond ihThird =>
      right
      have hfirstCard := weightedSpineChildBoundary_card_le boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)
      have hsecondCard := weightedSpineChildBoundary_card_le boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)
      have hthirdCard := weightedSpineChildBoundary_card_le boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)
      have hparts := three_inter_card_sum_le boundary spine.exposedSide spine.stopSides.1
        spine.stopSides.2 spine.exposedSide_disjoint_stopSides.1
        spine.exposedSide_disjoint_stopSides.2 spine.stopSides_disjoint
      have hfirstLight : 3 * (boundary ∩ spine.exposedSide).card ≤ 2 * boundary.card :=
        spine.exposedSide_marked_light
      have hstopLight := spine.stopSides_marked_light
      rcases ihFirst with hfirstZero | hfirstCharge <;>
        rcases ihSecond with hsecondZero | hsecondCharge <;>
        rcases ihThird with hthirdZero | hthirdCharge
      · simp only [splitCount, hfirstZero, hsecondZero, hthirdZero, zero_add,
          add_zero, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [splitCount, hfirstZero, hsecondZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hthirdCharge ⊢
        omega
      · simp only [splitCount, hfirstZero, hthirdZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hsecondCharge ⊢
        omega
      · simp only [splitCount, hfirstZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hsecondCharge hthirdCharge ⊢
        omega
      · simp only [splitCount, hsecondZero, hthirdZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hfirstCharge ⊢
        omega
      · simp only [splitCount, hsecondZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hfirstCharge hthirdCharge ⊢
        omega
      · simp only [splitCount, hthirdZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hfirstCharge hsecondCharge ⊢
        omega
      · simp only [splitCount, Nat.add_mul, Nat.one_mul] at hfirstCharge hsecondCharge hthirdCharge ⊢
        omega

private theorem WeightedBoundaryEdgeRecursion.splitCount_mul_budget_le_boundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.splitCount * spineBudget ≤ boundary.card := by
  rcases tree.splitCount_zero_or_mul_add_three_le_boundary with hzero | hcharge
  · simp [hzero]
  · exact (Nat.mul_le_mul_right spineBudget (Nat.le_add_right tree.splitCount 3)).trans hcharge

theorem WeightedBoundaryEdgeRecursion.terminalOwnerCount_mul_budget_le
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.terminalOwnerCount * spineBudget ≤ spineBudget + 2 * boundary.card := by
  rw [tree.terminalOwnerCount_eq_one_add_two_mul_splitCount, Nat.add_mul, Nat.one_mul]
  have hcharge := Nat.mul_le_mul_left 2 tree.splitCount_mul_budget_le_boundary
  simpa [Nat.mul_assoc] using Nat.add_le_add_left hcharge spineBudget

end QEC.Locality

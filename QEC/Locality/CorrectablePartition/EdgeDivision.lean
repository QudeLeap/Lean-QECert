import QEC.Locality.CorrectablePartition.SmallBoundary
/-!
# Source-faithful edge divisions for the BGKL route

HKRS regions partition edges, not vertices.  This module records the finite
directed-edge presentation of that convention and proves the graph-to-QEC
adapter which is independent of the still-missing quantitative HKRS existence
theorem.  Shared vertices are removed from region incident sets; the resulting
interiors are disjoint, have no cross interaction edge, and have outer boundary
contained in the shared boundary.

The module also proves the convention bridge used before applying HKRS:
deleting edges from a graph on the same vertex type cannot increase any of the
repository's measured induced-subgraph `2/3` separator values.
-/

namespace QEC.Locality

open QEC Semantics Coding

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- `H` is obtained from `G` by deleting edges while retaining the vertex type. -/
def IsSpanningSubgraph (H G : ConnectivityGraph ι) : Prop :=
  ∀ ⦃x y : ι⦄, H.adjacent x y → G.adjacent x y

/-- A no-cross-edge certificate survives deletion of graph edges. -/
theorem NoEdgeBetween.mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    {left right : Finset ι} (hnoEdge : NoEdgeBetween G left right) :
    NoEdgeBetween H left right := by
  intro x hx y hy hHxy
  exact hnoEdge hx hy (hHG hHxy)

/-- Every balanced separator for a graph remains balanced after deleting edges. -/
theorem IsTwoThirdsBalancedVertexSeparator.mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    {vertices separator : Finset ι}
    (hseparator : IsTwoThirdsBalancedVertexSeparator G vertices separator) :
    IsTwoThirdsBalancedVertexSeparator H vertices separator := by
  rcases hseparator with
    ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright, hnoEdge⟩
  exact ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright,
    hnoEdge.mono_spanningSubgraph hHG⟩

/-- Deleting edges cannot increase the minimum separator of a fixed vertex set. -/
theorem minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    (vertices : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize H vertices ≤
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by
  rcases exists_minimumTwoThirdsBalancedVertexSeparator G vertices with
    ⟨separator, hsubset, hbalanced, hcard⟩
  rw [← hcard]
  exact minimumTwoThirdsBalancedVertexSeparatorSize_le_card H vertices separator
    hsubset (hbalanced.mono_spanningSubgraph hHG)

/-- The exact induced-subgraph separation profile is monotone under edge deletion. -/
theorem twoThirdsSeparationProfile_mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G) (scale : Nat) :
    twoThirdsSeparationProfile H scale ≤ twoThirdsSeparationProfile G scale := by
  classical
  apply Finset.max'_le
  intro size hsize
  rcases Finset.mem_image.1 hsize with ⟨vertices, hvertices, rfl⟩
  rcases (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices with
    ⟨hsubset, hcard⟩
  exact (minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
    hHG vertices).trans
      (minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
        G scale vertices hsubset hcard)

/-- The finite set of oriented representatives of graph edges. -/
noncomputable def directedEdgeFinset (G : ConnectivityGraph ι) : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter fun edge => decide (G.adjacent edge.1 edge.2)

omit [DecidableEq ι] in
theorem mem_directedEdgeFinset_iff (G : ConnectivityGraph ι) (x y : ι) :
    (x, y) ∈ directedEdgeFinset G ↔ G.adjacent x y := by
  classical
  simp [directedEdgeFinset]

/-- Vertices incident to at least one edge in a finite edge region. -/
def edgeIncidentVertices (edges : Finset (ι × ι)) : Finset ι :=
  edges.biUnion fun edge => {edge.1, edge.2}

omit [Fintype ι] in
theorem mem_edgeIncidentVertices_iff (edges : Finset (ι × ι)) (x : ι) :
    x ∈ edgeIncidentVertices edges ↔
      ∃ edge ∈ edges, x = edge.1 ∨ x = edge.2 := by
  classical
  simp [edgeIncidentVertices]

/--
An edge division assigns every oriented graph edge to exactly one active
region.  Symmetry of the graph means both orientations occur; uniqueness is
required separately for each orientation and is enough for the interior
adapter below.
-/
def IsEdgeDivision {m : Type w} [DecidableEq m]
    (G : ConnectivityGraph ι) (regions : m → Finset (ι × ι))
    (active : Finset m) : Prop :=
  (∀ i, i ∈ active → regions i ⊆ directedEdgeFinset G) ∧
    (∀ i, i ∈ active → ∀ x y, (x, y) ∈ regions i ↔ (y, x) ∈ regions i) ∧
    ∀ edge, edge ∈ directedEdgeFinset G →
      ∃! i, i ∈ active ∧ edge ∈ regions i

/-- The active region edge sets cover exactly the graph edges. -/
theorem edgeDivision_edges_cover {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active) :
    active.biUnion regions = directedEdgeFinset G := by
  classical
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_biUnion.mp hedge with ⟨i, hi, hiedge⟩
    exact hDivision.1 i hi hiedge
  · intro hedge
    rcases hDivision.2.2 edge hedge with ⟨i, ⟨hi, hiedge⟩, _⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, hiedge⟩

omit [DecidableEq ι] in
/-- Distinct active regions have disjoint edge sets. -/
theorem edgeDivision_regions_pairwise_disjoint {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (regions i) (regions j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro edge hiedge hjedge
  have hedge : edge ∈ directedEdgeFinset G := hDivision.1 i hi hiedge
  rcases hDivision.2.2 edge hedge with ⟨owner, _, howner⟩
  have hiOwner : i = owner := howner i ⟨hi, hiedge⟩
  have hjOwner : j = owner := howner j ⟨hj, hjedge⟩
  exact hij (hiOwner.trans hjOwner.symm)

/-- Vertices incident to two distinct active edge regions are shared boundary vertices. -/
noncomputable def edgeDivisionSharedBoundary {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m) : Finset ι := by
  classical
  exact Finset.univ.filter fun x => decide
    (∃ i ∈ active, ∃ j ∈ active, i ≠ j ∧
      x ∈ edgeIncidentVertices (regions i) ∧
      x ∈ edgeIncidentVertices (regions j))

theorem mem_edgeDivisionSharedBoundary_iff {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m) (x : ι) :
    x ∈ edgeDivisionSharedBoundary regions active ↔
      ∃ i ∈ active, ∃ j ∈ active, i ≠ j ∧
        x ∈ edgeIncidentVertices (regions i) ∧
        x ∈ edgeIncidentVertices (regions j) := by
  classical
  simp [edgeDivisionSharedBoundary]

/-- The interior of a region is its incident vertex set minus all shared vertices. -/
noncomputable def edgeDivisionInterior {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m) (i : m) : Finset ι :=
  edgeIncidentVertices (regions i) \ edgeDivisionSharedBoundary regions active

/-- Vertices not incident to any graph edge. -/
noncomputable def graphIsolatedVertices (G : ConnectivityGraph ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun x => decide (∀ y, ¬ G.adjacent x y)

omit [DecidableEq ι] in
theorem mem_graphIsolatedVertices_iff (G : ConnectivityGraph ι) (x : ι) :
    x ∈ graphIsolatedVertices G ↔ ∀ y, ¬ G.adjacent x y := by
  classical
  simp [graphIsolatedVertices]

/-- Distinct edge-region interiors are vertex-disjoint. -/
theorem edgeDivisionInteriors_disjoint {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    Disjoint (edgeDivisionInterior regions active i)
      (edgeDivisionInterior regions active j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hxi' := Finset.mem_sdiff.mp hxi
  have hxj' := Finset.mem_sdiff.mp hxj
  exact hxi'.2 ((mem_edgeDivisionSharedBoundary_iff regions active x).2
    ⟨i, hi, j, hj, hij, hxi'.1, hxj'.1⟩)

omit [Fintype ι] in
private theorem endpoint_mem_edgeIncidentVertices {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) {i : m} {x y : ι}
    (hedge : (x, y) ∈ regions i) :
    x ∈ edgeIncidentVertices (regions i) ∧
      y ∈ edgeIncidentVertices (regions i) := by
  constructor
  · exact (mem_edgeIncidentVertices_iff (regions i) x).2
      ⟨(x, y), hedge, Or.inl rfl⟩
  · exact (mem_edgeIncidentVertices_iff (regions i) y).2
      ⟨(x, y), hedge, Or.inr rfl⟩

private theorem interior_incident_region_unique {m : Type w} [DecidableEq m]
    (regions : m → Finset (ι × ι)) (active : Finset m)
    {i k : m} (hi : i ∈ active) (hk : k ∈ active) {x : ι}
    (hxi : x ∈ edgeDivisionInterior regions active i)
    (hxk : x ∈ edgeIncidentVertices (regions k)) : k = i := by
  classical
  by_contra hki
  have hxi' := Finset.mem_sdiff.mp hxi
  exact hxi'.2 ((mem_edgeDivisionSharedBoundary_iff regions active x).2
    ⟨i, hi, k, hk, Ne.symm hki, hxi'.1, hxk⟩)

/-- Different interiors have no edge between them in the divided graph. -/
theorem edgeDivisionInteriors_noEdgeBetween {m : Type w} [DecidableEq m]
    {G : ConnectivityGraph ι} {regions : m → Finset (ι × ι)}
    {active : Finset m} (hDivision : IsEdgeDivision G regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    NoEdgeBetween G (edgeDivisionInterior regions active i)
      (edgeDivisionInterior regions active j) := by
  classical
  intro x hxi y hyj hxy
  have hedge : (x, y) ∈ directedEdgeFinset G :=
    (mem_directedEdgeFinset_iff G x y).2 hxy
  rcases (hDivision.2.2 (x, y) hedge) with ⟨k, ⟨hk, hkedge⟩, _⟩
  have endpoints := endpoint_mem_edgeIncidentVertices regions hkedge
  have hki := interior_incident_region_unique regions active hi hk hxi endpoints.1
  have hkj := interior_incident_region_unique regions active hj hk hyj endpoints.2
  exact hij (hki.symm.trans hkj)

/-- Every outer neighbor of a region interior is a shared boundary vertex. -/
theorem fixedGeneratorOuterBoundary_interior_subset_sharedBoundary
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i : m} (hi : i ∈ active) :
    fixedGeneratorOuterBoundaryFinset P (edgeDivisionInterior regions active i) ⊆
      edgeDivisionSharedBoundary regions active := by
  classical
  intro y hy
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hy
  rcases hy with ⟨hyInterior, x, hxi, hxy⟩
  have hedge : (x, y) ∈ directedEdgeFinset P.fixedGeneratorInteractionGraph :=
    (mem_directedEdgeFinset_iff _ x y).2 hxy
  rcases hDivision.2.2 (x, y) hedge with ⟨k, ⟨hk, hkedge⟩, _⟩
  have endpoints := endpoint_mem_edgeIncidentVertices regions hkedge
  have hki := interior_incident_region_unique regions active hi hk hxi endpoints.1
  subst k
  by_contra hyShared
  apply hyInterior
  exact Finset.mem_sdiff.mpr ⟨endpoints.2, hyShared⟩

/-- The outer-boundary cardinality is bounded by the global shared boundary. -/
theorem fixedGeneratorOuterBoundary_interior_card_le_sharedBoundary_card
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i : m} (hi : i ∈ active) :
    (fixedGeneratorOuterBoundaryFinset P
      (edgeDivisionInterior regions active i)).card ≤
        (edgeDivisionSharedBoundary regions active).card :=
  Finset.card_le_card
    (fixedGeneratorOuterBoundary_interior_subset_sharedBoundary P hDivision hi)

/-- The fixed-generator interiors of distinct regions are source-level decoupled. -/
theorem edgeDivisionInteriors_fixedGeneratorDecoupled
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    {i j : m} (hi : i ∈ active) (hj : j ∈ active) (hij : i ≠ j) :
    P.fixedGeneratorDecoupled
      (edgeDivisionInterior regions active i : Set ι)
      (edgeDivisionInterior regions active j : Set ι) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Finset.disjoint_left.mp
      (edgeDivisionInteriors_disjoint regions active hi hj hij)
      (by simpa using hxi) (by simpa using hxj)
  · intro x hxi y hyj
    exact edgeDivisionInteriors_noEdgeBetween hDivision hi hj hij
      (by simpa using hxi) (by simpa using hyj)

/-- All non-isolated vertices lie in an interior or in the shared boundary. -/
theorem vertices_subset_interiors_union_sharedBoundary_union_isolated
    {m : Type w} [DecidableEq m] {G : ConnectivityGraph ι}
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision G regions active) :
    Finset.univ ⊆
      (active.biUnion fun i => edgeDivisionInterior regions active i) ∪
        edgeDivisionSharedBoundary regions active ∪ graphIsolatedVertices G := by
  classical
  intro x _
  by_cases hIsolated : x ∈ graphIsolatedVertices G
  · exact Finset.mem_union_right _ hIsolated
  · have hNotAll : ¬ ∀ y, ¬ G.adjacent x y := by
      simpa [mem_graphIsolatedVertices_iff] using hIsolated
    push Not at hNotAll
    rcases hNotAll with ⟨y, hxy⟩
    have hedge : (x, y) ∈ directedEdgeFinset G :=
      (mem_directedEdgeFinset_iff G x y).2 hxy
    rcases hDivision.2.2 (x, y) hedge with ⟨i, ⟨hi, hiedge⟩, _⟩
    have hxi := (endpoint_mem_edgeIncidentVertices regions hiedge).1
    by_cases hxShared : x ∈ edgeDivisionSharedBoundary regions active
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxShared)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨hxi, hxShared⟩⟩

/-- Removing all interiors leaves only shared-boundary and isolated vertices. -/
theorem complement_interiors_subset_sharedBoundary_union_isolated
    {m : Type w} [DecidableEq m] {G : ConnectivityGraph ι}
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hDivision : IsEdgeDivision G regions active) :
    Finset.univ \ (active.biUnion fun i => edgeDivisionInterior regions active i) ⊆
      edgeDivisionSharedBoundary regions active ∪ graphIsolatedVertices G := by
  intro x hx
  have hcover := vertices_subset_interiors_union_sharedBoundary_union_isolated hDivision
    (Finset.mem_univ x)
  rcases Finset.mem_union.mp hcover with hInteriorOrShared | hIsolated
  · rcases Finset.mem_union.mp hInteriorOrShared with hInterior | hShared
    · exact (Finset.mem_sdiff.mp hx).2 hInterior |>.elim
    · exact Finset.mem_union_left _ hShared
  · exact Finset.mem_union_right _ hIsolated

/--
If every interior meets the exact #382 size and boundary hypotheses, the HKRS
interior adapter constructs a concrete recovery for their finite union using
the #373 pairwise-decoupled union theorem.
-/
theorem exists_erasureRecovery_of_edgeDivisionInteriors
    {κ : Type v} [Fintype κ] {m : Type w} [DecidableEq m]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (regions : m → Finset (ι × ι)) (active : Finset m)
    (hDivision : IsEdgeDivision P.fixedGeneratorInteractionGraph regions active)
    (hSmall : ∀ i, i ∈ active →
      ((edgeDivisionInterior regions active i).card : ℝ) ≤
        Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : ∀ i, i ∈ active →
      4 * (fixedGeneratorOuterBoundaryFinset P
        (edgeDivisionInterior regions active i)).card ≤ d) :
    ∃ recovery : QuantumChannel
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).complementSystem
        P.semanticCode
        (familyUnionSubsystem
          (fun i => finiteSubsystemOfFinset (edgeDivisionInterior regions active i))
          active).erasureChannelFromRegister recovery := by
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
  · intro i hi
    exact bgklSmallBoundaryCorrectable P d hd hdn hDistance beta exponent
      hProfile hexponent (edgeDivisionInterior regions active i)
        (hSmall i hi) (hBoundary i hi)
  · intro i hi j hj hij
    exact edgeDivisionInteriors_fixedGeneratorDecoupled P hDivision hi hj hij

end QEC.Locality

import QEC.Locality.CorrectablePartition.EdgeDivision
/-!
# Explicit finite edge-division constructions

This module contains the project-owned finite constructions used at the leaves
and degenerate branches of the profile-sensitive separator recursion.
The construction is deliberately independent of HKRS: an arbitrary finite
enumeration chooses one representative of each undirected edge and assigns the
two orientations to that representative.

The resulting regions have at most two incident vertices.  This proves the
orientation, ownership, coverage, and `r >= 2` leaf obligations without
assuming an `IsEdgeDivision`.  The profile-sensitive count and boundary bounds
are completed separately by `ProfileSeparatorExplicitDivision`.
-/

namespace QEC.Locality

universe u w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Reverse an oriented edge. -/
def reverseDirectedEdge (edge : ι × ι) : ι × ι :=
  (edge.2, edge.1)

/-- A fixed finite enumeration used only to choose edge representatives. -/
noncomputable def finiteVertexIndex (x : ι) : Fin (Fintype.card ι) :=
  Fintype.equivFin ι x

/--
The canonical representative of an unordered pair, chosen by the fixed finite
enumeration.  Loops are harmless here; graph looplessness excludes them from
`directedEdgeFinset`.
-/
noncomputable def canonicalEdgeOwner (edge : ι × ι) : ι × ι :=
  if finiteVertexIndex edge.1 < finiteVertexIndex edge.2 then edge
  else reverseDirectedEdge edge

omit [DecidableEq ι] in
theorem canonicalEdgeOwner_eq_self_or_reverse (edge : ι × ι) :
    canonicalEdgeOwner edge = edge ∨
      canonicalEdgeOwner edge = reverseDirectedEdge edge := by
  classical
  simp only [canonicalEdgeOwner]
  split <;> simp_all

omit [DecidableEq ι] in
/-- Reversing an oriented pair does not change its canonical owner. -/
theorem canonicalEdgeOwner_reverse (edge : ι × ι) :
    canonicalEdgeOwner (reverseDirectedEdge edge) = canonicalEdgeOwner edge := by
  classical
  rcases edge with ⟨x, y⟩
  simp only [canonicalEdgeOwner, reverseDirectedEdge]
  by_cases hxy : finiteVertexIndex x < finiteVertexIndex y
  · have hyx : ¬ finiteVertexIndex y < finiteVertexIndex x :=
      (not_lt_of_ge (le_of_lt hxy))
    simp [hxy, hyx]
  · by_cases hyx : finiteVertexIndex y < finiteVertexIndex x
    · simp [hxy, hyx]
    · have hindex : finiteVertexIndex x = finiteVertexIndex y :=
        le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      have hxyEq : x = y := (Fintype.equivFin ι).injective hindex
      subst y
      simp

/-- The finite set of canonical representatives of graph edges. -/
noncomputable def canonicalEdgeRepresentatives (G : ConnectivityGraph ι) :
    Finset (ι × ι) :=
  (directedEdgeFinset G).image canonicalEdgeOwner

/-- All oriented graph edges owned by one canonical representative. -/
noncomputable def canonicalEdgeRegion (G : ConnectivityGraph ι)
    (owner : ι × ι) : Finset (ι × ι) :=
  (directedEdgeFinset G).filter fun edge => canonicalEdgeOwner edge = owner

theorem mem_canonicalEdgeRegion_iff (G : ConnectivityGraph ι)
    (owner edge : ι × ι) :
    edge ∈ canonicalEdgeRegion G owner ↔
      edge ∈ directedEdgeFinset G ∧ canonicalEdgeOwner edge = owner := by
  classical
  simp [canonicalEdgeRegion]

/--
The canonical representative construction is a genuine finite edge division:
every orientation has one owner and the reverse orientation has the same owner.
-/
theorem canonicalEdgeRegions_isEdgeDivision (G : ConnectivityGraph ι) :
    IsEdgeDivision G (canonicalEdgeRegion G) (canonicalEdgeRepresentatives G) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro owner _ edge hedge
    exact (mem_canonicalEdgeRegion_iff G owner edge).1 hedge |>.1
  · intro owner _ x y
    rw [mem_canonicalEdgeRegion_iff, mem_canonicalEdgeRegion_iff]
    constructor
    · rintro ⟨hxy, howner⟩
      exact ⟨(mem_directedEdgeFinset_iff G y x).2
        (G.symmetric ((mem_directedEdgeFinset_iff G x y).1 hxy)),
        (canonicalEdgeOwner_reverse (x, y)).trans howner⟩
    · rintro ⟨hyx, howner⟩
      exact ⟨(mem_directedEdgeFinset_iff G x y).2
        (G.symmetric ((mem_directedEdgeFinset_iff G y x).1 hyx)),
        (canonicalEdgeOwner_reverse (y, x)).trans howner⟩
  · intro edge hedge
    refine ⟨canonicalEdgeOwner edge, ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.2 ⟨edge, hedge, rfl⟩
      · exact (mem_canonicalEdgeRegion_iff G (canonicalEdgeOwner edge) edge).2
          ⟨hedge, rfl⟩
    · intro owner howner
      exact (mem_canonicalEdgeRegion_iff G owner edge).1 howner.2 |>.2.symm

private theorem canonicalEdgeRegion_incident_subset_pair
    (G : ConnectivityGraph ι) (owner : ι × ι) :
    edgeIncidentVertices (canonicalEdgeRegion G owner) ⊆ {owner.1, owner.2} := by
  classical
  intro x hx
  rcases (mem_edgeIncidentVertices_iff (canonicalEdgeRegion G owner) x).1 hx with
    ⟨edge, hedge, hxLeft | hxRight⟩
  all_goals
    have howner := (mem_canonicalEdgeRegion_iff G owner edge).1 hedge |>.2
    rcases canonicalEdgeOwner_eq_self_or_reverse edge with hself | hreverse
    · rw [hself] at howner
      subst owner
      simp_all
    · rw [hreverse] at howner
      subst owner
      simp_all [reverseDirectedEdge]

/-- Every canonical leaf region is incident to at most two vertices. -/
theorem canonicalEdgeRegion_incident_card_le_two
    (G : ConnectivityGraph ι) (owner : ι × ι) :
    (edgeIncidentVertices (canonicalEdgeRegion G owner)).card ≤ 2 := by
  classical
  exact (Finset.card_le_card (canonicalEdgeRegion_incident_subset_pair G owner)).trans
    Finset.card_le_two

/-- Hence the canonical leaf construction satisfies every integer cap `r >= 2`. -/
theorem canonicalEdgeRegion_incident_card_le
    (G : ConnectivityGraph ι) {r : Nat} (hr : 2 ≤ r) (owner : ι × ι) :
    (edgeIncidentVertices (canonicalEdgeRegion G owner)).card ≤ r :=
  (canonicalEdgeRegion_incident_card_le_two G owner).trans hr

/-- The local shared boundary of a canonical leaf is also at most two. -/
theorem canonicalEdgeRegion_localSharedBoundary_card_le_two
    (G : ConnectivityGraph ι) (owner : ι × ι) :
    ((edgeIncidentVertices (canonicalEdgeRegion G owner)) ∩
      edgeDivisionSharedBoundary (canonicalEdgeRegion G)
        (canonicalEdgeRepresentatives G)).card ≤ 2 := by
  classical
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    (canonicalEdgeRegion_incident_card_le_two G owner)

/-- Canonical representatives cannot outnumber oriented graph edges. -/
theorem canonicalEdgeRepresentatives_card_le_directedEdges
    (G : ConnectivityGraph ι) :
    (canonicalEdgeRepresentatives G).card ≤ (directedEdgeFinset G).card := by
  classical
  exact Finset.card_image_le

/--
The canonical leaf data packaged existentially.  All witnesses are the explicit
definitions above; no division or cardinality conclusion is supplied as an
input hypothesis.
-/
theorem exists_explicitEdgeDivision_leaf (G : ConnectivityGraph ι)
    {r : Nat} (hr : 2 ≤ r) :
    ∃ regions : (ι × ι) → Finset (ι × ι), ∃ active : Finset (ι × ι),
      IsEdgeDivision G regions active ∧
        (∀ owner, owner ∈ active →
          (edgeIncidentVertices (regions owner)).card ≤ r) ∧
        (∀ owner, owner ∈ active →
          ((edgeIncidentVertices (regions owner)) ∩
            edgeDivisionSharedBoundary regions active).card ≤ 2) ∧
        active.card ≤ (directedEdgeFinset G).card := by
  classical
  exact ⟨canonicalEdgeRegion G, canonicalEdgeRepresentatives G,
    canonicalEdgeRegions_isEdgeDivision G,
    fun owner _ => canonicalEdgeRegion_incident_card_le G hr owner,
    fun owner _ => canonicalEdgeRegion_localSharedBoundary_card_le_two G owner,
    canonicalEdgeRepresentatives_card_le_directedEdges G⟩

/-- A one-active-region totalization, used for valid large-scale branches. -/
noncomputable def totalEdgeRegion (G : ConnectivityGraph ι) (_ : Unit) :
    Finset (ι × ι) :=
  directedEdgeFinset G

/-- The unique active index for `totalEdgeRegion`. -/
def totalEdgeActive : Finset Unit :=
  {()}

omit [DecidableEq ι] in
theorem totalEdgeRegion_isEdgeDivision (G : ConnectivityGraph ι) :
    IsEdgeDivision G (totalEdgeRegion G) totalEdgeActive := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    exact subset_rfl
  · intro i _ x y
    change (x, y) ∈ directedEdgeFinset G ↔ (y, x) ∈ directedEdgeFinset G
    rw [mem_directedEdgeFinset_iff, mem_directedEdgeFinset_iff]
    constructor
    · exact fun hxy => G.symmetric hxy
    · exact fun hyx => G.symmetric hyx
  · intro edge hedge
    refine ⟨(), ?_, ?_⟩
    · simpa [totalEdgeActive, totalEdgeRegion] using hedge
    · intro i hi
      exact Subsingleton.elim _ _

/-- Every vertex incident to the total region belongs to the ambient vertex type. -/
theorem totalEdgeRegion_incident_card_le_vertexCount (G : ConnectivityGraph ι) :
    (edgeIncidentVertices (totalEdgeRegion G ())).card ≤ Fintype.card ι := by
  classical
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The one-region wrapper meets the incident cap whenever `|V| <= r`. -/
theorem totalEdgeRegion_incident_card_le (G : ConnectivityGraph ι)
    {r : Nat} (hr : Fintype.card ι ≤ r) :
    (edgeIncidentVertices (totalEdgeRegion G ())).card ≤ r :=
  (totalEdgeRegion_incident_card_le_vertexCount G).trans hr

/-- The total wrapper has exactly one active region. -/
theorem totalEdgeActive_card : totalEdgeActive.card = 1 := by
  simp [totalEdgeActive]

/-- The exact graph-side predicate for a single undirected edge. -/
def HasSingleUndirectedEdge (G : ConnectivityGraph ι) (x y : ι) : Prop :=
  G.adjacent x y ∧
    ∀ ⦃a b : ι⦄, G.adjacent a b →
      (a = x ∧ b = y) ∨ (a = y ∧ b = x)

private theorem singleUndirectedEdge_incident_subset_pair
    (G : ConnectivityGraph ι) {x y : ι}
    (hsingle : HasSingleUndirectedEdge G x y) :
    edgeIncidentVertices (totalEdgeRegion G ()) ⊆ {x, y} := by
  classical
  intro z hz
  rcases (mem_edgeIncidentVertices_iff (totalEdgeRegion G ()) z).1 hz with
    ⟨edge, hedge, hzEndpoint⟩
  rcases edge with ⟨a, b⟩
  have hab := hsingle.2 ((mem_directedEdgeFinset_iff G a b).1 hedge)
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hzEndpoint with hza | hzb <;>
    simp_all

/-- A single-edge graph is totalized by one region with incident cap two. -/
theorem totalEdgeRegion_incident_card_le_two_of_singleEdge
    (G : ConnectivityGraph ι) {x y : ι}
    (hsingle : HasSingleUndirectedEdge G x y) :
    (edgeIncidentVertices (totalEdgeRegion G ())).card ≤ 2 := by
  classical
  exact (Finset.card_le_card
    (singleUndirectedEdge_incident_subset_pair G hsingle)).trans Finset.card_le_two

/-- A one-region division has no shared boundary. -/
theorem totalEdgeRegion_sharedBoundary_eq_empty (G : ConnectivityGraph ι) :
    edgeDivisionSharedBoundary (totalEdgeRegion G) totalEdgeActive = ∅ := by
  classical
  ext x
  simp [mem_edgeDivisionSharedBoundary_iff, totalEdgeActive]

/-- Empty regions and no active indices totalize an edgeless graph. -/
def emptyEdgeRegion (_ : Unit) : Finset (ι × ι) :=
  ∅

/-- The zero-active-region convention. -/
def emptyEdgeActive : Finset Unit :=
  ∅

omit [DecidableEq ι] in
theorem emptyEdgeRegion_isEdgeDivision (G : ConnectivityGraph ι)
    (hedgeless : directedEdgeFinset G = ∅) :
    IsEdgeDivision G (emptyEdgeRegion (ι := ι)) emptyEdgeActive := by
  classical
  simp [IsEdgeDivision, emptyEdgeActive, hedgeless]

/-- The zero-region edgeless wrapper also has empty shared boundary. -/
theorem emptyEdgeRegion_sharedBoundary_eq_empty :
    edgeDivisionSharedBoundary (emptyEdgeRegion (ι := ι)) emptyEdgeActive = ∅ := by
  classical
  ext x
  simp [mem_edgeDivisionSharedBoundary_iff, emptyEdgeActive]

/-- The edgeless wrapper has zero active regions. -/
theorem emptyEdgeActive_card : emptyEdgeActive.card = 0 := by
  simp [emptyEdgeActive]

/--
A nonempty loopless graph cannot have an edge-covering division all of whose
active regions are incident to at most one vertex.  This is the exact project
boundary excluding the nonempty-edge `r = 1` branch.
-/
theorem no_edgeDivision_with_incident_cap_one
    (G : ConnectivityGraph ι)
    {m : Type w} [DecidableEq m]
    {regions : m → Finset (ι × ι)} {active : Finset m}
    (hedges : (directedEdgeFinset G).Nonempty)
    (hDivision : IsEdgeDivision G regions active)
    (hcap : ∀ i, i ∈ active → (edgeIncidentVertices (regions i)).card ≤ 1) :
    False := by
  classical
  rcases hedges with ⟨edge, hedge⟩
  rcases edge with ⟨x, y⟩
  have hxy : G.adjacent x y := (mem_directedEdgeFinset_iff G x y).1 hedge
  have hne : x ≠ y := by
    intro hxyEq
    subst y
    exact G.loopless x hxy
  rcases hDivision.2.2 (x, y) hedge with ⟨i, ⟨hi, hiedge⟩, -⟩
  have hx : x ∈ edgeIncidentVertices (regions i) :=
    (mem_edgeIncidentVertices_iff (regions i) x).2
      ⟨(x, y), hiedge, Or.inl rfl⟩
  have hy : y ∈ edgeIncidentVertices (regions i) :=
    (mem_edgeIncidentVertices_iff (regions i) y).2
      ⟨(x, y), hiedge, Or.inr rfl⟩
  have hpair : ({x, y} : Finset ι) ⊆ edgeIncidentVertices (regions i) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · have hzy : z = y := Finset.mem_singleton.mp hz
      subst z
      exact hy
  have htwo : 2 ≤ (edgeIncidentVertices (regions i)).card := by
    have := Finset.card_le_card hpair
    simpa [hne] using this
  exact (Nat.not_succ_le_self 1) (htwo.trans (hcap i hi))

end QEC.Locality

import QEC.Locality.SeparatorProfile.StoppedPotential
/-!
# Total explicit separator-profile edge division

The final witness chooses the zero-region edgeless division, the one-region
large-scale division, or the fully constructed two-phase separator division.
All constants precede the graph and scale quantifiers.
-/

noncomputable section

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A finite edge division carrying all exact quantitative obligations. -/
structure ExplicitProfileEdgeDivision
    (G : ConnectivityGraph ι) (incidentCap localBoundaryCap activeCountCap : Nat) where
  Owner : Type
  [ownerDecidableEq : DecidableEq Owner]
  region : Owner → Finset (ι × ι)
  active : Finset Owner
  isEdgeDivision : IsEdgeDivision G region active
  incident_card_le : ∀ owner, owner ∈ active →
    (edgeIncidentVertices (region owner)).card ≤ incidentCap
  localBoundary_card_le : ∀ owner, owner ∈ active →
    (edgeIncidentVertices (region owner) ∩
      edgeDivisionSharedBoundary region active).card ≤ localBoundaryCap
  active_card_le : active.card ≤ activeCountCap

/-- Root quantitative size recursion on all oriented graph edges and all vertices. -/
private noncomputable def quantitativeProfileStoppedResult
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r) :=
  buildQuantitativeStoppedRecursion G beta exponent hProfile hexponent r hthreshold
    (directedEdgeFinset G) Finset.univ subset_rfl
    (directedEdgeFinset_reverseSymmetric G) (Finset.subset_univ _)

/-- The concrete tree component of the root quantitative construction. -/
private noncomputable def quantitativeProfileStoppedTree
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    EdgeRestrictedStoppedRecursion G r (directedEdgeFinset G) Finset.univ :=
  (quantitativeProfileStoppedResult G beta exponent hProfile hexponent r hthreshold).1

private theorem quantitativeProfileStoppedTree_stoppedAtScale
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    (quantitativeProfileStoppedTree G beta exponent hProfile hexponent r hthreshold)
      |>.StoppedAtScale :=
  (quantitativeProfileStoppedResult G beta exponent hProfile hexponent r hthreshold).2

/-- The nondegenerate two-phase branch, including exact count and local-boundary ceilings. -/
private noncomputable def quantitativeProfileEdgeDivision_of_lt
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1) (r : Nat)
    (hr : 2 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hrootLarge : r < Fintype.card ι) :
    ExplicitProfileEdgeDivision G r (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) := by
  let tree := quantitativeProfileStoppedTree G beta exponent hProfile hexponent.2 r hthreshold
  have hstopped := quantitativeProfileStoppedTree_stoppedAtScale
    G beta exponent hProfile hexponent.2 r hthreshold
  have hlower : r ≤ 4 * Fintype.card ι := by omega
  exact
    { Owner := tree.refinedOwnerType beta exponent hProfile
      region := tree.refinedEdgeRegion beta exponent hProfile
      active := tree.refinedEdgeActive beta exponent hProfile
      isEdgeDivision := tree.refinedEdgeRegions_isEdgeDivision beta exponent hProfile rfl
      incident_card_le := fun owner _ =>
        tree.refinedEdgeRegion_incident_card_le beta exponent hProfile owner
      localBoundary_card_le := fun owner _ => by
        simpa [weightedProfileBoundaryBudget] using
          tree.refinedLocalSharedBoundary_card_le beta exponent hProfile owner
      active_card_le := tree.refinedEdgeActive_card_le_uniform_ceil hstopped beta exponent
        hProfile hexponent (by omega) hthreshold hlower }

/-- The edgeless branch has no active regions and satisfies every numeric cap. -/
private noncomputable def emptyProfileEdgeDivision
    (G : ConnectivityGraph ι) (hedgeless : directedEdgeFinset G = ∅)
    (incidentCap localBoundaryCap activeCountCap : Nat) :
    ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap :=
  { Owner := Unit
    region := emptyEdgeRegion
    active := emptyEdgeActive
    isEdgeDivision := emptyEdgeRegion_isEdgeDivision G hedgeless
    incident_card_le := by simp [emptyEdgeActive]
    localBoundary_card_le := by simp [emptyEdgeActive]
    active_card_le := by simp [emptyEdgeActive] }

omit [DecidableEq ι] in
/-- A nonempty edge set certifies that the ambient finite vertex type is nonempty. -/
private theorem vertexCount_pos_of_directedEdges_nonempty
    (G : ConnectivityGraph ι) (hedges : (directedEdgeFinset G).Nonempty) :
    0 < Fintype.card ι := by
  rcases hedges with ⟨⟨x, y⟩, hxy⟩
  exact Fintype.card_pos_iff.mpr ⟨x⟩

/-- The one-region large-scale branch satisfies the same uniform count ceiling. -/
private noncomputable def totalProfileEdgeDivision
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (r : Nat) (hr : 2 ≤ r) (hcard : Fintype.card ι ≤ r)
    (hedges : (directedEdgeFinset G).Nonempty) :
    ExplicitProfileEdgeDivision G r (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) := by
  have hcountPositive : 0 <
      profileDivisionRegionConstant beta exponent * Fintype.card ι / r := by
    exact div_pos
      (mul_pos (profileDivisionRegionConstant_pos hbeta hexponent)
        (by exact_mod_cast vertexCount_pos_of_directedEdges_nonempty G hedges))
      (by exact_mod_cast (show 0 < r by omega))
  exact
    { Owner := Unit
      region := totalEdgeRegion G
      active := totalEdgeActive
      isEdgeDivision := totalEdgeRegion_isEdgeDivision G
      incident_card_le := by
        intro owner _
        simpa [show owner = () from Subsingleton.elim _ _] using
          totalEdgeRegion_incident_card_le G hcard
      localBoundary_card_le := by
        intro owner _
        have hempty := totalEdgeRegion_sharedBoundary_eq_empty G
        simp [hempty]
      active_card_le := by
        rw [totalEdgeActive_card]
        exact Nat.one_le_ceil_iff.mpr hcountPositive }

/-- Total construction for every valid scale above the graph-uniform threshold. -/
noncomputable def explicitProfileEdgeDivision
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1) (r : Nat)
    (hr : 2 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    ExplicitProfileEdgeDivision G r (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) := by
  classical
  by_cases hedgeless : directedEdgeFinset G = ∅
  · exact emptyProfileEdgeDivision G hedgeless _ _ _
  · have hedges : (directedEdgeFinset G).Nonempty := Finset.nonempty_iff_ne_empty.mpr hedgeless
    by_cases hcard : Fintype.card ι ≤ r
    · exact totalProfileEdgeDivision G beta exponent hProfile.1 hexponent r hr hcard hedges
    · exact quantitativeProfileEdgeDivision_of_lt G beta exponent hProfile hexponent r hr
        hthreshold (Nat.lt_of_not_ge hcard)

/--
Graph-uniform closure contract: constants are fixed before the vertex type,
graph, profile witness, and scale.  Isolated vertices are allowed because no
incidence-cover assumption appears in the quantifier list.
-/
theorem exists_uniform_explicitProfileEdgeDivision
    (beta exponent : ℝ) (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    ∃ threshold : Nat, ∃ countConstant : ℝ,
      threshold = profileDivisionThreshold beta exponent ∧
      countConstant = profileDivisionRegionConstant beta exponent ∧
      0 < countConstant ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        (G : ConnectivityGraph ι)
        (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
        (r : Nat), 2 ≤ r → threshold ≤ r →
          Nonempty (ExplicitProfileEdgeDivision G r
            (weightedProfileBoundaryBudget beta exponent r)
            (Nat.ceil (countConstant * Fintype.card ι / r))) := by
  refine ⟨profileDivisionThreshold beta exponent,
    profileDivisionRegionConstant beta exponent, rfl, rfl,
    profileDivisionRegionConstant_pos hbeta hexponent, ?_⟩
  intro ι instFintype instDecidableEq G hProfile r hr hthreshold
  exact ⟨explicitProfileEdgeDivision G beta exponent hProfile hexponent r hr hthreshold⟩

/-- A single undirected edge always uses one total region at every `r >= 2`. -/
theorem exists_singleEdge_profileDivision
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    {x y : ι} (hsingle : HasSingleUndirectedEdge G x y) (r : Nat) (hr : 2 ≤ r) :
    ∃ division : ExplicitProfileEdgeDivision G r
        (weightedProfileBoundaryBudget beta exponent r)
        (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)),
      division.active.card = 1 := by
  have hedges : (directedEdgeFinset G).Nonempty := by
    exact ⟨(x, y), (mem_directedEdgeFinset_iff G x y).2 hsingle.1⟩
  have hcountPositive : 0 <
      profileDivisionRegionConstant beta exponent * Fintype.card ι / r := by
    exact div_pos
      (mul_pos (profileDivisionRegionConstant_pos hbeta hexponent)
        (by exact_mod_cast vertexCount_pos_of_directedEdges_nonempty G hedges))
      (by exact_mod_cast (show 0 < r by omega))
  let division : ExplicitProfileEdgeDivision G r
      (weightedProfileBoundaryBudget beta exponent r)
      (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / r)) :=
    { Owner := Unit
      region := totalEdgeRegion G
      active := totalEdgeActive
      isEdgeDivision := totalEdgeRegion_isEdgeDivision G
      incident_card_le := by
        intro owner _
        exact (totalEdgeRegion_incident_card_le_two_of_singleEdge G hsingle).trans hr
      localBoundary_card_le := by
        intro owner _
        simp [totalEdgeRegion_sharedBoundary_eq_empty G]
      active_card_le := by
        rw [totalEdgeActive_card]
        exact Nat.one_le_ceil_iff.mpr hcountPositive }
  exact ⟨division, totalEdgeActive_card⟩

/-- Graph-isolated vertices are incident to no active edge region. -/
theorem ExplicitProfileEdgeDivision.isolated_not_mem_incident
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    {x : ι} (hx : x ∈ graphIsolatedVertices G)
    (owner : division.Owner) (howner : owner ∈ division.active) :
    x ∉ edgeIncidentVertices (division.region owner) := by
  letI : DecidableEq division.Owner := division.ownerDecidableEq
  intro hxIncident
  rcases (mem_edgeIncidentVertices_iff (division.region owner) x).1 hxIncident with
    ⟨⟨a, b⟩, habRegion, hxa | hxb⟩
  · have hab : G.adjacent a b := (mem_directedEdgeFinset_iff G a b).1
      (division.isEdgeDivision.1 owner howner habRegion)
    exact (mem_graphIsolatedVertices_iff G x).1 hx b (hxa.symm ▸ hab)
  · have hba : G.adjacent b a := G.symmetric ((mem_directedEdgeFinset_iff G a b).1
      (division.isEdgeDivision.1 owner howner habRegion))
    exact (mem_graphIsolatedVertices_iff G x).1 hx a (hxb.symm ▸ hba)

/-- The only `r = 1` completion is the edgeless branch. -/
theorem profileDivision_r_one_iff_edgeless
    (G : ConnectivityGraph ι) :
    (∃ (m : Type) (_ : DecidableEq m) (regions : m → Finset (ι × ι))
      (active : Finset m), IsEdgeDivision G regions active ∧
        ∀ owner, owner ∈ active → (edgeIncidentVertices (regions owner)).card ≤ 1) ↔
      directedEdgeFinset G = ∅ := by
  constructor
  · rintro ⟨m, inst, regions, active, hdivision, hcap⟩
    by_contra hedgeless
    exact no_edgeDivision_with_incident_cap_one G
      (Finset.nonempty_iff_ne_empty.mpr hedgeless) hdivision hcap
  · intro hedgeless
    exact ⟨Unit, inferInstance, emptyEdgeRegion, emptyEdgeActive,
      emptyEdgeRegion_isEdgeDivision G hedgeless, by simp [emptyEdgeActive]⟩

end QEC.Locality

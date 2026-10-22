import QEC.Locality.SeparatorProfile.WeightedRefinement
/-!
# Completed separator-profile edge-division composition

This module composes the size-stopped recursion with the weighted local
boundary refinement.  The first owner coordinate chooses an `r`-bounded size
leaf; the dependent second coordinate chooses a boundary-balanced edge region
inside that leaf.
-/

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Carrier stored at the terminal size-recursion path of one owner. -/
noncomputable def EdgeRestrictedStoppedRecursion.terminalCarrier
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      tree.edgeOwnerType → Finset ι
  | .leaf (vertices := vertices) _ _ _ _, _ => vertices
  | .split _ _ _ _ _ _ _ leftTree rightTree, owner =>
      match owner with
      | Sum.inl owner => leftTree.terminalCarrier owner
      | Sum.inr owner => rightTree.terminalCarrier owner

/-- Actual inherited boundary presented to the weighted refinement. -/
noncomputable def EdgeRestrictedStoppedRecursion.terminalBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) : Finset ι :=
  tree.edgeOwnerAncestors owner ∩ edgeIncidentVertices (tree.edgeRegion owner)

private theorem EdgeRestrictedStoppedRecursion.rootEdges_subset_directed
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    edges ⊆ directedEdgeFinset G := by
  cases tree with
  | leaf hsubset _ _ _ => exact hsubset
  | split hsubset _ _ _ _ _ _ _ _ => exact hsubset

private theorem EdgeRestrictedStoppedRecursion.terminal_incident_subset_carrier
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    edgeIncidentVertices (tree.edgeRegion owner) ⊆ tree.terminalCarrier owner := by
  induction tree with
  | leaf _ _ hincident _ => simpa [edgeRegion, terminalCarrier] using hincident
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner

private theorem EdgeRestrictedStoppedRecursion.terminalCarrier_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (tree.terminalCarrier owner).card ≤ r := by
  induction tree with
  | leaf _ _ _ hcard => simpa [terminalCarrier] using hcard
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner

private theorem EdgeRestrictedStoppedRecursion.terminalBoundary_subset_carrier
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    tree.terminalBoundary owner ⊆ tree.terminalCarrier owner :=
  Finset.inter_subset_right.trans (tree.terminal_incident_subset_carrier owner)

/-- Weighted local refinement constructed inside one stopped-recursion leaf. -/
private noncomputable def EdgeRestrictedStoppedRecursion.weightedRefinementAt
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.edgeOwnerType) :
    WeightedBoundaryEdgeRecursion G r (weightedSpineSeparatorBudget beta exponent r)
      (tree.edgeRegion owner) (tree.terminalCarrier owner) (tree.terminalBoundary owner) :=
  buildWeightedBoundaryEdgeRecursion G beta exponent hProfile r
    (tree.edgeRegion owner) (tree.terminalCarrier owner) (tree.terminalBoundary owner)
    ((tree.edgeRegion_subset owner).trans tree.rootEdges_subset_directed)
    (tree.edgeRegion_reverse owner)
    (tree.terminal_incident_subset_carrier owner)
    (tree.terminalBoundary_subset_carrier owner)
    (tree.terminalCarrier_card_le owner)

/-- Dependent two-level owner of the fully refined division. -/
def EdgeRestrictedStoppedRecursion.refinedOwnerType
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) : Type :=
  Sigma fun owner : tree.edgeOwnerType =>
    (tree.weightedRefinementAt beta exponent hProfile owner).edgeOwnerType

noncomputable instance EdgeRestrictedStoppedRecursion.refinedOwnerFintype
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    Fintype (tree.refinedOwnerType beta exponent hProfile) := by
  unfold refinedOwnerType
  infer_instance

noncomputable instance EdgeRestrictedStoppedRecursion.refinedOwnerDecidableEq
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    DecidableEq (tree.refinedOwnerType beta exponent hProfile) := by
  unfold refinedOwnerType
  infer_instance

/-- Final edge region selected by a two-level refined owner. -/
noncomputable def EdgeRestrictedStoppedRecursion.refinedEdgeRegion
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) : Finset (ι × ι) :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion owner.2

/-- Active final owners are exactly those carrying a nonempty edge region. -/
noncomputable def EdgeRestrictedStoppedRecursion.refinedEdgeActive
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    Finset (tree.refinedOwnerType beta exponent hProfile) := by
  classical
  exact Finset.univ.filter fun owner =>
    (tree.refinedEdgeRegion beta exponent hProfile owner).Nonempty

private theorem EdgeRestrictedStoppedRecursion.refinedEdgeRegion_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    tree.refinedEdgeRegion beta exponent hProfile owner ⊆ edges :=
  ((tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion_subset owner.2).trans
    (tree.edgeRegion_subset owner.1)

private theorem EdgeRestrictedStoppedRecursion.refinedEdgeRegion_reverse
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) (x y : ι) :
    (x, y) ∈ tree.refinedEdgeRegion beta exponent hProfile owner ↔
      (y, x) ∈ tree.refinedEdgeRegion beta exponent hProfile owner :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion_reverse owner.2 x y

theorem EdgeRestrictedStoppedRecursion.refinedEdgeRegion_incident_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner)).card ≤ r :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).edgeRegion_incident_card_le owner.2

private theorem EdgeRestrictedStoppedRecursion.existsUnique_refinedEdgeOwner
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.refinedOwnerType beta exponent hProfile,
      edge ∈ tree.refinedEdgeRegion beta exponent hProfile owner := by
  classical
  rcases tree.existsUnique_edgeOwner edge hedge with ⟨outer, houter, houterUnique⟩
  rcases (tree.weightedRefinementAt beta exponent hProfile outer).existsUnique_edgeOwner
      edge houter with ⟨inner, hinner, hinnerUnique⟩
  refine ⟨⟨outer, inner⟩, hinner, ?_⟩
  intro candidate hcandidate
  have hcandOuter : edge ∈ tree.edgeRegion candidate.1 :=
    (tree.weightedRefinementAt beta exponent hProfile candidate.1).edgeRegion_subset
      candidate.2 hcandidate
  have houterEq : candidate.1 = outer := houterUnique candidate.1 hcandOuter
  rcases candidate with ⟨candidateOuter, candidateInner⟩
  dsimp at houterEq
  subst candidateOuter
  have hinnerEq : candidateInner = inner := hinnerUnique candidateInner hcandidate
  subst candidateInner
  rfl

theorem EdgeRestrictedStoppedRecursion.refinedEdgeRegions_isEdgeDivision
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hroot : edges = directedEdgeFinset G) :
    IsEdgeDivision G (tree.refinedEdgeRegion beta exponent hProfile)
      (tree.refinedEdgeActive beta exponent hProfile) := by
  refine ⟨?_, ?_, ?_⟩
  · intro owner _ edge hedge
    rw [← hroot]
    exact tree.refinedEdgeRegion_subset beta exponent hProfile owner hedge
  · intro owner _ x y
    exact tree.refinedEdgeRegion_reverse beta exponent hProfile owner x y
  · intro edge hedge
    have hedgeRoot : edge ∈ edges := by simpa [hroot] using hedge
    rcases tree.existsUnique_refinedEdgeOwner beta exponent hProfile edge hedgeRoot with
      ⟨owner, howner, hunique⟩
    refine ⟨owner, ⟨?_, howner⟩, ?_⟩
    · simp only [refinedEdgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨edge, howner⟩
    · intro candidate hcandidate
      exact hunique candidate hcandidate.2

/-- Leaf boundary resource of a fully refined owner. -/
private noncomputable def EdgeRestrictedStoppedRecursion.refinedOwnerBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) : Finset ι :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).ownerBoundary owner.2

private theorem EdgeRestrictedStoppedRecursion.refinedOwnerBoundary_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (tree.refinedOwnerBoundary beta exponent hProfile owner).card ≤
      6 * weightedSpineSeparatorBudget beta exponent r :=
  (tree.weightedRefinementAt beta exponent hProfile owner.1).ownerBoundary_card_le owner.2

/-- The two-level construction charges every actual shared vertex to its final leaf budget. -/
private theorem EdgeRestrictedStoppedRecursion.refinedLocalSharedBoundary_subset_ownerBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner) ∩
        edgeDivisionSharedBoundary (tree.refinedEdgeRegion beta exponent hProfile)
          (tree.refinedEdgeActive beta exponent hProfile) ⊆
      tree.refinedOwnerBoundary beta exponent hProfile owner := by
  classical
  intro x hx
  have hxOwner : x ∈ edgeIncidentVertices
      (tree.refinedEdgeRegion beta exponent hProfile owner) :=
    (Finset.mem_inter.mp hx).1
  have hownerNonempty : (tree.refinedEdgeRegion beta exponent hProfile owner).Nonempty := by
    rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
    exact ⟨edge, hedge⟩
  have hownerActive : owner ∈ tree.refinedEdgeActive beta exponent hProfile := by
    simp only [refinedEdgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hownerNonempty
  rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
    ⟨i, hi, j, hj, hij, hxi, hxj⟩
  have hcandidate : ∃ candidate : tree.refinedOwnerType beta exponent hProfile,
      candidate ≠ owner ∧ candidate ∈ tree.refinedEdgeActive beta exponent hProfile ∧
        x ∈ edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile candidate) := by
    by_cases hiOwner : i = owner
    · refine ⟨j, ?_, hj, hxj⟩
      intro hjOwner
      exact hij (hiOwner.trans hjOwner.symm)
    · exact ⟨i, hiOwner, hi, hxi⟩
  rcases hcandidate with ⟨candidate, hne, hcandidateActive, hxCandidate⟩
  rcases owner with ⟨outer, inner⟩
  rcases candidate with ⟨candidateOuter, candidateInner⟩
  by_cases hsameOuter : candidateOuter = outer
  · subst candidateOuter
    have hinnerNe : candidateInner ≠ inner := by
      intro heq
      subst candidateInner
      exact hne rfl
    have hinnerActive : inner ∈
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeActive := by
      simp only [WeightedBoundaryEdgeRecursion.edgeActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hownerNonempty
    have hcandidateInnerActive : candidateInner ∈
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeActive := by
      have hnonempty := (@Finset.mem_filter _ _
        (fun _ => Finset.decidableNonempty) _ _).mp hcandidateActive
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hnonempty.2⟩
    have hxWeightedShared : x ∈ edgeDivisionSharedBoundary
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeRegion
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeActive :=
      (mem_edgeDivisionSharedBoundary_iff _ _ x).2
        ⟨inner, hinnerActive, candidateInner, hcandidateInnerActive, Ne.symm hinnerNe,
          hxOwner, hxCandidate⟩
    exact (tree.weightedRefinementAt beta exponent hProfile outer)
      |>.localSharedBoundary_subset_ownerBoundary inner
        (Finset.mem_inter.mpr ⟨hxOwner, hxWeightedShared⟩)
  · have hxOuter : x ∈ edgeIncidentVertices (tree.edgeRegion outer) := by
      exact (edgeIncidentVertices_mono
        ((tree.weightedRefinementAt beta exponent hProfile outer).edgeRegion_subset inner))
          hxOwner
    have hxCandidateOuter : x ∈ edgeIncidentVertices (tree.edgeRegion candidateOuter) := by
      exact (edgeIncidentVertices_mono
        ((tree.weightedRefinementAt beta exponent hProfile candidateOuter).edgeRegion_subset
          candidateInner)) hxCandidate
    have houterActive : outer ∈ tree.edgeActive := by
      simp only [EdgeRestrictedStoppedRecursion.edgeActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases (mem_edgeIncidentVertices_iff _ x).1 hxOuter with ⟨edge, hedge, _⟩
      exact ⟨edge, hedge⟩
    have hcandidateOuterActive : candidateOuter ∈ tree.edgeActive := by
      simp only [EdgeRestrictedStoppedRecursion.edgeActive, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rcases (mem_edgeIncidentVertices_iff _ x).1 hxCandidateOuter with
        ⟨edge, hedge, _⟩
      exact ⟨edge, hedge⟩
    have hxStoppedShared : x ∈ edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive :=
      (mem_edgeDivisionSharedBoundary_iff _ _ x).2
        ⟨outer, houterActive, candidateOuter, hcandidateOuterActive,
          Ne.symm hsameOuter, hxOuter, hxCandidateOuter⟩
    have hxAncestor : x ∈ tree.edgeOwnerAncestors outer :=
      tree.localSharedBoundary_subset_ancestors outer
        (Finset.mem_inter.mpr ⟨hxOuter, hxStoppedShared⟩)
    have hxTerminalBoundary : x ∈ tree.terminalBoundary outer :=
      Finset.mem_inter.mpr ⟨hxAncestor, hxOuter⟩
    exact (tree.weightedRefinementAt beta exponent hProfile outer)
      |>.initialBoundary_incident_subset_ownerBoundary inner
        (Finset.mem_inter.mpr ⟨hxTerminalBoundary, hxOwner⟩)

theorem EdgeRestrictedStoppedRecursion.refinedLocalSharedBoundary_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (owner : tree.refinedOwnerType beta exponent hProfile) :
    (edgeIncidentVertices (tree.refinedEdgeRegion beta exponent hProfile owner) ∩
      edgeDivisionSharedBoundary (tree.refinedEdgeRegion beta exponent hProfile)
        (tree.refinedEdgeActive beta exponent hProfile)).card ≤
      6 * weightedSpineSeparatorBudget beta exponent r :=
  (Finset.card_le_card
    (tree.refinedLocalSharedBoundary_subset_ownerBoundary beta exponent hProfile owner)).trans
      (tree.refinedOwnerBoundary_card_le beta exponent hProfile owner)

/-- Total actual inherited-boundary mass over all terminal size leaves. -/
noncomputable def EdgeRestrictedStoppedRecursion.terminalBoundaryMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) : Nat :=
  ∑ owner : tree.edgeOwnerType, (tree.terminalBoundary owner).card

private theorem EdgeRestrictedStoppedRecursion.refinedOwnerType_card_mul_budget_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    Fintype.card (tree.refinedOwnerType beta exponent hProfile) *
        weightedSpineSeparatorBudget beta exponent r ≤
      tree.terminalOwnerCount * weightedSpineSeparatorBudget beta exponent r +
        2 * tree.terminalBoundaryMass := by
  classical
  let budget := weightedSpineSeparatorBudget beta exponent r
  calc
    Fintype.card (tree.refinedOwnerType beta exponent hProfile) * budget =
        (∑ outer : tree.edgeOwnerType,
          Fintype.card (tree.weightedRefinementAt beta exponent hProfile outer).edgeOwnerType) *
          budget := by
      change Fintype.card (Sigma fun outer : tree.edgeOwnerType =>
        (tree.weightedRefinementAt beta exponent hProfile outer).edgeOwnerType) * budget = _
      rw [Fintype.card_sigma]
    _ = ∑ outer : tree.edgeOwnerType,
        Fintype.card (tree.weightedRefinementAt beta exponent hProfile outer).edgeOwnerType *
          budget := Finset.sum_mul _ _ _
    _ ≤ ∑ outer : tree.edgeOwnerType,
        (budget + 2 * (tree.terminalBoundary outer).card) := by
      apply Finset.sum_le_sum
      intro outer _
      rw [(tree.weightedRefinementAt beta exponent hProfile outer)
        |>.edgeOwnerType_card_eq_terminalOwnerCount]
      exact (tree.weightedRefinementAt beta exponent hProfile outer)
        |>.terminalOwnerCount_mul_budget_le
    _ = Fintype.card tree.edgeOwnerType * budget + 2 * tree.terminalBoundaryMass := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.cast_id, ← Finset.mul_sum, terminalBoundaryMass, Nat.mul_comm]
    _ = tree.terminalOwnerCount * budget + 2 * tree.terminalBoundaryMass := by
      rw [tree.edgeOwnerType_card_eq_terminalOwnerCount]

theorem EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_mul_budget_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent) :
    (tree.refinedEdgeActive beta exponent hProfile).card *
        weightedSpineSeparatorBudget beta exponent r ≤
      tree.terminalOwnerCount * weightedSpineSeparatorBudget beta exponent r +
        2 * tree.terminalBoundaryMass := by
  exact (Nat.mul_le_mul_right _
    (show (tree.refinedEdgeActive beta exponent hProfile).card ≤
        Fintype.card (tree.refinedOwnerType beta exponent hProfile) by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _))).trans
    (tree.refinedOwnerType_card_mul_budget_le beta exponent hProfile)

end QEC.Locality

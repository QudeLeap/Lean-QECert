import QEC.Locality.SeparatorProfile.DivisionPotential
import QEC.Locality.SeparatorProfile.Completion
/-!
# Quantitative potential for the size-stopped separator recursion

This module rebuilds the ordinary size recursion together with evidence that
every split occurs strictly above the requested terminal scale.  The retained
separator potential then amortizes the complete separator ledger without any
assumed region-count or boundary hypothesis.
-/

noncomputable section

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Every internal node of a genuinely stopped recursion lies above scale `r`. -/
def EdgeRestrictedStoppedRecursion.StoppedAtScale
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Prop
  | .leaf _ _ _ _ => True
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      r < vertices.card ∧ leftTree.StoppedAtScale ∧ rightTree.StoppedAtScale

/-- Disjointness of one raw side and the deleted separator. -/
private theorem profileSplit_left_disjoint_separator
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    Disjoint left separator := by
  apply Finset.disjoint_left.mpr
  intro x hxLeft hxSeparator
  have hxDiff : x ∈ vertices \ separator := by
    rw [← hpartition.2.1]
    exact Finset.mem_union_left _ hxLeft
  exact (Finset.mem_sdiff.mp hxDiff).2 hxSeparator

/-- Disjointness of the other raw side and the deleted separator. -/
private theorem profileSplit_right_disjoint_separator
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    Disjoint right separator := by
  apply Finset.disjoint_left.mpr
  intro x hxRight hxSeparator
  have hxDiff : x ∈ vertices \ separator := by
    rw [← hpartition.2.1]
    exact Finset.mem_union_right _ hxRight
  exact (Finset.mem_sdiff.mp hxDiff).2 hxSeparator

/-- Retaining the separator duplicates exactly its cardinality. -/
private theorem profileSplit_child_carrier_card_sum
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    (left ∪ separator).card + (right ∪ separator).card =
      vertices.card + separator.card := by
  have hleftSeparator := profileSplit_left_disjoint_separator hpartition
  have hrightSeparator := profileSplit_right_disjoint_separator hpartition
  have hleftRight : Disjoint left right := hpartition.2.2.1
  have hseparatorRemainder : Disjoint separator (vertices \ separator) := by
    exact Finset.disjoint_left.mpr fun _ hs hr => (Finset.mem_sdiff.mp hr).2 hs
  have hseparatorCard : separator.card + (left ∪ right).card = vertices.card := by
    calc
      separator.card + (left ∪ right).card =
          separator.card + (vertices \ separator).card := by rw [← hpartition.2.1]
      _ = (separator ∪ (vertices \ separator)).card :=
        (Finset.card_union_of_disjoint hseparatorRemainder).symm
      _ = vertices.card := by rw [Finset.union_sdiff_of_subset hpartition.1]
  rw [Finset.card_union_of_disjoint hleftRight] at hseparatorCard
  rw [Finset.card_union_of_disjoint hleftSeparator,
    Finset.card_union_of_disjoint hrightSeparator]
  omega

/-- Twelfth-scale balance places the retained left carrier in `[1/4,3/4]` of total mass. -/
private theorem profileSplit_left_carrier_interval
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    vertices.card + separator.card ≤ 4 * (left ∪ separator).card ∧
      4 * (left ∪ separator).card ≤ 3 * (vertices.card + separator.card) := by
  have hleftSeparator := profileSplit_left_disjoint_separator hpartition
  have hrightSeparator := profileSplit_right_disjoint_separator hpartition
  have hleftRight : Disjoint left right := hpartition.2.2.1
  have hseparatorRemainder : Disjoint separator (vertices \ separator) := by
    exact Finset.disjoint_left.mpr fun _ hs hr => (Finset.mem_sdiff.mp hr).2 hs
  have hcard : separator.card + left.card + right.card = vertices.card := by
    calc
      separator.card + left.card + right.card =
          separator.card + (left ∪ right).card := by
        rw [Finset.card_union_of_disjoint hleftRight, Nat.add_assoc]
      _ = separator.card + (vertices \ separator).card := by rw [← hpartition.2.1]
      _ = (separator ∪ (vertices \ separator)).card :=
        (Finset.card_union_of_disjoint hseparatorRemainder).symm
      _ = vertices.card := by rw [Finset.union_sdiff_of_subset hpartition.1]
  rw [Finset.card_union_of_disjoint hleftSeparator]
  have hleftBalanced := hpartition.2.2.2.1
  have hrightBalanced := hpartition.2.2.2.2.1
  constructor <;> omega

/-- The retained right carrier obeys the same complementary interval. -/
private theorem profileSplit_right_carrier_interval
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    vertices.card + separator.card ≤ 4 * (right ∪ separator).card ∧
      4 * (right ∪ separator).card ≤ 3 * (vertices.card + separator.card) := by
  have hsum := profileSplit_child_carrier_card_sum hpartition
  have hleft := profileSplit_left_carrier_interval hpartition
  omega

/-- Construct the stopped tree together with its exact stopping invariant. -/
noncomputable def buildQuantitativeStoppedRecursion
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (edges : Finset (ι × ι)) (vertices : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices) :
    { tree : EdgeRestrictedStoppedRecursion G r edges vertices // tree.StoppedAtScale } := by
  classical
  by_cases hterminal : vertices.card ≤ r
  · exact ⟨.leaf hsubset hsymmetric hincident hterminal, trivial⟩
  · let H := edgeRestrictedGraph G edges
    let left := measuredTwoThirdsLeft H vertices
    let separator := measuredTwoThirdsSeparator H vertices
    let right := measuredTwoThirdsRight H vertices
    have hlarge : r < vertices.card := Nat.lt_of_not_ge hterminal
    have hseparatorThreshold : profileSeparatorThreshold beta exponent ≤ r :=
      (Nat.le_max_left _ _).trans hthreshold
    have hscale : profileSeparatorThreshold beta exponent ≤ vertices.card :=
      hseparatorThreshold.trans hlarge.le
    have hvertices : 1 ≤ vertices.card := by omega
    have hpartition : TwoThirdsBalancedPartitionAfterDeleting H vertices left separator right :=
      measuredTwoThirdsSplit_spec H vertices
    have hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize H vertices :=
      (measuredTwoThirdsSeparator_spec H vertices).2.2
    have hprofileH := hProfile.edgeRestricted G beta exponent edges
    have hleftRaw : left.card + separator.card < vertices.card :=
      profileSeparator_child_card_lt H beta exponent hprofileH hexponent
        hvertices hscale hminimum hpartition.2.2.2.1
    have hrightRaw : right.card + separator.card < vertices.card :=
      profileSeparator_child_card_lt H beta exponent hprofileH hexponent
        hvertices hscale hminimum hpartition.2.2.2.2.1
    have hleft : (left ∪ separator).card < vertices.card :=
      (Finset.card_union_le left separator).trans_lt hleftRaw
    have hright : (right ∪ separator).card < vertices.card :=
      (Finset.card_union_le right separator).trans_lt hrightRaw
    let leftResult := buildQuantitativeStoppedRecursion G beta exponent hProfile hexponent r
      hthreshold (separatorLeftEdges edges left) (left ∪ separator)
      (separatorLeftEdges_subset_directed G edges left hsubset)
      (separatorLeftEdges_reverse edges left hsymmetric)
      (separatorLeftEdges_incident_subset G edges vertices left separator right
        hsubset hsymmetric hincident hpartition)
    let rightResult := buildQuantitativeStoppedRecursion G beta exponent hProfile hexponent r
      hthreshold (separatorRightEdges edges left) (right ∪ separator)
      (separatorRightEdges_subset_directed G edges left hsubset)
      (separatorRightEdges_reverse edges left hsymmetric)
      (separatorRightEdges_incident_subset G edges vertices left separator right
        hsubset hsymmetric hincident hpartition)
    exact ⟨.split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftResult.1 rightResult.1, hlarge, leftResult.2, rightResult.2⟩
termination_by vertices.card
decreasing_by
  · exact hleft
  · exact hright

/-- Sum of separator cardinalities over the size-recursion tree. -/
private noncomputable def EdgeRestrictedStoppedRecursion.separatorCharge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Nat
  | .leaf _ _ _ _ => 0
  | .split (separator := separator) _ _ _ _ _ _ _ leftTree rightTree =>
      separator.card + leftTree.separatorCharge + rightTree.separatorCharge

/-- Sum of retained potentials over all terminal size leaves. -/
private noncomputable def EdgeRestrictedStoppedRecursion.terminalPotentialMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (beta exponent : ℝ) :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) → ℝ
  | .leaf _ _ _ _ => profileDivisionPotential beta exponent r vertices.card
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      leftTree.terminalPotentialMass beta exponent +
        rightTree.terminalPotentialMass beta exponent

/-- Total retained carrier cardinality over terminal size leaves. -/
private noncomputable def EdgeRestrictedStoppedRecursion.terminalCarrierMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Nat
  | .leaf _ _ _ _ => vertices.card
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      leftTree.terminalCarrierMass + rightTree.terminalCarrierMass

/-- The retained potential pays three copies of every size separator. -/
private theorem EdgeRestrictedStoppedRecursion.potential_amortizes_separatorCharge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (3 * tree.separatorCharge : Nat) + tree.terminalPotentialMass beta exponent ≤
      profileDivisionPotential beta exponent r vertices.card := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      simp [separatorCharge, terminalPotentialMass]
  | @split edges vertices left separator right hsubset hsymmetric hincident hpartition
      hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      rcases hstopped with ⟨hlarge, hleftStopped, hrightStopped⟩
      have hsum := profileSplit_child_carrier_card_sum hpartition
      have hleftInterval := profileSplit_left_carrier_interval hpartition
      have hrightInterval := profileSplit_right_carrier_interval hpartition
      have hleftLower : r ≤ 4 * (left ∪ separator).card := by omega
      have hrightLower : r ≤ 4 * (right ∪ separator).card := by omega
      have hleftBound := ihLeft hleftStopped hleftLower
      have hrightBound := ihRight hrightStopped hrightLower
      have hvertices : 1 ≤ vertices.card := by omega
      have hseparatorReal : (separator.card : ℝ) ≤
          beta * (vertices.card : ℝ) ^ exponent :=
        minimumSeparator_card_real_le_profilePower
          (edgeRestrictedGraph G edges) beta exponent
          (hProfile.edgeRestricted G beta exponent edges) vertices separator
          hvertices hminimum
      have hscale := profileDivisionPotential_linearScale_le_one_of_threshold
        hProfile.1 hexponent hthreshold
      have hsplit := profileDivisionPotential_split
        (beta := beta) (exponent := exponent) (r := r)
        (parent := vertices.card) (left := (left ∪ separator).card)
        (right := (right ∪ separator).card) (separator := separator.card)
        (zero_le_one.trans hProfile.1) hexponent hr (by omega) hsum
        hleftInterval.1 hleftInterval.2 hseparatorReal hscale
      simp only [separatorCharge, terminalPotentialMass]
      push_cast at hleftBound hrightBound ⊢
      nlinarith

/-- Terminal leaf potentials are nonnegative under the inherited quarter-scale invariant. -/
private theorem EdgeRestrictedStoppedRecursion.terminalPotentialMass_nonneg
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ) (hbeta : 0 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hlower : r ≤ 4 * vertices.card) :
    0 ≤ tree.terminalPotentialMass beta exponent := by
  induction tree with
  | leaf _ _ _ _ =>
      simpa [terminalPotentialMass] using
        profileDivisionPotential_nonneg hbeta hexponent hr hlower
  | @split _ vertices left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      rcases hstopped with ⟨hlarge, hleftStopped, hrightStopped⟩
      have hleftInterval := profileSplit_left_carrier_interval hpartition
      have hrightInterval := profileSplit_right_carrier_interval hpartition
      have hleftLower : r ≤ 4 * (left ∪ separator).card := by omega
      have hrightLower : r ≤ 4 * (right ∪ separator).card := by omega
      exact add_nonneg (ihLeft hleftStopped hleftLower) (ihRight hrightStopped hrightLower)

/-- The size-separator ledger is bounded by the root retained potential. -/
private theorem EdgeRestrictedStoppedRecursion.separatorCharge_le_potential
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (3 * tree.separatorCharge : Nat) ≤
      profileDivisionPotential beta exponent r vertices.card := by
  have hfull := tree.potential_amortizes_separatorCharge hstopped beta exponent
    hProfile hexponent hr hthreshold hlower
  have hterminal := tree.terminalPotentialMass_nonneg hstopped beta exponent
    (zero_le_one.trans hProfile.1) hexponent hr hlower
  norm_cast at hfull ⊢
  linarith

/-- Retained terminal carrier mass is root mass plus at most one copy of every separator. -/
private theorem EdgeRestrictedStoppedRecursion.terminalCarrierMass_le_root_add_charge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    tree.terminalCarrierMass ≤ vertices.card + tree.separatorCharge := by
  induction tree with
  | leaf _ _ _ _ => simp [terminalCarrierMass, separatorCharge]
  | @split _ vertices left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      have hsum := profileSplit_child_carrier_card_sum hpartition
      simp only [terminalCarrierMass, separatorCharge]
      omega

/-- In a nondegenerate stopped tree, every terminal carrier has more than one quarter scale. -/
private theorem EdgeRestrictedStoppedRecursion.terminalOwnerCount_mul_scale_le_four_carrierMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale) (hlower : r ≤ 4 * vertices.card) :
    tree.terminalOwnerCount * r ≤ 4 * tree.terminalCarrierMass := by
  induction tree with
  | leaf _ _ _ _ => simpa [terminalOwnerCount, terminalCarrierMass] using hlower
  | @split _ vertices left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      rcases hstopped with ⟨hlarge, hleftStopped, hrightStopped⟩
      have hleftInterval := profileSplit_left_carrier_interval hpartition
      have hrightInterval := profileSplit_right_carrier_interval hpartition
      have hleftLower : r ≤ 4 * (left ∪ separator).card := by omega
      have hrightLower : r ≤ 4 * (right ∪ separator).card := by omega
      have hl := ihLeft hleftStopped hleftLower
      have hr := ihRight hrightStopped hrightLower
      simp only [terminalOwnerCount, terminalCarrierMass]
      rw [Nat.add_mul, Nat.mul_add]
      omega

/-- Boundary inherited by the left child of the retained size recursion. -/
private noncomputable def leftRefinedBoundary
    (boundary left separator : Finset ι) : Finset ι :=
  separator ∪ (boundary ∩ (left ∪ separator))

/-- Boundary inherited by the right child of the retained size recursion. -/
private noncomputable def rightRefinedBoundary
    (boundary right separator : Finset ι) : Finset ι :=
  separator ∪ (boundary ∩ (right ∪ separator))

omit [Fintype ι] in
private theorem separator_subset_leftRefinedBoundary
    (boundary left separator : Finset ι) :
    separator ⊆ leftRefinedBoundary boundary left separator :=
  Finset.subset_union_left

omit [Fintype ι] in
private theorem separator_subset_rightRefinedBoundary
    (boundary right separator : Finset ι) :
    separator ⊆ rightRefinedBoundary boundary right separator :=
  Finset.subset_union_left

/-- Boundary presented to one terminal size leaf after exact separator propagation. -/
private noncomputable def EdgeRestrictedStoppedRecursion.propagatedBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      Finset ι → tree.edgeOwnerType → Finset ι
  | .leaf (edges := edges) _ _ _ _, boundary, _ =>
      boundary ∩ edgeIncidentVertices edges
  | .split (left := left) (separator := separator) (right := right)
      _ _ _ _ _ _ _ leftTree rightTree, boundary, owner =>
      match owner with
      | Sum.inl owner =>
          leftTree.propagatedBoundary (leftRefinedBoundary boundary left separator) owner
      | Sum.inr owner =>
          rightTree.propagatedBoundary (rightRefinedBoundary boundary right separator) owner

/-- Recursive total of all propagated terminal boundaries. -/
private noncomputable def EdgeRestrictedStoppedRecursion.propagatedBoundaryMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Finset ι → Nat
  | .leaf (edges := edges) _ _ _ _, boundary =>
      (boundary ∩ edgeIncidentVertices edges).card
  | .split (left := left) (separator := separator) (right := right)
      _ _ _ _ _ _ _ leftTree rightTree, boundary =>
      leftTree.propagatedBoundaryMass (leftRefinedBoundary boundary left separator) +
        rightTree.propagatedBoundaryMass (rightRefinedBoundary boundary right separator)

omit [Fintype ι] in
/-- One separator split increases total propagated boundary by at most three copies. -/
private theorem profileSplit_child_boundary_card_sum_le
    (boundary left separator right : Finset ι) (hleftRight : Disjoint left right) :
    (leftRefinedBoundary boundary left separator).card +
        (rightRefinedBoundary boundary right separator).card ≤
      boundary.card + 3 * separator.card := by
  let leftPart := boundary ∩ (left ∪ separator)
  let rightPart := boundary ∩ (right ∪ separator)
  have hinter : leftPart ∩ rightPart ⊆ boundary ∩ separator := by
    intro x hx
    have hxLeft := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
    have hxRight := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).2
    have hxBoundary := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
    rcases Finset.mem_union.mp hxLeft with hxLeft | hxSeparator
    · rcases Finset.mem_union.mp hxRight with hxRight | hxSeparator
      · exact False.elim ((Finset.disjoint_left.mp hleftRight) hxLeft hxRight)
      · exact Finset.mem_inter.mpr ⟨hxBoundary, hxSeparator⟩
    · exact Finset.mem_inter.mpr ⟨hxBoundary, hxSeparator⟩
  have hunion : leftPart ∪ rightPart ⊆ boundary :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hintersection :
      (boundary ∩ (left ∪ separator)).card +
          (boundary ∩ (right ∪ separator)).card ≤
        boundary.card + separator.card := by
    calc
      _ = (leftPart ∪ rightPart).card + (leftPart ∩ rightPart).card := by
        dsimp [leftPart, rightPart]
        exact (Finset.card_union_add_card_inter _ _).symm
      _ ≤ boundary.card + (boundary ∩ separator).card :=
        Nat.add_le_add (Finset.card_le_card hunion) (Finset.card_le_card hinter)
      _ ≤ boundary.card + separator.card :=
        Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
  simp only [leftRefinedBoundary, rightRefinedBoundary]
  have hleft := Finset.card_union_le separator (boundary ∩ (left ∪ separator))
  have hright := Finset.card_union_le separator (boundary ∩ (right ∪ separator))
  omega

/-- Propagated boundary mass is root boundary plus three times the size-separator ledger. -/
private theorem EdgeRestrictedStoppedRecursion.propagatedBoundaryMass_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) (boundary : Finset ι) :
    tree.propagatedBoundaryMass boundary ≤ boundary.card + 3 * tree.separatorCharge := by
  induction tree generalizing boundary with
  | leaf _ _ _ _ =>
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp [separatorCharge])
  | @split _ _ left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      have hchildren := profileSplit_child_boundary_card_sum_le boundary left separator right
        hpartition.2.2.1
      have hl := ihLeft (leftRefinedBoundary boundary left separator)
      have hr := ihRight (rightRefinedBoundary boundary right separator)
      simp only [propagatedBoundaryMass, separatorCharge]
      omega

/-- Propagated boundaries are exactly enumerated by the terminal owner type. -/
private theorem EdgeRestrictedStoppedRecursion.sum_propagatedBoundary_card_eq_mass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) (boundary : Finset ι) :
    (∑ owner : tree.edgeOwnerType, (tree.propagatedBoundary boundary owner).card) =
      tree.propagatedBoundaryMass boundary := by
  classical
  induction tree generalizing boundary with
  | @leaf edges vertices hsubset hsymmetric hincident hcard =>
      let root := EdgeRestrictedStoppedRecursion.leaf hsubset hsymmetric hincident hcard
      have hFintype : EdgeRestrictedStoppedRecursion.edgeOwnerFintype root =
          (inferInstance : Fintype Unit) := Subsingleton.elim _ _
      rw [hFintype]
      simp [edgeOwnerType, propagatedBoundary, propagatedBoundaryMass]
  | @split edges vertices left separator right hsubset hsymmetric hincident hpartition
      hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      let root := EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident hpartition
        hminimum hleft hright leftTree rightTree
      let sumFintype : Fintype (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType) :=
        instFintypeSum _ _
      have hFintype : EdgeRestrictedStoppedRecursion.edgeOwnerFintype root = sumFintype :=
        Subsingleton.elim _ _
      rw [hFintype]
      simp [edgeOwnerType, propagatedBoundary, propagatedBoundaryMass,
        Fintype.sum_sum_type, ihLeft, ihRight]

/-- Ancestor separators and an inherited root boundary are contained in propagation. -/
private theorem EdgeRestrictedStoppedRecursion.inheritedAncestorBoundary_subset_propagated
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (boundary : Finset ι) (owner : tree.edgeOwnerType) :
    (boundary ∪ tree.edgeOwnerAncestors owner) ∩
        edgeIncidentVertices (tree.edgeRegion owner) ⊆
      tree.propagatedBoundary boundary owner := by
  classical
  induction tree generalizing boundary with
  | leaf _ _ _ _ => simp [edgeOwnerAncestors, edgeRegion, propagatedBoundary]
  | @split edges vertices left separator right hsubset hsymmetric hincident hpartition
      hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner =>
          intro x hx
          have hxIncident : x ∈ edgeIncidentVertices (leftTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
          have hxCarrier : x ∈ left ∪ separator := by
            exact separatorLeftEdges_incident_subset G edges vertices left separator right
              hsubset hsymmetric hincident hpartition
              (edgeIncidentVertices_mono (leftTree.edgeRegion_subset owner) hxIncident)
          have hxUnion : x ∈ leftRefinedBoundary boundary left separator ∪
              leftTree.edgeOwnerAncestors owner := by
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with
              hxBoundary | hxAncestor
            · have hxChildBoundary : x ∈ leftRefinedBoundary boundary left separator := by
                simp only [leftRefinedBoundary, Finset.mem_union]
                exact Or.inr (Finset.mem_inter.mpr ⟨hxBoundary, hxCarrier⟩)
              exact Finset.mem_union_left _ hxChildBoundary
            · rcases Finset.mem_union.mp hxAncestor with hxSeparator | hxChildAncestor
              · exact Finset.mem_union_left _
                  (separator_subset_leftRefinedBoundary boundary left separator hxSeparator)
              · exact Finset.mem_union_right _ hxChildAncestor
          exact ihLeft (leftRefinedBoundary boundary left separator) owner
            (Finset.mem_inter.mpr ⟨hxUnion, hxIncident⟩)
      | inr owner =>
          intro x hx
          have hxIncident : x ∈ edgeIncidentVertices (rightTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
          have hxCarrier : x ∈ right ∪ separator := by
            exact separatorRightEdges_incident_subset G edges vertices left separator right
              hsubset hsymmetric hincident hpartition
              (edgeIncidentVertices_mono (rightTree.edgeRegion_subset owner) hxIncident)
          have hxUnion : x ∈ rightRefinedBoundary boundary right separator ∪
              rightTree.edgeOwnerAncestors owner := by
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with
              hxBoundary | hxAncestor
            · have hxChildBoundary : x ∈ rightRefinedBoundary boundary right separator := by
                simp only [rightRefinedBoundary, Finset.mem_union]
                exact Or.inr (Finset.mem_inter.mpr ⟨hxBoundary, hxCarrier⟩)
              exact Finset.mem_union_left _ hxChildBoundary
            · rcases Finset.mem_union.mp hxAncestor with hxSeparator | hxChildAncestor
              · exact Finset.mem_union_left _
                  (separator_subset_rightRefinedBoundary boundary right separator hxSeparator)
              · exact Finset.mem_union_right _ hxChildAncestor
          exact ihRight (rightRefinedBoundary boundary right separator) owner
            (Finset.mem_inter.mpr ⟨hxUnion, hxIncident⟩)

/-- Actual terminal ancestor boundaries cost at most three copies of the separator ledger. -/
private theorem EdgeRestrictedStoppedRecursion.terminalBoundaryMass_le_three_charge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    tree.terminalBoundaryMass ≤ 3 * tree.separatorCharge := by
  classical
  calc
    tree.terminalBoundaryMass =
        ∑ owner : tree.edgeOwnerType, (tree.terminalBoundary owner).card := rfl
    _ ≤ ∑ owner : tree.edgeOwnerType,
        (tree.propagatedBoundary ∅ owner).card := by
      exact Finset.sum_le_sum fun owner _ => Finset.card_le_card (by
        intro x hx
        apply tree.inheritedAncestorBoundary_subset_propagated ∅ owner
        simpa [terminalBoundary] using hx)
    _ = tree.propagatedBoundaryMass ∅ :=
      tree.sum_propagatedBoundary_card_eq_mass ∅
    _ ≤ (∅ : Finset ι).card + 3 * tree.separatorCharge :=
      tree.propagatedBoundaryMass_le ∅
    _ = 3 * tree.separatorCharge := by simp

/-- Fixed coefficient controlling total size-separator charge relative to root mass. -/
private def profileDivisionChargeRootConstant (beta exponent : ℝ) : ℝ :=
  profileDivisionPotentialCoefficient beta exponent /
    (3 * (1 / 4 : ℝ) ^ (1 - exponent))

/-- Fixed coefficient controlling terminal-boundary refinement after division by its budget. -/
private def profileDivisionBoundaryRatioConstant (beta exponent : ℝ) : ℝ :=
  profileDivisionPotentialCoefficient beta exponent /
    ((1 / 4 : ℝ) ^ (1 - exponent) *
      (beta / (1 - markedSpineDecayRatio exponent)))

/-- Explicit graph-uniform active-region constant for the two-phase construction. -/
def profileDivisionRegionConstant (beta exponent : ℝ) : ℝ :=
  4 + 4 * profileDivisionChargeRootConstant beta exponent +
    2 * profileDivisionBoundaryRatioConstant beta exponent

/-- The fixed region constant is positive on the profile parameter range. -/
theorem profileDivisionRegionConstant_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionRegionConstant beta exponent := by
  have hpotential := profileDivisionPotentialCoefficient_pos hbeta hexponent
  have hquarter : 0 < (1 / 4 : ℝ) ^ (1 - exponent) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hdecay : 0 < 1 - markedSpineDecayRatio exponent :=
    sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent.1)
  have hweighted : 0 < beta / (1 - markedSpineDecayRatio exponent) :=
    div_pos (zero_lt_one.trans_le hbeta) hdecay
  unfold profileDivisionRegionConstant profileDivisionChargeRootConstant
    profileDivisionBoundaryRatioConstant
  positivity

/-- Quantitative two-phase count before converting the real ratio to a ceiling. -/
private theorem EdgeRestrictedStoppedRecursion.refinedEdgeActive_mul_scale_le_root
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (((tree.refinedEdgeActive beta exponent hProfile).card * r : Nat) : ℝ) ≤
      profileDivisionRegionConstant beta exponent * vertices.card := by
  let budget := weightedSpineSeparatorBudget beta exponent r
  let potentialCoefficient := profileDivisionPotentialCoefficient beta exponent
  let quarterPower := (1 / 4 : ℝ) ^ (1 - exponent)
  let weightedCoefficient := beta / (1 - markedSpineDecayRatio exponent)
  have hrPos : 0 < r := Nat.zero_lt_of_lt hr
  have hbudgetPosNat : 0 < budget :=
    weightedSpineSeparatorBudget_pos hProfile.1 hexponent.1 hr
  have hbudgetPos : (0 : ℝ) < budget := by exact_mod_cast hbudgetPosNat
  have hquarterPos : 0 < quarterPower := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hweightedPos : 0 < weightedCoefficient := by
    exact div_pos (zero_lt_one.trans_le hProfile.1)
      (sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent.1))
  have hbudgetLower : weightedCoefficient * (r : ℝ) ^ exponent ≤ budget := by
    dsimp [budget, weightedCoefficient, weightedSpineSeparatorBudget]
    exact_mod_cast (Nat.le_ceil
      (beta / (1 - markedSpineDecayRatio exponent) * (r : ℝ) ^ exponent))
  have hchargePotential := tree.separatorCharge_le_potential hstopped beta exponent
    hProfile hexponent hrPos hthreshold hlower
  have hpotentialRoot := profileDivisionPotential_le_root
    (zero_le_one.trans hProfile.1) hexponent hr
    (r := r) (parent := vertices.card)
  have hchargeRoot : (tree.separatorCharge : ℝ) ≤
      profileDivisionChargeRootConstant beta exponent * vertices.card := by
    push_cast at hchargePotential
    calc
      (tree.separatorCharge : ℝ) ≤
          profileDivisionPotential beta exponent r vertices.card / 3 := by
        linarith
      _ ≤ (profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ (1 - exponent) * vertices.card) / 3 :=
        div_le_div_of_nonneg_right hpotentialRoot (by norm_num)
      _ = profileDivisionChargeRootConstant beta exponent * vertices.card := by
        unfold profileDivisionChargeRootConstant
        field_simp [hquarterPos.ne']
  have hboundaryPotential : (tree.terminalBoundaryMass : ℝ) ≤
      profileDivisionPotential beta exponent r vertices.card := by
    have hboundary := tree.terminalBoundaryMass_le_three_charge
    have hboundaryReal : (tree.terminalBoundaryMass : ℝ) ≤
        3 * tree.separatorCharge := by exact_mod_cast hboundary
    have hcharge := hchargePotential
    push_cast at hcharge
    linarith [hboundaryReal]
  have hpotentialLinear := profileDivisionPotential_le_linear
    (zero_le_one.trans hProfile.1) hexponent hrPos
    (r := r) (parent := vertices.card)
  have hrpowIdentity :
      (r : ℝ) * (r : ℝ) ^ (exponent - 1) = (r : ℝ) ^ exponent := by
    rw [Real.rpow_sub_one (by positivity)]
    field_simp [show (r : ℝ) ≠ 0 by positivity]
  have hboundaryRatio :
      (r : ℝ) * tree.terminalBoundaryMass / budget ≤
        profileDivisionBoundaryRatioConstant beta exponent * vertices.card := by
    have hnumerator :
        (r : ℝ) * tree.terminalBoundaryMass ≤
          (potentialCoefficient / quarterPower) * vertices.card * (r : ℝ) ^ exponent := by
      have hboundaryLinear := hboundaryPotential.trans hpotentialLinear
      have hscaledLinear := mul_le_mul_of_nonneg_left hboundaryLinear
        (Nat.cast_nonneg r)
      calc
        (r : ℝ) * tree.terminalBoundaryMass ≤
            (r : ℝ) * (profileDivisionPotentialCoefficient beta exponent *
              (vertices.card * (r : ℝ) ^ (exponent - 1) /
                (1 / 4 : ℝ) ^ (1 - exponent))) := hscaledLinear
        _ = (potentialCoefficient / quarterPower) * vertices.card *
            (r : ℝ) ^ exponent := by
          rw [← hrpowIdentity]
          dsimp [potentialCoefficient, quarterPower]
          ring
    apply (div_le_iff₀ hbudgetPos).2
    calc
      (r : ℝ) * tree.terminalBoundaryMass ≤
          (potentialCoefficient / quarterPower) * vertices.card * (r : ℝ) ^ exponent :=
        hnumerator
      _ = profileDivisionBoundaryRatioConstant beta exponent * vertices.card *
          (weightedCoefficient * (r : ℝ) ^ exponent) := by
        change (potentialCoefficient / quarterPower) * vertices.card *
            (r : ℝ) ^ exponent =
          (potentialCoefficient / (quarterPower * weightedCoefficient)) * vertices.card *
            (weightedCoefficient * (r : ℝ) ^ exponent)
        field_simp [hquarterPos.ne', hweightedPos.ne']
      _ ≤ profileDivisionBoundaryRatioConstant beta exponent * vertices.card * budget := by
        apply mul_le_mul_of_nonneg_left hbudgetLower
        have hconstantNonneg : 0 ≤ profileDivisionBoundaryRatioConstant beta exponent := by
          unfold profileDivisionBoundaryRatioConstant
          exact div_nonneg
            (profileDivisionPotentialCoefficient_nonneg
              (zero_le_one.trans hProfile.1) hexponent)
            (mul_nonneg hquarterPos.le hweightedPos.le)
        exact mul_nonneg hconstantNonneg (Nat.cast_nonneg vertices.card)
  have hleaf := tree.terminalOwnerCount_mul_scale_le_four_carrierMass hstopped hlower
  have hcarrier := tree.terminalCarrierMass_le_root_add_charge
  have hleafRoot : (tree.terminalOwnerCount : ℝ) * r ≤
      (4 + 4 * profileDivisionChargeRootConstant beta exponent) * vertices.card := by
    have hleafReal : (tree.terminalOwnerCount : ℝ) * r ≤
        4 * tree.terminalCarrierMass := by exact_mod_cast hleaf
    have hcarrierReal : (tree.terminalCarrierMass : ℝ) ≤
        vertices.card + tree.separatorCharge := by exact_mod_cast hcarrier
    calc
      (tree.terminalOwnerCount : ℝ) * r ≤ 4 * tree.terminalCarrierMass := hleafReal
      _ ≤ 4 * ((vertices.card : ℝ) + tree.separatorCharge) := by
        exact mul_le_mul_of_nonneg_left hcarrierReal (by norm_num)
      _ ≤ 4 * ((vertices.card : ℝ) +
          profileDivisionChargeRootConstant beta exponent * vertices.card) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (le_refl (vertices.card : ℝ)) hchargeRoot) (by norm_num)
      _ = (4 + 4 * profileDivisionChargeRootConstant beta exponent) * vertices.card := by
        ring
  have hrefined := tree.refinedEdgeActive_card_mul_budget_le beta exponent hProfile
  have hrefinedReal : ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) ≤
      tree.terminalOwnerCount + 2 * tree.terminalBoundaryMass / budget := by
    have hrefinedCast :
        ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) * budget ≤
          tree.terminalOwnerCount * budget + 2 * tree.terminalBoundaryMass := by
      exact_mod_cast hrefined
    calc
      ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) ≤
          (tree.terminalOwnerCount * budget + 2 * tree.terminalBoundaryMass) / budget :=
        (le_div_iff₀ hbudgetPos).2 hrefinedCast
      _ = tree.terminalOwnerCount + 2 * tree.terminalBoundaryMass / budget := by
        field_simp [hbudgetPos.ne']
  have hrNonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hscaled := mul_le_mul_of_nonneg_right hrefinedReal hrNonneg
  push_cast
  calc
    ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) * r ≤
        (tree.terminalOwnerCount : ℝ) * r +
          2 * ((r : ℝ) * (tree.terminalBoundaryMass : ℝ) / budget) := by
      have hdecompose :
          ((tree.terminalOwnerCount : ℝ) +
              2 * (tree.terminalBoundaryMass : ℝ) / (budget : ℝ)) * (r : ℝ) =
            (tree.terminalOwnerCount : ℝ) * r +
              2 * ((r : ℝ) * (tree.terminalBoundaryMass : ℝ) / budget) := by
        ring
      exact hscaled.trans_eq hdecompose
    _ ≤ (4 + 4 * profileDivisionChargeRootConstant beta exponent) * vertices.card +
        2 * (profileDivisionBoundaryRatioConstant beta exponent * vertices.card) :=
      add_le_add hleafRoot (mul_le_mul_of_nonneg_left hboundaryRatio (by norm_num))
    _ = profileDivisionRegionConstant beta exponent * vertices.card := by
      unfold profileDivisionRegionConstant
      ring

/-- Exact graph-uniform ceiling form of the two-phase active-region count. -/
theorem EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_le_uniform_ceil
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (tree.refinedEdgeActive beta exponent hProfile).card ≤
      Nat.ceil (profileDivisionRegionConstant beta exponent * vertices.card / r) := by
  have hscaled := tree.refinedEdgeActive_mul_scale_le_root hstopped beta exponent
    hProfile hexponent hr hthreshold hlower
  have hrReal : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hratio : ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) ≤
      profileDivisionRegionConstant beta exponent * vertices.card / r := by
    apply (le_div_iff₀ hrReal).2
    simpa [Nat.cast_mul] using hscaled
  exact_mod_cast hratio.trans (Nat.le_ceil _)

end QEC.Locality

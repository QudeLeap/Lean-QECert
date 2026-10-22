import QEC.Locality.ConnectivityTradeoff.RecursiveSeparator
import QEC.Locality.SeparatorProfile.Quantitative
/-!
# Edge-restricted stopped profile-separator recursion

Unlike the vertex-only recursion checkpoint, this construction carries the
current symmetric edge set explicitly.  At a split, both child carriers retain
the chosen separator, so every terminal edge region is incident only to the
stored terminal carrier.  The uniform threshold makes those carriers strictly
smaller despite the retained separator.
-/

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A finite oriented edge set is closed under reversal. -/
def ReverseSymmetricEdgeSet (edges : Finset (ι × ι)) : Prop :=
  ∀ x y, (x, y) ∈ edges ↔ (y, x) ∈ edges

/-- The graph's full oriented edge set is reverse-symmetric. -/
theorem directedEdgeFinset_reverseSymmetric (G : ConnectivityGraph ι) :
    ReverseSymmetricEdgeSet (directedEdgeFinset G) := by
  intro x y
  rw [mem_directedEdgeFinset_iff, mem_directedEdgeFinset_iff]
  constructor
  · exact fun hxy => G.symmetric hxy
  · exact fun hyx => G.symmetric hyx

/-- Separator allocation preserves the ambient graph-edge invariant. -/
theorem separatorLeftEdges_subset_directed
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (left : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G) :
    separatorLeftEdges edges left ⊆ directedEdgeFinset G :=
  (Finset.filter_subset _ _).trans hsubset

/-- Complementary separator allocation preserves the ambient graph-edge invariant. -/
theorem separatorRightEdges_subset_directed
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (left : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G) :
    separatorRightEdges edges left ⊆ directedEdgeFinset G :=
  (Finset.filter_subset _ _).trans hsubset

/-- The left child carrier contains every endpoint of its allocated edge set. -/
theorem separatorLeftEdges_incident_subset
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι))
    (vertices left separator right : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    edgeIncidentVertices (separatorLeftEdges edges left) ⊆ left ∪ separator := by
  classical
  intro z hz
  rcases (mem_edgeIncidentVertices_iff _ z).1 hz with
    ⟨⟨x, y⟩, hedge, hzEndpoint⟩
  have hedgeParent : (x, y) ∈ edges := (Finset.mem_filter.mp hedge).1
  have hxy : (edgeRestrictedGraph G edges).adjacent x y := by
    refine ⟨(mem_directedEdgeFinset_iff G x y).1 (hsubset hedgeParent), Or.inl hedgeParent⟩
  have hleft : x ∈ left ∨ y ∈ left := (Finset.mem_filter.mp hedge).2
  have hxvertices : x ∈ vertices := by
    apply hincident
    exact (mem_edgeIncidentVertices_iff edges x).2
      ⟨(x, y), hedgeParent, Or.inl rfl⟩
  have hyvertices : y ∈ vertices := by
    apply hincident
    exact (mem_edgeIncidentVertices_iff edges y).2
      ⟨(x, y), hedgeParent, Or.inr rfl⟩
  have hcover : separator ∪ (left ∪ right) = vertices := by
    rw [hpartition.2.1]
    exact Finset.union_sdiff_of_subset hpartition.1
  have hxparts : x ∈ left ∪ separator ∪ right := by
    rw [← hcover] at hxvertices
    simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hxvertices
  have hyparts : y ∈ left ∪ separator ∪ right := by
    rw [← hcover] at hyvertices
    simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hyvertices
  rcases hzEndpoint with rfl | rfl
  · rcases hleft with hxleft | hyleft
    · exact Finset.mem_union_left _ hxleft
    · rcases Finset.mem_union.mp hxparts with hxparts | hxright
      · rcases Finset.mem_union.mp hxparts with hxleft | hxseparator
        · exact Finset.mem_union_left _ hxleft
        · exact Finset.mem_union_right _ hxseparator
      · exact False.elim (hpartition.2.2.2.2.2 hyleft hxright
          ((edgeRestrictedGraph G edges).symmetric hxy))
  · rcases hleft with hxleft | hyleft
    · rcases Finset.mem_union.mp hyparts with hyparts | hyright
      · rcases Finset.mem_union.mp hyparts with hyleft | hyseparator
        · exact Finset.mem_union_left _ hyleft
        · exact Finset.mem_union_right _ hyseparator
      · exact False.elim (hpartition.2.2.2.2.2 hxleft hyright hxy)
    · exact Finset.mem_union_left _ hyleft

/-- The right child carrier contains every endpoint of its allocated edge set. -/
theorem separatorRightEdges_incident_subset
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι))
    (vertices left separator right : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    edgeIncidentVertices (separatorRightEdges edges left) ⊆ right ∪ separator := by
  classical
  intro z hz
  rcases (mem_edgeIncidentVertices_iff _ z).1 hz with
    ⟨⟨x, y⟩, hedge, hzEndpoint⟩
  have hedgeParent : (x, y) ∈ edges := (Finset.mem_filter.mp hedge).1
  have hxy : (edgeRestrictedGraph G edges).adjacent x y := by
    refine ⟨(mem_directedEdgeFinset_iff G x y).1 (hsubset hedgeParent), Or.inl hedgeParent⟩
  have hnotLeft : ¬ (x ∈ left ∨ y ∈ left) := (Finset.mem_filter.mp hedge).2
  have hxvertices : x ∈ vertices := by
    apply hincident
    exact (mem_edgeIncidentVertices_iff edges x).2
      ⟨(x, y), hedgeParent, Or.inl rfl⟩
  have hyvertices : y ∈ vertices := by
    apply hincident
    exact (mem_edgeIncidentVertices_iff edges y).2
      ⟨(x, y), hedgeParent, Or.inr rfl⟩
  have hcover : separator ∪ (left ∪ right) = vertices := by
    rw [hpartition.2.1]
    exact Finset.union_sdiff_of_subset hpartition.1
  have hxparts : x ∈ left ∪ separator ∪ right := by
    rw [← hcover] at hxvertices
    simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hxvertices
  have hyparts : y ∈ left ∪ separator ∪ right := by
    rw [← hcover] at hyvertices
    simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hyvertices
  rcases hzEndpoint with rfl | rfl
  · rcases Finset.mem_union.mp hxparts with hxparts | hxright
    · rcases Finset.mem_union.mp hxparts with hxleft | hxseparator
      · exact False.elim (hnotLeft (Or.inl hxleft))
      · exact Finset.mem_union_right _ hxseparator
    · exact Finset.mem_union_left _ hxright
  · rcases Finset.mem_union.mp hyparts with hyparts | hyright
    · rcases Finset.mem_union.mp hyparts with hyleft | hyseparator
      · exact False.elim (hnotLeft (Or.inr hyleft))
      · exact Finset.mem_union_right _ hyseparator
    · exact Finset.mem_union_left _ hyright

/--
The edge-restricted recursion retains a separator in each child carrier.  This
is the missing stopped-recursion invariant: terminal edge regions are bounded
by their actual incident vertices rather than by a separator-free vertex leaf.
-/
inductive EdgeRestrictedStoppedRecursion (G : ConnectivityGraph ι) (r : Nat) :
    Finset (ι × ι) → Finset ι → Type u
  | leaf {edges : Finset (ι × ι)} {vertices : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hcard : vertices.card ≤ r) :
      EdgeRestrictedStoppedRecursion G r edges vertices
  | split {edges : Finset (ι × ι)} {vertices left separator right : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hpartition :
        TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
          vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize (edgeRestrictedGraph G edges) vertices)
      (hleft : (left ∪ separator).card < vertices.card)
      (hright : (right ∪ separator).card < vertices.card)
      (leftTree : EdgeRestrictedStoppedRecursion G r
        (separatorLeftEdges edges left) (left ∪ separator))
      (rightTree : EdgeRestrictedStoppedRecursion G r
        (separatorRightEdges edges left) (right ∪ separator)) :
      EdgeRestrictedStoppedRecursion G r edges vertices

private theorem left_disjoint_separator
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    Disjoint left separator := by
  apply Finset.disjoint_left.mpr
  intro x hxleft hxseparator
  have hdiff : x ∈ vertices \ separator := by
    rw [← hpartition.2.1]
    exact Finset.mem_union_left _ hxleft
  exact (Finset.mem_sdiff.mp hdiff).2 hxseparator

private theorem right_disjoint_separator
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    Disjoint right separator := by
  apply Finset.disjoint_left.mpr
  intro x hxright hxseparator
  have hdiff : x ∈ vertices \ separator := by
    rw [← hpartition.2.1]
    exact Finset.mem_union_right _ hxright
  exact (Finset.mem_sdiff.mp hdiff).2 hxseparator

/-- Retaining a separator in both child carriers duplicates exactly that separator. -/
private theorem split_child_carrier_card_sum
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right) :
    (left ∪ separator).card + (right ∪ separator).card =
      vertices.card + separator.card := by
  have hleftSeparator : Disjoint left separator := left_disjoint_separator hpartition
  have hrightSeparator : Disjoint right separator := right_disjoint_separator hpartition
  have hleftRight : Disjoint left right := hpartition.2.2.1
  have hseparatorRemainder : Disjoint separator (vertices \ separator) := by
    apply Finset.disjoint_left.mpr
    intro x hxseparator hxremainder
    exact (Finset.mem_sdiff.mp hxremainder).2 hxseparator
  have hseparatorCard : separator.card + (left ∪ right).card = vertices.card := by
    calc
      separator.card + (left ∪ right).card = separator.card +
          (vertices \ separator).card := by rw [← hpartition.2.1]
      _ = (separator ∪ (vertices \ separator)).card :=
        (Finset.card_union_of_disjoint hseparatorRemainder).symm
      _ = vertices.card := by rw [Finset.union_sdiff_of_subset hpartition.1]
  have hleftRightCard : (left ∪ right).card = left.card + right.card :=
    Finset.card_union_of_disjoint hleftRight
  rw [Finset.card_union_of_disjoint hleftSeparator,
    Finset.card_union_of_disjoint hrightSeparator]
  omega

/-- A twelfth-scale separator forces both balanced sides to carry a quarter of the parent. -/
private theorem split_side_card_ge_quarter
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (hseparator : 12 * separator.card ≤ vertices.card) :
    vertices.card ≤ 4 * left.card ∧ vertices.card ≤ 4 * right.card := by
  have hleftRight : Disjoint left right := hpartition.2.2.1
  have hseparatorRemainder : Disjoint separator (vertices \ separator) := by
    apply Finset.disjoint_left.mpr
    intro x hxseparator hxremainder
    exact (Finset.mem_sdiff.mp hxremainder).2 hxseparator
  have hcard : separator.card + left.card + right.card = vertices.card := by
    calc
      separator.card + left.card + right.card =
          separator.card + (left ∪ right).card := by
        rw [Finset.card_union_of_disjoint hleftRight, Nat.add_assoc]
      _ = separator.card + (vertices \ separator).card := by rw [← hpartition.2.1]
      _ = (separator ∪ (vertices \ separator)).card :=
        (Finset.card_union_of_disjoint hseparatorRemainder).symm
      _ = vertices.card := by rw [Finset.union_sdiff_of_subset hpartition.1]
  have hleftBalanced : 3 * left.card ≤ 2 * vertices.card := hpartition.2.2.2.1
  have hrightBalanced : 3 * right.card ≤ 2 * vertices.card := hpartition.2.2.2.2.1
  constructor <;> omega

private theorem split_child_carrier_card_ge_quarter
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (hseparator : 12 * separator.card ≤ vertices.card) :
    vertices.card ≤ 4 * (left ∪ separator).card ∧
      vertices.card ≤ 4 * (right ∪ separator).card := by
  have hsides := split_side_card_ge_quarter hpartition hseparator
  constructor
  · exact hsides.1.trans (Nat.mul_le_mul_left 4
      (Finset.card_le_card Finset.subset_union_left))
  · exact hsides.2.trans (Nat.mul_le_mul_left 4
      (Finset.card_le_card Finset.subset_union_left))

/-- Terminal owner indices of the stopped edge recursion. -/
def EdgeRestrictedStoppedRecursion.edgeOwnerType
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Type
  | .leaf _ _ _ _ => Unit
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      Sum leftTree.edgeOwnerType rightTree.edgeOwnerType

noncomputable instance EdgeRestrictedStoppedRecursion.edgeOwnerFintype
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    Fintype tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ =>
      change Fintype Unit
      infer_instance
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      change Fintype (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType)
      letI := ihLeft
      letI := ihRight
      infer_instance

noncomputable instance EdgeRestrictedStoppedRecursion.edgeOwnerDecidableEq
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    DecidableEq tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ =>
      change DecidableEq Unit
      infer_instance
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      change DecidableEq (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType)
      letI := ihLeft
      letI := ihRight
      infer_instance

/-- The exact terminal edge region owned by a stopped-recursion path. -/
noncomputable def EdgeRestrictedStoppedRecursion.edgeRegion
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      tree.edgeOwnerType → Finset (ι × ι)
  | .leaf (edges := edges) _ _ _ _, _ => edges
  | .split _ _ _ _ _ _ _ leftTree rightTree, owner =>
      match owner with
      | Sum.inl owner => leftTree.edgeRegion owner
      | Sum.inr owner => rightTree.edgeRegion owner

/-- Only terminal paths carrying an edge are active regions. -/
noncomputable def EdgeRestrictedStoppedRecursion.edgeActive
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) : Finset tree.edgeOwnerType := by
  classical
  exact Finset.univ.filter fun owner => (tree.edgeRegion owner).Nonempty

/-- Exact terminal-path count. -/
noncomputable def EdgeRestrictedStoppedRecursion.terminalOwnerCount
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Nat
  | .leaf _ _ _ _ => 1
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      leftTree.terminalOwnerCount + rightTree.terminalOwnerCount

theorem EdgeRestrictedStoppedRecursion.edgeOwnerType_card_eq_terminalOwnerCount
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    Fintype.card tree.edgeOwnerType = tree.terminalOwnerCount := by
  induction tree with
  | leaf _ _ _ _ => simp [edgeOwnerType, terminalOwnerCount]
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      change Fintype.card (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType) =
        leftTree.terminalOwnerCount + rightTree.terminalOwnerCount
      rw [Fintype.card_sum, ihLeft, ihRight]

/-- Every terminal region is a subset of its recursion-node edge set. -/
theorem EdgeRestrictedStoppedRecursion.edgeRegion_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) : tree.edgeRegion owner ⊆ edges := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      simpa [edgeRegion]
  | split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner =>
          exact (ihLeft owner).trans (Finset.filter_subset _ _)
      | inr owner =>
          exact (ihRight owner).trans (Finset.filter_subset _ _)

/-- Every terminal region remains reverse-symmetric. -/
theorem EdgeRestrictedStoppedRecursion.edgeRegion_reverse
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) (x y : ι) :
    (x, y) ∈ tree.edgeRegion owner ↔ (y, x) ∈ tree.edgeRegion owner := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      exact hsymmetric x y
  | split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner

/-- A terminal stopped-recursion region obeys the requested incident cap. -/
theorem EdgeRestrictedStoppedRecursion.edgeRegion_incident_card_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)).card ≤ r := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      exact (Finset.card_le_card hincident).trans hcard
  | split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner => exact ihLeft owner
      | inr owner => exact ihRight owner

/-- Incident-vertex sets are monotone under edge-set inclusion. -/
theorem edgeIncidentVertices_mono {edges₁ edges₂ : Finset (ι × ι)}
    (hsubset : edges₁ ⊆ edges₂) :
    edgeIncidentVertices edges₁ ⊆ edgeIncidentVertices edges₂ := by
  intro x hx
  rcases (mem_edgeIncidentVertices_iff _ x).1 hx with ⟨edge, hedge, hendpoint⟩
  exact (mem_edgeIncidentVertices_iff _ x).2 ⟨edge, hsubset hedge, hendpoint⟩

/-- Separators retained on the route from the root to a terminal owner. -/
noncomputable def EdgeRestrictedStoppedRecursion.edgeOwnerAncestors
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      tree.edgeOwnerType → Finset ι
  | .leaf _ _ _ _, _ => ∅
  | .split (separator := separator) _ _ _ _ _ _ _ leftTree rightTree, owner =>
      match owner with
      | Sum.inl owner => separator ∪ leftTree.edgeOwnerAncestors owner
      | Sum.inr owner => separator ∪ rightTree.edgeOwnerAncestors owner

private theorem left_terminal_incident_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (leftTree : EdgeRestrictedStoppedRecursion G r
      (separatorLeftEdges edges left) (left ∪ separator))
    (owner : leftTree.edgeOwnerType) :
    edgeIncidentVertices (leftTree.edgeRegion owner) ⊆ left ∪ separator := by
  apply (edgeIncidentVertices_mono (leftTree.edgeRegion_subset owner)).trans
  exact separatorLeftEdges_incident_subset G edges vertices left separator right
    hsubset hsymmetric hincident hpartition

private theorem right_terminal_incident_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (rightTree : EdgeRestrictedStoppedRecursion G r
      (separatorRightEdges edges left) (right ∪ separator))
    (owner : rightTree.edgeOwnerType) :
    edgeIncidentVertices (rightTree.edgeRegion owner) ⊆ right ∪ separator := by
  apply (edgeIncidentVertices_mono (rightTree.edgeRegion_subset owner)).trans
  exact separatorRightEdges_incident_subset G edges vertices left separator right
    hsubset hsymmetric hincident hpartition

private theorem cross_terminal_incident_inter_subset_separator
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
        vertices left separator right)
    (leftTree : EdgeRestrictedStoppedRecursion G r
      (separatorLeftEdges edges left) (left ∪ separator))
    (rightTree : EdgeRestrictedStoppedRecursion G r
      (separatorRightEdges edges left) (right ∪ separator))
    (leftOwner : leftTree.edgeOwnerType) (rightOwner : rightTree.edgeOwnerType) :
    edgeIncidentVertices (leftTree.edgeRegion leftOwner) ∩
      edgeIncidentVertices (rightTree.edgeRegion rightOwner) ⊆ separator := by
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hxleft, hxright⟩
  by_contra hxseparator
  have hxleft' := left_terminal_incident_subset hsubset hsymmetric hincident hpartition
    leftTree leftOwner hxleft
  have hxright' := right_terminal_incident_subset hsubset hsymmetric hincident hpartition
    rightTree rightOwner hxright
  have hxL : x ∈ left := by
    rcases Finset.mem_union.mp hxleft' with hxL | hxS
    · exact hxL
    · exact False.elim (hxseparator hxS)
  have hxR : x ∈ right := by
    rcases Finset.mem_union.mp hxright' with hxR | hxS
    · exact hxR
    · exact False.elim (hxseparator hxS)
  exact (Finset.disjoint_left.mp hpartition.2.2.1) hxL hxR

/--
Any shared vertex incident to a terminal region occurs in a separator on that
owner's ancestor route.  This removes the global edge-division definition from
the later quantitative boundary charge.
-/
theorem EdgeRestrictedStoppedRecursion.localSharedBoundary_subset_ancestors
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)) ∩
      edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive ⊆
        tree.edgeOwnerAncestors owner := by
  classical
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      intro x hx
      rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
        ⟨i, hi, j, hj, hij, hxi, hxj⟩
      have heq : i = j := by
        simpa [edgeOwnerType] using (Subsingleton.elim (α := Unit) i j)
      exact False.elim (hij heq)
  | @split edges vertices left separator right hsubset hsymmetric hincident
      hpartition hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner =>
          intro x hx
          have hxOwner : x ∈ edgeIncidentVertices (leftTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).1
          have hownerNonempty : (leftTree.edgeRegion owner).Nonempty := by
            rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
            exact ⟨edge, hedge⟩
          have hownerActive : owner ∈ leftTree.edgeActive := by
            simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hownerNonempty
          rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
            ⟨i, hi, j, hj, hij, hxi, hxj⟩
          have hcandidate : ∃ candidate : Sum leftTree.edgeOwnerType rightTree.edgeOwnerType,
              candidate ≠ Sum.inl owner ∧ candidate ∈
                (EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeActive ∧
              x ∈ edgeIncidentVertices
                ((EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeRegion candidate) := by
            by_cases hiOwner : i = Sum.inl owner
            · refine ⟨j, ?_, hj, hxj⟩
              intro hjOwner
              apply hij
              exact hiOwner.trans hjOwner.symm
            · exact ⟨i, hiOwner, hi, hxi⟩
          rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
          cases candidate with
          | inl candidate =>
              have hcandidateActive : candidate ∈ leftTree.edgeActive := by
                have hnonempty := (@Finset.mem_filter _ _
                  (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_univ _, hnonempty.2⟩
              have hxcandidate' : x ∈ edgeIncidentVertices (leftTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              have hxChildShared : x ∈ edgeDivisionSharedBoundary
                  leftTree.edgeRegion leftTree.edgeActive := by
                apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                  hxcandidate'⟩
                intro heq
                exact hne (congrArg Sum.inl heq.symm)
              exact Finset.mem_union_right _
                (ihLeft owner (Finset.mem_inter.mpr ⟨hxOwner, hxChildShared⟩))
          | inr candidate =>
              have hxcandidate' : x ∈ edgeIncidentVertices (rightTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              exact Finset.mem_union_left _
                (cross_terminal_incident_inter_subset_separator hsubset hsymmetric hincident
                  hpartition leftTree rightTree owner candidate
                  (Finset.mem_inter.mpr ⟨hxOwner, hxcandidate'⟩))
      | inr owner =>
          intro x hx
          have hxOwner : x ∈ edgeIncidentVertices (rightTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).1
          have hownerNonempty : (rightTree.edgeRegion owner).Nonempty := by
            rcases (mem_edgeIncidentVertices_iff _ x).1 hxOwner with ⟨edge, hedge, _⟩
            exact ⟨edge, hedge⟩
          have hownerActive : owner ∈ rightTree.edgeActive := by
            simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hownerNonempty
          rcases (mem_edgeDivisionSharedBoundary_iff _ _ x).1 (Finset.mem_inter.mp hx).2 with
            ⟨i, hi, j, hj, hij, hxi, hxj⟩
          have hcandidate : ∃ candidate : Sum leftTree.edgeOwnerType rightTree.edgeOwnerType,
              candidate ≠ Sum.inr owner ∧ candidate ∈
                (EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeActive ∧
              x ∈ edgeIncidentVertices
                ((EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident
                  hpartition hminimum hleft hright leftTree rightTree).edgeRegion candidate) := by
            by_cases hiOwner : i = Sum.inr owner
            · refine ⟨j, ?_, hj, hxj⟩
              intro hjOwner
              apply hij
              exact hiOwner.trans hjOwner.symm
            · exact ⟨i, hiOwner, hi, hxi⟩
          rcases hcandidate with ⟨candidate, hne, hcandActive, hxcandidate⟩
          cases candidate with
          | inl candidate =>
              have hxcandidate' : x ∈ edgeIncidentVertices (leftTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              exact Finset.mem_union_left _
                (cross_terminal_incident_inter_subset_separator hsubset hsymmetric hincident
                  hpartition leftTree rightTree candidate owner
                  (Finset.mem_inter.mpr ⟨hxcandidate', hxOwner⟩))
          | inr candidate =>
              have hcandidateActive : candidate ∈ rightTree.edgeActive := by
                have hnonempty := (@Finset.mem_filter _ _
                  (fun _ => Finset.decidableNonempty) _ _).mp hcandActive
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_univ _, hnonempty.2⟩
              have hxcandidate' : x ∈ edgeIncidentVertices (rightTree.edgeRegion candidate) := by
                simpa [edgeRegion] using hxcandidate
              have hxChildShared : x ∈ edgeDivisionSharedBoundary
                  rightTree.edgeRegion rightTree.edgeActive := by
                apply (mem_edgeDivisionSharedBoundary_iff _ _ x).2
                refine ⟨owner, hownerActive, candidate, hcandidateActive, ?_, hxOwner,
                  hxcandidate'⟩
                intro heq
                exact hne (congrArg Sum.inr heq.symm)
              exact Finset.mem_union_right _
                (ihRight owner (Finset.mem_inter.mpr ⟨hxOwner, hxChildShared⟩))

/-- Every edge in the current edge set has a unique terminal owner. -/
theorem EdgeRestrictedStoppedRecursion.existsUnique_edgeOwner
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.edgeOwnerType, edge ∈ tree.edgeRegion owner := by
  induction tree generalizing edge with
  | leaf hsubset hsymmetric hincident hcard =>
      refine ⟨Unit.unit, ?_, ?_⟩
      · simpa [edgeRegion] using hedge
      · intro owner _
        simpa [edgeOwnerType] using
          (Subsingleton.elim (α := Unit) owner Unit.unit)
  | @split edges vertices left separator right hsubset hsymmetric hincident
      hpartition hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      by_cases hleftEdge : edge.1 ∈ left ∨ edge.2 ∈ left
      · have hchild : edge ∈ separatorLeftEdges edges left :=
          Finset.mem_filter.mpr ⟨hedge, hleftEdge⟩
        rcases ihLeft edge hchild with ⟨owner, howner, hunique⟩
        refine ⟨Sum.inl owner, ?_, ?_⟩
        · simpa [edgeRegion] using howner
        · intro candidate hcandidate
          cases candidate with
          | inl candidate =>
              exact congrArg Sum.inl (hunique candidate (by simpa [edgeRegion] using hcandidate))
          | inr candidate =>
              have hright : edge ∈ separatorRightEdges edges left := by
                apply rightTree.edgeRegion_subset candidate
                simpa [edgeRegion] using hcandidate
              exact False.elim ((Finset.mem_filter.mp hright).2 hleftEdge)
      · have hchild : edge ∈ separatorRightEdges edges left :=
          Finset.mem_filter.mpr ⟨hedge, hleftEdge⟩
        rcases ihRight edge hchild with ⟨owner, howner, hunique⟩
        refine ⟨Sum.inr owner, ?_, ?_⟩
        · simpa [edgeRegion] using howner
        · intro candidate hcandidate
          cases candidate with
          | inl candidate =>
              have hleftRegion : edge ∈ separatorLeftEdges edges left := by
                apply leftTree.edgeRegion_subset candidate
                simpa [edgeRegion] using hcandidate
              exact False.elim (hleftEdge (Finset.mem_filter.mp hleftRegion).2)
          | inr candidate =>
              exact congrArg Sum.inr (hunique candidate (by simpa [edgeRegion] using hcandidate))

/-- The stopped recursion constructs an edge division whenever its root owns all graph edges. -/
theorem EdgeRestrictedStoppedRecursion.edgeRegions_isEdgeDivision
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
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
    refine ⟨owner, ⟨by
      simp only [edgeActive, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨edge, howner⟩, howner⟩, ?_⟩
    intro candidate hcandidate
    exact hunique candidate hcandidate.2

end QEC.Locality

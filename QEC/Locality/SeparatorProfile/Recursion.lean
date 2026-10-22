import QEC.Locality.SeparatorProfile.EdgeDivision
/-!
# Finite profile-separator recursion

This module supplies the well-founded vertex-recursion substrate for the
profile-sensitive edge-division construction.  It uses the repository's exact
minimum `2/3` separator at every non-leaf node, records strict cardinality
decrease for both children, and proves finite depth, leaf-size, leaf-count,
coverage, profile-power, and natural-ceiling invariants.

The recursion removes separator vertices rather than assigning their incident
edges.  Consequently it is not yet an edge division: the subsequent edge
allocation layer must attach separator-incident edges to recursive regions and
derive the sharper profile-sensitive active-region and local-boundary bounds.
-/

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Restrict a graph to a vertex set while retaining the ambient finite type. -/
def vertexRestrictedGraph (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ConnectivityGraph ι where
  adjacent x y := x ∈ vertices ∧ y ∈ vertices ∧ G.adjacent x y
  symmetric := by
    rintro x y ⟨hx, hy, hxy⟩
    exact ⟨hy, hx, G.symmetric hxy⟩
  loopless := by
    intro x hxx
    exact G.loopless x hxx.2.2

omit [DecidableEq ι] in
/-- Vertex restriction is an edge deletion on the same ambient type. -/
theorem vertexRestrictedGraph_isSpanningSubgraph
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    IsSpanningSubgraph (vertexRestrictedGraph G vertices) G := by
  intro x y hxy
  exact hxy.2.2

/-- Exact measured profiles are inherited by ambient-type vertex restrictions. -/
theorem twoThirdsSeparationProfile_vertexRestricted_le
    (G : ConnectivityGraph ι) (vertices : Finset ι) (scale : Nat) :
    twoThirdsSeparationProfile (vertexRestrictedGraph G vertices) scale ≤
      twoThirdsSeparationProfile G scale :=
  twoThirdsSeparationProfile_mono_spanningSubgraph
    (vertexRestrictedGraph_isSpanningSubgraph G vertices) scale

/-- Restrict a graph to the undirected edges represented by a finite oriented set. -/
def edgeRestrictedGraph (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) :
    ConnectivityGraph ι where
  adjacent x y := G.adjacent x y ∧ ((x, y) ∈ edges ∨ (y, x) ∈ edges)
  symmetric := by
    rintro x y ⟨hxy, hmem⟩
    exact ⟨G.symmetric hxy, hmem.symm⟩
  loopless := by
    intro x hxx
    exact G.loopless x hxx.1

omit [DecidableEq ι] in
/-- Finite edge restriction is a spanning subgraph. -/
theorem edgeRestrictedGraph_isSpanningSubgraph
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) :
    IsSpanningSubgraph (edgeRestrictedGraph G edges) G := by
  intro x y hxy
  exact hxy.1

/-- Exact measured profiles are inherited by finite edge restrictions. -/
theorem twoThirdsSeparationProfile_edgeRestricted_le
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (scale : Nat) :
    twoThirdsSeparationProfile (edgeRestrictedGraph G edges) scale ≤
      twoThirdsSeparationProfile G scale :=
  twoThirdsSeparationProfile_mono_spanningSubgraph
    (edgeRestrictedGraph_isSpanningSubgraph G edges) scale

private theorem left_card_lt_of_twoThirdsPartition
    (G : ConnectivityGraph ι) {vertices left separator right : Finset ι}
    (hvertices : 0 < vertices.card)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    left.card < vertices.card := by
  have hbalanced : 3 * left.card ≤ 2 * vertices.card := hpartition.2.2.2.1
  omega

private theorem right_card_lt_of_twoThirdsPartition
    (G : ConnectivityGraph ι) {vertices left separator right : Finset ι}
    (hvertices : 0 < vertices.card)
    (hpartition :
      TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    right.card < vertices.card := by
  have hbalanced : 3 * right.card ≤ 2 * vertices.card := hpartition.2.2.2.2.1
  omega

/--
A finite recursion tree whose non-leaf nodes use an exact minimum measured
separator and whose children are strictly smaller than their parent.
-/
inductive ProfileSeparatorRecursion (G : ConnectivityGraph ι) (r : Nat) :
    Finset ι → Type u
  | leaf {vertices : Finset ι} (hcard : vertices.card ≤ r) :
      ProfileSeparatorRecursion G r vertices
  | split {vertices left separator right : Finset ι}
      (hpartition :
        TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum :
        separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hleft : left.card < vertices.card)
      (hright : right.card < vertices.card)
      (leftTree : ProfileSeparatorRecursion G r left)
      (rightTree : ProfileSeparatorRecursion G r right) :
      ProfileSeparatorRecursion G r vertices

private structure MinimumSeparatorSplit (G : ConnectivityGraph ι)
    (vertices : Finset ι) where
  left : Finset ι
  separator : Finset ι
  right : Finset ι
  partition :
    TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right
  minimum :
    separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices

private noncomputable def chosenMinimumSeparatorSplit
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    MinimumSeparatorSplit G vertices :=
  Classical.choice (by
    rcases exists_minimumTwoThirdsBalancedVertexSeparator G vertices with
      ⟨separator, -, hbalanced, hminimum⟩
    rcases hbalanced with ⟨left, right, hpartition⟩
    exact ⟨⟨left, separator, right, hpartition, hminimum⟩⟩)

/-- Construct the exact measured separator recursion by strong cardinality descent. -/
noncomputable def buildProfileSeparatorRecursion
    (G : ConnectivityGraph ι) (r : Nat) (hr : 0 < r) (vertices : Finset ι) :
    ProfileSeparatorRecursion G r vertices := by
  classical
  by_cases hleaf : vertices.card ≤ r
  · exact .leaf hleaf
  · let chosen := chosenMinimumSeparatorSplit G vertices
    have hvertices : 0 < vertices.card := by omega
    have hleft := left_card_lt_of_twoThirdsPartition G hvertices chosen.partition
    have hright := right_card_lt_of_twoThirdsPartition G hvertices chosen.partition
    exact .split chosen.partition chosen.minimum hleft hright
      (buildProfileSeparatorRecursion G r hr chosen.left)
      (buildProfileSeparatorRecursion G r hr chosen.right)
termination_by vertices.card
decreasing_by
  · simpa [chosen] using hleft
  · simpa [chosen] using hright

/-- Recursive leaves, omitting empty leaves. -/
def ProfileSeparatorRecursion.leaves
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → List (Finset ι)
  | .leaf _ => if vertices = ∅ then [] else [vertices]
  | .split _ _ _ _ leftTree rightTree => leftTree.leaves ++ rightTree.leaves

/-- The union of all vertices stored at leaf nodes. -/
def ProfileSeparatorRecursion.leafUnion
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → Finset ι
  | .leaf _ => vertices
  | .split _ _ _ _ leftTree rightTree => leftTree.leafUnion ∪ rightTree.leafUnion

/-- The union of all separators removed at internal nodes. -/
def ProfileSeparatorRecursion.separatorUnion
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → Finset ι
  | .leaf _ => ∅
  | @split _ _ _ _ _ _ _ separator _ _ _ _ _ leftTree rightTree =>
      separator ∪ leftTree.separatorUnion ∪ rightTree.separatorUnion

/-- The vertex set indexed by the recursion tree. -/
def ProfileSeparatorRecursion.root
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (_ : ProfileSeparatorRecursion G r vertices) : Finset ι :=
  vertices

/-- Maximum number of split nodes on a root-to-leaf path. -/
def ProfileSeparatorRecursion.depth
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι} :
    ProfileSeparatorRecursion G r vertices → Nat
  | .leaf _ => 0
  | .split _ _ _ _ leftTree rightTree =>
      Nat.succ (max leftTree.depth rightTree.depth)

/-- Every recursively produced leaf obeys the requested cardinality cap. -/
theorem ProfileSeparatorRecursion.mem_leaves_card_le
    {G : ConnectivityGraph ι} {r : Nat} {vertices leaf : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) (hleaf : leaf ∈ tree.leaves) :
    leaf.card ≤ r := by
  induction tree with
  | leaf hcard =>
      simp only [leaves] at hleaf
      split at hleaf
      · simp at hleaf
      · simp_all
  | split hpartition hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      simp only [leaves, List.mem_append] at hleaf
      exact hleaf.elim ihLeft ihRight

/-- Removed separators together with the leaf union cover the root exactly. -/
theorem ProfileSeparatorRecursion.separatorUnion_union_leafUnion
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.separatorUnion ∪ tree.leafUnion = tree.root := by
  induction tree with
  | @leaf vertices hcard => simp [separatorUnion, leafUnion, root]
  | @split vertices left separator right hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      change (separator ∪ leftTree.separatorUnion ∪ rightTree.separatorUnion) ∪
        (leftTree.leafUnion ∪ rightTree.leafUnion) = vertices
      change leftTree.separatorUnion ∪ leftTree.leafUnion = left at ihLeft
      change rightTree.separatorUnion ∪ rightTree.leafUnion = right at ihRight
      calc
        (separator ∪ leftTree.separatorUnion ∪ rightTree.separatorUnion) ∪
            (leftTree.leafUnion ∪ rightTree.leafUnion) =
            separator ∪
              ((leftTree.separatorUnion ∪ leftTree.leafUnion) ∪
                (rightTree.separatorUnion ∪ rightTree.leafUnion)) := by ac_rfl
        _ = separator ∪ (left ∪ right) := by
              rw [ihLeft, ihRight]
        _ = separator ∪ (vertices \ separator) := by rw [hpartition.2.1]
        _ = vertices := Finset.union_sdiff_of_subset hpartition.1

/-- The number of nonempty leaves is bounded by the root cardinality. -/
theorem ProfileSeparatorRecursion_leaves_length_le_card
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.leaves.length ≤ tree.root.card := by
  induction tree with
  | @leaf vertices hcard =>
      by_cases hempty : vertices = ∅
      · simp [ProfileSeparatorRecursion.leaves, ProfileSeparatorRecursion.root, hempty]
      · change (if vertices = ∅ then [] else [vertices]).length ≤ vertices.card
        rw [if_neg hempty]
        simp only [List.length_singleton]
        exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  | @split vertices left separator right hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      simp only [ProfileSeparatorRecursion.leaves, List.length_append]
      calc
        leftTree.leaves.length + rightTree.leaves.length ≤
            left.card + right.card :=
          Nat.add_le_add ihLeft ihRight
        _ = (left ∪ right).card := by
          rw [Finset.card_union_of_disjoint hpartition.2.2.1]
        _ ≤ (ProfileSeparatorRecursion.split hpartition hminimum hleft hright
            leftTree rightTree).root.card := by
          change (left ∪ right).card ≤ vertices.card
          rw [hpartition.2.1]
          exact Finset.card_le_card (Finset.sdiff_subset)

/-- Strict child descent bounds recursion depth by the root cardinality. -/
theorem ProfileSeparatorRecursion_depth_le_card
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.depth ≤ tree.root.card := by
  induction tree with
  | @leaf vertices hcard => simp [ProfileSeparatorRecursion.depth]
  | @split vertices left separator right hpartition hminimum hleft hright
      leftTree rightTree ihLeft ihRight =>
      simp only [ProfileSeparatorRecursion.depth]
      have hleftDepth : leftTree.depth < vertices.card := ihLeft.trans_lt hleft
      have hrightDepth : rightTree.depth < vertices.card := ihRight.trans_lt hright
      change Nat.succ (max leftTree.depth rightTree.depth) ≤ vertices.card
      omega

/-- An exact minimum separator is bounded by the measured profile at its own scale. -/
theorem minimumSeparator_card_le_ownProfile
    (G : ConnectivityGraph ι) (vertices separator : Finset ι)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    separator.card ≤ twoThirdsSeparationProfile G vertices.card := by
  rw [hminimum]
  exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    G vertices.card vertices (Finset.subset_univ _) le_rfl

/-- The profile hypothesis gives the exact real-power cap at every nonempty node. -/
theorem minimumSeparator_card_real_le_profilePower
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (vertices separator : Finset ι)
    (hvertices : 1 ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    (separator.card : ℝ) ≤ beta * Real.rpow vertices.card exponent := by
  have hmeasured := minimumSeparator_card_le_ownProfile G vertices separator hminimum
  exact (Nat.cast_le.2 hmeasured).trans
    (hProfile.2.2.2 vertices.card hvertices (Finset.card_le_univ vertices))

/-- Natural-ceiling form of the same exact profile-power bound. -/
theorem minimumSeparator_card_le_profilePowerCeil
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (vertices separator : Finset ι)
    (hvertices : 1 ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    separator.card ≤ Nat.ceil (beta * Real.rpow vertices.card exponent) := by
  have hreal := minimumSeparator_card_real_le_profilePower
    G beta exponent hProfile vertices separator hvertices hminimum
  exact_mod_cast hreal.trans (Nat.le_ceil (beta * Real.rpow vertices.card exponent))

end QEC.Locality

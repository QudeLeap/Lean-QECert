import QEC.Locality.CorrectableRegions.CorrectableRegionClosure
import QEC.Locality.SeparatorProfile.Core
/-!
# BGKL small-boundary correctability

This module implements the recursive `2/3`-separator tree used in the proof of
BGKL, Lemma `correct-1`.  The exponent range in this slice is the source range
`0 < c < 1`; the endpoint `c = 1` belongs to the separate finite-stabilizer
argument routed by the M4 source audit.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding
open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- A finite coordinate set viewed as the concrete qubit subsystem it selects. -/
def finiteSubsystemOfFinset (vertices : Finset ι) : FiniteSubsystem ι :=
  ⟨vertices⟩

/-- The explicit minimum-separator split selected at one internal tree node. -/
structure BGKLSeparatorSplit
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) where
  separator : Finset ι
  left : Finset ι
  right : Finset ι
  separator_subset : separator ⊆ vertices
  partition : left ∪ right = vertices \ separator
  disjoint : Disjoint left right
  left_balance : 3 * left.card ≤ 2 * vertices.card
  right_balance : 3 * right.card ≤ 2 * vertices.card
  noEdge : P.fixedGeneratorNoEdgeBetween left right
  separator_card : separator.card =
    P.fixedGeneratorMinimumTwoThirdsBalancedVertexSeparatorSize vertices

/-- Choose a witnessed minimum separator and its witnessed `2/3` partition. -/
noncomputable def minimumBGKLSeparatorSplit
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) : BGKLSeparatorSplit P vertices := by
  classical
  let witness :=
    exists_minimumTwoThirdsBalancedVertexSeparator
      P.fixedGeneratorInteractionGraph vertices
  let separator := Classical.choose witness
  have hseparator := Classical.choose_spec witness
  let leftWitness := hseparator.2.1
  let left := Classical.choose leftWitness
  let rightWitness := Classical.choose_spec leftWitness
  let right := Classical.choose rightWitness
  have hpartitionData := Classical.choose_spec rightWitness
  exact
    { separator := separator
      left := left
      right := right
      separator_subset := hseparator.1
      partition := hpartitionData.2.1
      disjoint := hpartitionData.2.2.1
      left_balance := hpartitionData.2.2.2.1
      right_balance := hpartitionData.2.2.2.2.1
      noEdge := hpartitionData.2.2.2.2.2
      separator_card := hseparator.2.2 }

theorem BGKLSeparatorSplit.left_card_lt
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    (hvertices : 0 < vertices.card) : split.left.card < vertices.card := by
  have hbalance := split.left_balance
  omega

theorem BGKLSeparatorSplit.right_card_lt
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    (hvertices : 0 < vertices.card) : split.right.card < vertices.card := by
  have hbalance := split.right_balance
  omega

/--
The actual finite recursive separator tree.  Leaves are precisely regions below
distance scale `d`; branches contain an explicit minimum separator, its two
balanced children, and recursively constructed child trees.
-/
inductive BGKLSeparatorTree
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) : Finset ι → Type u
  | leaf (vertices : Finset ι) (small : vertices.card < d) :
      BGKLSeparatorTree P d vertices
  | branch {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
      (large : d ≤ vertices.card)
      (leftTree : BGKLSeparatorTree P d split.left)
      (rightTree : BGKLSeparatorTree P d split.right) :
      BGKLSeparatorTree P d vertices

/--
Build the separator tree by well-founded recursion on node cardinality.  The
`2/3` balance inequalities make both recursive calls strictly smaller whenever
the node is not already a distance leaf.
-/
noncomputable def buildBGKLSeparatorTree
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (vertices : Finset ι) :
    BGKLSeparatorTree P d vertices := by
  classical
  by_cases hsmall : vertices.card < d
  · exact .leaf vertices hsmall
  · let split := minimumBGKLSeparatorSplit P vertices
    have hvertices : 0 < vertices.card := lt_of_lt_of_le hd (Nat.le_of_not_gt hsmall)
    exact .branch split (Nat.le_of_not_gt hsmall)
      (buildBGKLSeparatorTree P d hd split.left)
      (buildBGKLSeparatorTree P d hd split.right)
termination_by vertices.card
decreasing_by
  · exact split.left_card_lt hvertices
  · exact split.right_card_lt hvertices

/-- The finite outer boundary of a finite vertex region in the fixed graph. -/
noncomputable def fixedGeneratorOuterBoundaryFinset
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun q => decide
    (q ∈ P.fixedGeneratorOuterBoundary (vertices : Set ι))

theorem mem_fixedGeneratorOuterBoundaryFinset_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) (q : ι) :
    q ∈ fixedGeneratorOuterBoundaryFinset P vertices ↔
      q ∈ P.fixedGeneratorOuterBoundary (vertices : Set ι) := by
  classical
  simp [fixedGeneratorOuterBoundaryFinset]

/-- Union the separator sets accumulated along a root-to-node path. -/
def ancestorSeparatorUnion (separators : List (Finset ι)) : Finset ι :=
  separators.foldr (· ∪ ·) ∅

/-- Sum the separator cardinalities accumulated along a root-to-node path. -/
def ancestorSeparatorCardSum (separators : List (Finset ι)) : Nat :=
  (separators.map Finset.card).sum

/-- A node of a concrete separator tree, together with its ancestor separators. -/
inductive BGKLSeparatorTree.IsNode
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)} {d : Nat} :
    {root : Finset ι} → BGKLSeparatorTree P d root →
      {node : Finset ι} → BGKLSeparatorTree P d node → List (Finset ι) → Prop
  | root {vertices : Finset ι} (tree : BGKLSeparatorTree P d vertices) :
      tree.IsNode tree []
  | left {vertices node : Finset ι} {ancestors : List (Finset ι)}
      (split : BGKLSeparatorSplit P vertices) (large : d ≤ vertices.card)
      (leftTree : BGKLSeparatorTree P d split.left)
      (rightTree : BGKLSeparatorTree P d split.right)
      (nodeTree : BGKLSeparatorTree P d node)
      (hnode : leftTree.IsNode nodeTree ancestors) :
      (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
        nodeTree (split.separator :: ancestors)
  | right {vertices node : Finset ι} {ancestors : List (Finset ι)}
      (split : BGKLSeparatorSplit P vertices) (large : d ≤ vertices.card)
      (leftTree : BGKLSeparatorTree P d split.left)
      (rightTree : BGKLSeparatorTree P d split.right)
      (nodeTree : BGKLSeparatorTree P d node)
      (hnode : rightTree.IsNode nodeTree ancestors) :
      (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
        nodeTree (split.separator :: ancestors)

/-- Compose a root-to-subtree path with a path inside that subtree. -/
theorem BGKLSeparatorTree.IsNode.trans
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)} {d : Nat}
    {globalRoot localRoot node : Finset ι}
    {globalTree : BGKLSeparatorTree P d globalRoot}
    {localTree : BGKLSeparatorTree P d localRoot}
    {globalAncestors localAncestors : List (Finset ι)}
    (hGlobal : globalTree.IsNode localTree globalAncestors)
    (nodeTree : BGKLSeparatorTree P d node)
    (hLocal : localTree.IsNode nodeTree localAncestors) :
    globalTree.IsNode nodeTree (globalAncestors ++ localAncestors) := by
  induction hGlobal with
  | root tree => simpa using hLocal
  | left split large leftTree rightTree localAtPosition hnode ih =>
      simpa using BGKLSeparatorTree.IsNode.left split large leftTree rightTree nodeTree
        (ih hLocal)
  | right split large leftTree rightTree localAtPosition hnode ih =>
      simpa using BGKLSeparatorTree.IsNode.right split large leftTree rightTree nodeTree
        (ih hLocal)

/-- A left child's outer boundary lies in the parent's boundary or separator. -/
theorem BGKLSeparatorSplit.left_outerBoundary_subset
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    fixedGeneratorOuterBoundaryFinset P split.left ⊆
      fixedGeneratorOuterBoundaryFinset P vertices ∪ split.separator := by
  intro q hq
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hq
  rcases hq with ⟨hqLeft, p, hpLeft, hpq⟩
  by_cases hqVertices : q ∈ vertices
  · apply Finset.mem_union_right
    by_contra hqSeparator
    have hqDiff : q ∈ vertices \ split.separator :=
      Finset.mem_sdiff.mpr ⟨hqVertices, hqSeparator⟩
    have hqSides : q ∈ split.left ∪ split.right := by
      rw [split.partition]
      exact hqDiff
    rcases Finset.mem_union.mp hqSides with hqLeft' | hqRight
    · exact hqLeft hqLeft'
    · exact split.noEdge hpLeft hqRight hpq
  · apply Finset.mem_union_left
    rw [mem_fixedGeneratorOuterBoundaryFinset_iff]
    have hpVertices : p ∈ vertices := by
      have hpSides : p ∈ split.left ∪ split.right := Finset.mem_union_left _ hpLeft
      rw [split.partition] at hpSides
      exact (Finset.mem_sdiff.mp hpSides).1
    exact ⟨by simpa using hqVertices, p, hpVertices, hpq⟩

/-- A right child's outer boundary lies in the parent's boundary or separator. -/
theorem BGKLSeparatorSplit.right_outerBoundary_subset
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    fixedGeneratorOuterBoundaryFinset P split.right ⊆
      fixedGeneratorOuterBoundaryFinset P vertices ∪ split.separator := by
  intro q hq
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hq
  rcases hq with ⟨hqRight, p, hpRight, hpq⟩
  by_cases hqVertices : q ∈ vertices
  · apply Finset.mem_union_right
    by_contra hqSeparator
    have hqDiff : q ∈ vertices \ split.separator :=
      Finset.mem_sdiff.mpr ⟨hqVertices, hqSeparator⟩
    have hqSides : q ∈ split.left ∪ split.right := by
      rw [split.partition]
      exact hqDiff
    rcases Finset.mem_union.mp hqSides with hqLeft | hqRight'
    · exact split.noEdge hqLeft hpRight
        (P.fixedGeneratorInteractionGraph.symmetric hpq)
    · exact hqRight hqRight'
  · apply Finset.mem_union_left
    rw [mem_fixedGeneratorOuterBoundaryFinset_iff]
    have hpVertices : p ∈ vertices := by
      have hpSides : p ∈ split.left ∪ split.right := Finset.mem_union_right _ hpRight
      rw [split.partition] at hpSides
      exact (Finset.mem_sdiff.mp hpSides).1
    exact ⟨by simpa using hqVertices, p, hpVertices, hpq⟩

/-- The boundary of a union is contained in the union of the two boundaries. -/
theorem fixedGeneratorOuterBoundaryFinset_union_subset
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) :
    fixedGeneratorOuterBoundaryFinset P (left ∪ right) ⊆
      fixedGeneratorOuterBoundaryFinset P left ∪
        fixedGeneratorOuterBoundaryFinset P right := by
  intro q hq
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hq
  rcases hq with ⟨hqUnion, p, hpUnion, hpq⟩
  have hqLeft : q ∉ left := fun h => hqUnion (Finset.mem_union_left right h)
  have hqRight : q ∉ right := fun h => hqUnion (Finset.mem_union_right left h)
  rcases Finset.mem_union.mp hpUnion with hpLeft | hpRight
  · apply Finset.mem_union_left
    rw [mem_fixedGeneratorOuterBoundaryFinset_iff]
    exact ⟨by simpa using hqLeft, p, hpLeft, hpq⟩
  · apply Finset.mem_union_right
    rw [mem_fixedGeneratorOuterBoundaryFinset_iff]
    exact ⟨by simpa using hqRight, p, hpRight, hpq⟩

/-- Every node boundary is covered by the root boundary and ancestor separators. -/
theorem BGKLSeparatorTree.IsNode.outerBoundary_subset
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)} {d : Nat}
    {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors) :
    fixedGeneratorOuterBoundaryFinset P node ⊆
      fixedGeneratorOuterBoundaryFinset P root ∪ ancestorSeparatorUnion ancestors := by
  induction hnode with
  | root tree => simp [ancestorSeparatorUnion]
  | left split large leftTree rightTree nodeTree hnode ih =>
      intro q hq
      have hq' := ih hq
      rcases Finset.mem_union.mp hq' with hqLeftBoundary | hqAncestors
      · have hparent := split.left_outerBoundary_subset hqLeftBoundary
        rcases Finset.mem_union.mp hparent with hqRoot | hqSeparator
        · exact Finset.mem_union_left _ hqRoot
        · exact Finset.mem_union_right _ (by
            simp [ancestorSeparatorUnion, hqSeparator])
      · exact Finset.mem_union_right _
          (Finset.mem_union_right split.separator hqAncestors)
  | right split large leftTree rightTree nodeTree hnode ih =>
      intro q hq
      have hq' := ih hq
      rcases Finset.mem_union.mp hq' with hqRightBoundary | hqAncestors
      · have hparent := split.right_outerBoundary_subset hqRightBoundary
        rcases Finset.mem_union.mp hparent with hqRoot | hqSeparator
        · exact Finset.mem_union_left _ hqRoot
        · exact Finset.mem_union_right _ (by
            simp [ancestorSeparatorUnion, hqSeparator])
      · exact Finset.mem_union_right _
          (Finset.mem_union_right split.separator hqAncestors)

/-- The source's geometric decay ratio `(2/3)^c`. -/
noncomputable def bgklDecayRatio (exponent : ℝ) : ℝ :=
  Real.rpow (2 / 3 : ℝ) exponent

/-- The exact constant selected in BGKL Lemma `correct-1`. -/
noncomputable def bgklSmallBoundaryEpsilon (beta exponent : ℝ) : ℝ :=
  (1 - bgklDecayRatio exponent) / (20 * beta)

theorem bgklDecayRatio_lt_one {exponent : ℝ} (hexponent : 0 < exponent) :
    bgklDecayRatio exponent < 1 := by
  rw [bgklDecayRatio, ← Real.one_rpow exponent]
  exact Real.rpow_lt_rpow (by norm_num) (by norm_num) hexponent

/-- A selected minimum separator obeys the assumed measured profile bound. -/
theorem BGKLSeparatorSplit.separator_card_le_profile_power
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {beta exponent : ℝ}
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hvertices : 0 < vertices.card) :
    (split.separator.card : ℝ) ≤ beta * Real.rpow vertices.card exponent := by
  have hMinProfile :
      P.fixedGeneratorMinimumTwoThirdsBalancedVertexSeparatorSize vertices ≤
        P.fixedGeneratorTwoThirdsSeparationProfile vertices.card := by
    exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
      P.fixedGeneratorInteractionGraph vertices.card vertices (by simp) le_rfl
  have hMeasured :
      (P.fixedGeneratorTwoThirdsSeparationProfile vertices.card : ℝ) ≤
        beta * Real.rpow vertices.card exponent :=
    hProfile.2.2.2 vertices.card hvertices (Finset.card_le_univ vertices)
  rw [split.separator_card]
  exact (Nat.cast_le.mpr hMinProfile).trans hMeasured

/-- `2/3` balance gives the corresponding real-power decay for the left child. -/
theorem BGKLSeparatorSplit.left_rpow_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {exponent : ℝ} (hexponent : 0 ≤ exponent) :
    Real.rpow split.left.card exponent ≤
      bgklDecayRatio exponent * Real.rpow vertices.card exponent := by
  have hcard : (split.left.card : ℝ) ≤ (2 / 3 : ℝ) * vertices.card := by
    have hcast : (3 : ℝ) * split.left.card ≤ 2 * vertices.card := by
      exact_mod_cast split.left_balance
    linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hcard hexponent
  simpa [bgklDecayRatio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (Nat.cast_nonneg vertices.card)] using hpow

/-- `2/3` balance gives the corresponding real-power decay for the right child. -/
theorem BGKLSeparatorSplit.right_rpow_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {exponent : ℝ} (hexponent : 0 ≤ exponent) :
    Real.rpow split.right.card exponent ≤
      bgklDecayRatio exponent * Real.rpow vertices.card exponent := by
  have hcard : (split.right.card : ℝ) ≤ (2 / 3 : ℝ) * vertices.card := by
    have hcast : (3 : ℝ) * split.right.card ≤ 2 * vertices.card := by
      exact_mod_cast split.right_balance
    linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hcard hexponent
  simpa [bgklDecayRatio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (Nat.cast_nonneg vertices.card)] using hpow

/-- One separator plus one child's remaining potential fits the parent's potential. -/
theorem BGKLSeparatorSplit.separator_add_childPotential_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices child : Finset ι} (split : BGKLSeparatorSplit P vertices)
    {beta exponent : ℝ}
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    (hSeparator : (split.separator.card : ℝ) ≤
      beta * Real.rpow vertices.card exponent)
    (hChild : Real.rpow child.card exponent ≤
      bgklDecayRatio exponent * Real.rpow vertices.card exponent) :
    (split.separator.card : ℝ) +
        beta / (1 - bgklDecayRatio exponent) * Real.rpow child.card exponent ≤
      beta / (1 - bgklDecayRatio exponent) * Real.rpow vertices.card exponent := by
  have hrlt := bgklDecayRatio_lt_one hexponent
  have hden : 0 < 1 - bgklDecayRatio exponent := sub_pos.mpr hrlt
  have hpotential : 0 ≤ beta / (1 - bgklDecayRatio exponent) :=
    div_nonneg (zero_le_one.trans hbeta) hden.le
  have hscaled := mul_le_mul_of_nonneg_left hChild hpotential
  have hid : beta + beta / (1 - bgklDecayRatio exponent) *
      bgklDecayRatio exponent = beta / (1 - bgklDecayRatio exponent) := by
    field_simp
    ring
  calc
    (split.separator.card : ℝ) +
          beta / (1 - bgklDecayRatio exponent) * Real.rpow child.card exponent
        ≤ beta * Real.rpow vertices.card exponent +
          beta / (1 - bgklDecayRatio exponent) * Real.rpow child.card exponent :=
      add_le_add hSeparator le_rfl
    _ ≤ beta * Real.rpow vertices.card exponent +
          beta / (1 - bgklDecayRatio exponent) *
            (bgklDecayRatio exponent * Real.rpow vertices.card exponent) :=
      by simpa only [add_comm] using
        (add_le_add_left hscaled (beta * Real.rpow vertices.card exponent))
    _ = (beta + beta / (1 - bgklDecayRatio exponent) *
          bgklDecayRatio exponent) * Real.rpow vertices.card exponent := by ring
    _ = beta / (1 - bgklDecayRatio exponent) *
          Real.rpow vertices.card exponent := by rw [hid]

/--
The ancestor-separator geometric-series estimate, proved directly on the real
tree.  The residual term is retained, so the estimate does not appeal to an
assumed infinite-series bound.
-/
theorem BGKLSeparatorTree.IsNode.ancestor_sum_add_potential_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent) :
    (ancestorSeparatorCardSum ancestors : ℝ) +
        beta / (1 - bgklDecayRatio exponent) * Real.rpow node.card exponent ≤
      beta / (1 - bgklDecayRatio exponent) * Real.rpow root.card exponent := by
  have hbeta : 1 ≤ beta := hProfile.1
  have hexponentPos : 0 < exponent := hProfile.2.1
  induction hnode with
  | root tree => simp [ancestorSeparatorCardSum]
  | left split large leftTree rightTree nodeTree hnode ih =>
      have hvertices : 0 < _ := lt_of_lt_of_le hd large
      have hsep := split.separator_card_le_profile_power hProfile hvertices
      have hstep := split.separator_add_childPotential_le hbeta hexponentPos hsep
        (split.left_rpow_le hexponentPos.le)
      simp only [ancestorSeparatorCardSum, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
      linarith
  | right split large leftTree rightTree nodeTree hnode ih =>
      have hvertices : 0 < _ := lt_of_lt_of_le hd large
      have hsep := split.separator_card_le_profile_power hProfile hvertices
      have hstep := split.separator_add_childPotential_le hbeta hexponentPos hsep
        (split.right_rpow_le hexponentPos.le)
      simp only [ancestorSeparatorCardSum, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
      linarith

theorem bgklSmallBoundaryEpsilon_pos {beta exponent : ℝ}
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent) :
    0 < bgklSmallBoundaryEpsilon beta exponent := by
  have hratio := bgklDecayRatio_lt_one hexponent
  exact div_pos (sub_pos.mpr hratio) (mul_pos (by norm_num) (zero_lt_one.trans_le hbeta))

/-- The source-size hypothesis converts exactly to the `d/20` path budget. -/
theorem BGKLSeparatorTree.IsNode.ancestor_sum_le_distance_twentieth
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹) :
    (ancestorSeparatorCardSum ancestors : ℝ) ≤ (d : ℝ) / 20 := by
  have hbeta : 1 ≤ beta := hProfile.1
  have hexponentPos : 0 < exponent := hProfile.2.1
  have hepsilon := bgklSmallBoundaryEpsilon_pos hbeta hexponentPos
  have hrootPower : Real.rpow root.card exponent ≤
      bgklSmallBoundaryEpsilon beta exponent * d := by
    exact (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg root.card)
      (mul_nonneg hepsilon.le (Nat.cast_nonneg d)) hexponentPos).mp hSmall
  have hpotential := hnode.ancestor_sum_add_potential_le hd hProfile
  have hcoefficient : 0 ≤ beta / (1 - bgklDecayRatio exponent) := by
    exact div_nonneg (zero_le_one.trans hbeta)
      (sub_nonneg.mpr (bgklDecayRatio_lt_one hexponentPos).le)
  have hrootScaled := mul_le_mul_of_nonneg_left hrootPower hcoefficient
  have hresidual : 0 ≤ beta / (1 - bgklDecayRatio exponent) *
      Real.rpow node.card exponent :=
    mul_nonneg hcoefficient (Real.rpow_nonneg (Nat.cast_nonneg node.card) _)
  have hconstant : beta / (1 - bgklDecayRatio exponent) *
      (bgklSmallBoundaryEpsilon beta exponent * (d : ℝ)) = (d : ℝ) / 20 := by
    rw [bgklSmallBoundaryEpsilon]
    have hbeta0 : beta ≠ 0 := ne_of_gt (zero_lt_one.trans_le hbeta)
    have hden0 : 1 - bgklDecayRatio exponent ≠ 0 :=
      ne_of_gt (sub_pos.mpr (bgklDecayRatio_lt_one hexponentPos))
    field_simp
  rw [hconstant] at hrootScaled
  linarith

/-- The union of a path's separators has at most the sum of their sizes. -/
theorem ancestorSeparatorUnion_card_le_sum
    {α : Type u} [DecidableEq α] (separators : List (Finset α)) :
    (ancestorSeparatorUnion separators).card ≤ ancestorSeparatorCardSum separators := by
  induction separators with
  | nil => simp [ancestorSeparatorUnion, ancestorSeparatorCardSum]
  | cons separator separators ih =>
      simp only [ancestorSeparatorUnion, List.foldr_cons, ancestorSeparatorCardSum,
        List.map_cons, List.sum_cons]
      exact (Finset.card_union_le separator (ancestorSeparatorUnion separators)).trans
        (Nat.add_le_add_left ih separator.card)

/-- Every tree-node boundary obeys the source's `3d/10` estimate. -/
theorem BGKLSeparatorTree.IsNode.outerBoundary_card_le_three_tenths
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hRootBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d) :
    ((fixedGeneratorOuterBoundaryFinset P node).card : ℝ) ≤ 3 * (d : ℝ) / 10 := by
  have hsubset := hnode.outerBoundary_subset
  have hnodeCard : (fixedGeneratorOuterBoundaryFinset P node).card ≤
      (fixedGeneratorOuterBoundaryFinset P root).card +
        (ancestorSeparatorUnion ancestors).card := by
    exact (Finset.card_le_card hsubset).trans
      (Finset.card_union_le _ _)
  have hancestorUnion : (ancestorSeparatorUnion ancestors).card ≤
      ancestorSeparatorCardSum ancestors := ancestorSeparatorUnion_card_le_sum ancestors
  have hancestor := hnode.ancestor_sum_le_distance_twentieth
    hd hProfile hSmall
  have hrootBoundaryReal :
      ((fixedGeneratorOuterBoundaryFinset P root).card : ℝ) ≤ (d : ℝ) / 4 := by
    have hcast : (4 : ℝ) * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d := by
      exact_mod_cast hRootBoundary
    linarith
  have hnodeCardReal : ((fixedGeneratorOuterBoundaryFinset P node).card : ℝ) ≤
      ((fixedGeneratorOuterBoundaryFinset P root).card : ℝ) +
        (ancestorSeparatorCardSum ancestors : ℝ) := by
    exact_mod_cast hnodeCard.trans (Nat.add_le_add_left hancestorUnion _)
  linarith

/-- Concrete qubit erasure recovery is monotone under shrinking the selected set. -/
theorem exists_erasureRecovery_of_finiteSubsystem_subset
    (S T : FiniteSubsystem ι) (hST : S.selected ⊆ T.selected)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (hRecovery : ∃ recovery : QuantumChannel T.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) T.complementSystem C
        T.erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by
  exact
    (exists_qudit_erasureRecovery_of_subset
      (quditSubsystemOfFinite S) (quditSubsystemOfFinite T) hST C hRecovery)

/-- A branch's retained children form the exact parent-minus-separator region. -/
theorem BGKLSeparatorSplit.vertices_subset_children_union_separator
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    vertices ⊆ (split.left ∪ split.right) ∪ split.separator := by
  intro q hq
  by_cases hqSeparator : q ∈ split.separator
  · exact Finset.mem_union_right _ hqSeparator
  · apply Finset.mem_union_left
    rw [split.partition]
    exact Finset.mem_sdiff.mpr ⟨hq, hqSeparator⟩

/-- The two child regions are fixed-generator decoupled, as required by #373. -/
theorem BGKLSeparatorSplit.children_decoupled
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    P.fixedGeneratorDecoupled (split.left : Set ι) (split.right : Set ι) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro q hqLeft hqRight
    exact (Finset.disjoint_left.mp split.disjoint) hqLeft hqRight
  · intro p hp q hq
    exact split.noEdge hp hq

/--
Structural recovery induction on the constructed tree.  Leaves invoke semantic
distance (#363); branches combine the two decoupled children (#373), correct a
distance-small boundary/separator buffer, expand across that buffer (#377), and
finally shrink to the parent vertex set.
-/
theorem exists_erasureRecovery_of_BGKLSeparatorTree_node
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {beta exponent : ℝ}
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    {root : Finset ι} (globalTree : BGKLSeparatorTree P d root)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hRootBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d)
    {vertices : Finset ι} (subtree : BGKLSeparatorTree P d vertices)
    {ancestors : List (Finset ι)}
    (hPosition : globalTree.IsNode subtree ancestors) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset vertices).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset vertices).complementSystem P.semanticCode
        (finiteSubsystemOfFinset vertices).erasureChannelFromRegister recovery := by
  induction subtree generalizing ancestors with
  | leaf vertices hLeaf =>
      simpa [finiteSubsystemOfFinset, StabilizerCode.BinaryStabilizerPresentation.semanticCode]
        using semanticStabilizerDistance_erasureRecoverableFromRegister
          P.code d hDistance (finiteSubsystemOfFinset vertices) hLeaf
  | @branch vertices split large leftTree rightTree ihLeft ihRight =>
      have hLeftLocal :
          (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
            leftTree [split.separator] := by
        exact BGKLSeparatorTree.IsNode.left split large leftTree rightTree leftTree
          (BGKLSeparatorTree.IsNode.root leftTree)
      have hRightLocal :
          (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
            rightTree [split.separator] := by
        exact BGKLSeparatorTree.IsNode.right split large leftTree rightTree rightTree
          (BGKLSeparatorTree.IsNode.root rightTree)
      have hLeftPosition := hPosition.trans leftTree hLeftLocal
      have hRightPosition := hPosition.trans rightTree hRightLocal
      rcases ihLeft hLeftPosition with ⟨recoveryLeft, hRecoveryLeft⟩
      rcases ihRight hRightPosition with ⟨recoveryRight, hRecoveryRight⟩
      let leftSubsystem := finiteSubsystemOfFinset split.left
      let rightSubsystem := finiteSubsystemOfFinset split.right
      have hDecoupled : P.fixedGeneratorDecoupled
          (leftSubsystem.selected : Set ι) (rightSubsystem.selected : Set ι) := by
        simpa [leftSubsystem, rightSubsystem, finiteSubsystemOfFinset] using
          split.children_decoupled
      obtain ⟨recoveryChildren, hRecoveryChildren⟩ :=
        exists_erasureRecovery_of_fixedGeneratorDecoupled P
          leftSubsystem rightSubsystem recoveryLeft recoveryRight
          (by simpa [leftSubsystem] using hRecoveryLeft)
          (by simpa [rightSubsystem] using hRecoveryRight) hDecoupled
      let children := split.left ∪ split.right
      let childrenSubsystem := unionSubsystem leftSubsystem rightSubsystem
      have hChildrenSelected : childrenSubsystem.selected = children := by
        rfl
      let buffer := fixedGeneratorOuterBoundaryFinset P children ∪ split.separator
      let bufferSubsystem := finiteSubsystemOfFinset buffer
      have hLeftBoundary := hLeftPosition.outerBoundary_card_le_three_tenths
        hd hProfile hSmall hRootBoundary
      have hRightBoundary := hRightPosition.outerBoundary_card_le_three_tenths
        hd hProfile hSmall hRootBoundary
      have hChildrenBoundarySubset :=
        fixedGeneratorOuterBoundaryFinset_union_subset P split.left split.right
      have hChildrenBoundaryCard :
          (fixedGeneratorOuterBoundaryFinset P children).card ≤
            (fixedGeneratorOuterBoundaryFinset P split.left).card +
              (fixedGeneratorOuterBoundaryFinset P split.right).card := by
        exact (Finset.card_le_card hChildrenBoundarySubset).trans (Finset.card_union_le _ _)
      have hAncestorBudget := hLeftPosition.ancestor_sum_le_distance_twentieth
        hd hProfile hSmall
      have hSeparatorInBudget : split.separator.card ≤
          ancestorSeparatorCardSum (ancestors ++ [split.separator]) := by
        simp [ancestorSeparatorCardSum]
      have hSeparatorReal : (split.separator.card : ℝ) ≤ (d : ℝ) / 20 := by
        have hCast : (split.separator.card : ℝ) ≤
            (ancestorSeparatorCardSum (ancestors ++ [split.separator]) : ℝ) := by
          exact_mod_cast hSeparatorInBudget
        exact hCast.trans hAncestorBudget
      have hBufferCardNat : buffer.card ≤
          (fixedGeneratorOuterBoundaryFinset P children).card + split.separator.card := by
        exact Finset.card_union_le _ _
      have hBufferCardReal : (buffer.card : ℝ) ≤ 13 * (d : ℝ) / 20 := by
        have hChildrenBoundaryCardReal :
            ((fixedGeneratorOuterBoundaryFinset P children).card : ℝ) ≤
              ((fixedGeneratorOuterBoundaryFinset P split.left).card : ℝ) +
                ((fixedGeneratorOuterBoundaryFinset P split.right).card : ℝ) := by
          exact_mod_cast hChildrenBoundaryCard
        have hBufferCardCast : (buffer.card : ℝ) ≤
            ((fixedGeneratorOuterBoundaryFinset P children).card : ℝ) +
              (split.separator.card : ℝ) := by
          exact_mod_cast hBufferCardNat
        linarith
      have hBufferSmall : buffer.card < d := by
        have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
        exact_mod_cast (hBufferCardReal.trans_lt (by linarith : 13 * (d : ℝ) / 20 < d))
      obtain ⟨recoveryBuffer, hRecoveryBuffer⟩ :=
        semanticStabilizerDistance_erasureRecoverableFromRegister
          P.code d hDistance bufferSubsystem (by
            simpa [bufferSubsystem, finiteSubsystemOfFinset] using hBufferSmall)
      have hBoundary : P.fixedGeneratorOuterBoundary
          (childrenSubsystem.selected : Set ι) ⊆ (bufferSubsystem.selected : Set ι) := by
        intro q hq
        have hqFinset : q ∈ fixedGeneratorOuterBoundaryFinset P children := by
          rw [mem_fixedGeneratorOuterBoundaryFinset_iff]
          simpa [hChildrenSelected] using hq
        simp [bufferSubsystem, finiteSubsystemOfFinset, buffer, hqFinset]
      obtain ⟨recoveryExpanded, hRecoveryExpanded⟩ :=
        exists_erasureRecovery_of_fixedGeneratorOuterBoundary_subset
          P childrenSubsystem bufferSubsystem recoveryChildren recoveryBuffer
          (by simpa [childrenSubsystem] using hRecoveryChildren)
          (by simpa [StabilizerCode.BinaryStabilizerPresentation.semanticCode]
            using hRecoveryBuffer) hBoundary
      have hParentSubset : (finiteSubsystemOfFinset vertices).selected ⊆
          (unionSubsystem childrenSubsystem bufferSubsystem).selected := by
        intro q hq
        have hqCover := split.vertices_subset_children_union_separator hq
        rcases Finset.mem_union.mp hqCover with hqChildren | hqSeparator
        · apply Finset.mem_union_left
          rw [hChildrenSelected]
          exact hqChildren
        · exact Finset.mem_union_right _ (by
            simp [bufferSubsystem, finiteSubsystemOfFinset, buffer, hqSeparator])
      exact exists_erasureRecovery_of_finiteSubsystem_subset
        (finiteSubsystemOfFinset vertices)
        (unionSubsystem childrenSubsystem bufferSubsystem) hParentSubset P.semanticCode
        ⟨recoveryExpanded, hRecoveryExpanded⟩

/--
BGKL small-boundary correctability (`lem:correct-1`) for the fixed-generator
interaction graph.  The constants and ranges are the source constants:
`beta ≥ 1`, `0 < exponent < 1`, `0 < d ≤ n`,
`|W| ≤ (epsilon' d)^(1/exponent)`, and `|∂₊W| ≤ d/4`, where
`epsilon' = (1 - (2/3)^exponent) / (20 beta)`.

The conclusion contains the concrete CPTP recovery for erasure of `W`; it is
not a stored correctability assumption or a target tradeoff premise.
-/
theorem bgklSmallBoundaryCorrectable
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (W : Finset ι)
    (hSmall : (W.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P W).card ≤ d) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset W).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset W).complementSystem P.semanticCode
        (finiteSubsystemOfFinset W).erasureChannelFromRegister recovery := by
  let _ : 0 < Fintype.card ι := hd.trans_le hdn
  let _ : 0 < 1 - exponent := sub_pos.mpr hexponent
  let tree := buildBGKLSeparatorTree P d hd W
  exact exists_erasureRecovery_of_BGKLSeparatorTree_node
    P d hd hDistance hProfile tree hSmall hBoundary tree
      (BGKLSeparatorTree.IsNode.root tree)

end QEC.Locality

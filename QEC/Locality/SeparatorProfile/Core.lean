import QEC.Coding.Stabilizer.FixedGeneratorInteraction

/-!
# Exact finite separator profiles

The measured separation profile in this module is the maximum, over explicitly
enumerated induced subgraphs of bounded cardinality, of the minimum size of a
`2/3`-balanced vertex separator.  Upper bounds are separate hypothesis
predicates and are never stored as the measured profile itself.
-/

namespace QEC.Locality

universe u

/-- All `2/3`-balanced separator candidates of one explicitly induced vertex set. -/
noncomputable def twoThirdsBalancedSeparatorCandidates {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset (Finset ι) := by
  classical
  exact vertices.powerset.filter
    (fun separator => decide (IsTwoThirdsBalancedVertexSeparator G vertices separator))

/-- A finite separator belongs to the candidate list exactly when it is admissible. -/
theorem mem_twoThirdsBalancedSeparatorCandidates_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices separator : Finset ι) :
    separator ∈ twoThirdsBalancedSeparatorCandidates G vertices ↔
      separator ⊆ vertices ∧ IsTwoThirdsBalancedVertexSeparator G vertices separator := by
  classical
  simp [twoThirdsBalancedSeparatorCandidates]

/-- The finite candidate list is nonempty because deleting all vertices is allowed. -/
theorem twoThirdsBalancedSeparatorCandidates_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (twoThirdsBalancedSeparatorCandidates G vertices).Nonempty := by
  refine ⟨vertices, (mem_twoThirdsBalancedSeparatorCandidates_iff G vertices vertices).2 ?_⟩
  exact ⟨subset_rfl, self_isTwoThirdsBalancedVertexSeparator G vertices⟩

/-- The finite multiset of cardinalities of all admissible `2/3` separators. -/
noncomputable def twoThirdsBalancedSeparatorCardinalities {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Finset Nat :=
  (twoThirdsBalancedSeparatorCandidates G vertices).image Finset.card

/-- The enumerated separator cardinalities are nonempty. -/
theorem twoThirdsBalancedSeparatorCardinalities_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    (twoThirdsBalancedSeparatorCardinalities G vertices).Nonempty := by
  rcases twoThirdsBalancedSeparatorCandidates_nonempty G vertices with ⟨separator, hseparator⟩
  exact ⟨separator.card, Finset.mem_image.2 ⟨separator, hseparator, rfl⟩⟩

/--
The minimum `2/3`-balanced vertex-separator size of the induced graph on
`vertices`, computed from the finite candidate list.
-/
noncomputable def minimumTwoThirdsBalancedVertexSeparatorSize {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) : Nat :=
  (twoThirdsBalancedSeparatorCardinalities G vertices).min'
    (twoThirdsBalancedSeparatorCardinalities_nonempty G vertices)

/-- The measured minimum is witnessed by an explicit finite separator. -/
theorem exists_minimumTwoThirdsBalancedVertexSeparator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ∃ separator : Finset ι,
      separator ⊆ vertices ∧
        IsTwoThirdsBalancedVertexSeparator G vertices separator ∧
        separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by
  classical
  have hmem : minimumTwoThirdsBalancedVertexSeparatorSize G vertices ∈
      twoThirdsBalancedSeparatorCardinalities G vertices := by
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.1 hmem with ⟨separator, hseparator, hcard⟩
  rcases (mem_twoThirdsBalancedSeparatorCandidates_iff G vertices separator).1 hseparator with
    ⟨hsubset, hbalanced⟩
  exact ⟨separator, hsubset, hbalanced, hcard⟩

/-- The measured minimum is no larger than every explicit admissible separator. -/
theorem minimumTwoThirdsBalancedVertexSeparatorSize_le_card {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices separator : Finset ι)
    (hsubset : separator ⊆ vertices)
    (hbalanced : IsTwoThirdsBalancedVertexSeparator G vertices separator) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤ separator.card := by
  classical
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨separator,
    (mem_twoThirdsBalancedSeparatorCandidates_iff G vertices separator).2
      ⟨hsubset, hbalanced⟩, rfl⟩

/-- The measured minimum is at most the cardinality of its induced vertex set. -/
theorem minimumTwoThirdsBalancedVertexSeparatorSize_le_vertex_card {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤ vertices.card :=
  minimumTwoThirdsBalancedVertexSeparatorSize_le_card G vertices vertices subset_rfl
    (self_isTwoThirdsBalancedVertexSeparator G vertices)

/-- All explicitly induced subgraphs with at most `scale` vertices. -/
noncomputable def inducedVertexSetsAtMost {ι : Type u} [Fintype ι] [DecidableEq ι]
    (scale : Nat) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun vertices => vertices.card ≤ scale)

/-- Membership makes both the induced-subgraph and cardinality quantifiers explicit. -/
theorem mem_inducedVertexSetsAtMost_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (scale : Nat) (vertices : Finset ι) :
    vertices ∈ inducedVertexSetsAtMost (ι := ι) scale ↔
      vertices ⊆ Finset.univ ∧ vertices.card ≤ scale := by
  classical
  simp [inducedVertexSetsAtMost]

/-- The finite family of induced subgraphs at any scale contains the empty graph. -/
theorem inducedVertexSetsAtMost_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (scale : Nat) : (inducedVertexSetsAtMost (ι := ι) scale).Nonempty := by
  refine ⟨∅, (mem_inducedVertexSetsAtMost_iff scale ∅).2 ?_⟩
  simp

/-- The measured minimum separator sizes for all induced subgraphs at one scale. -/
noncomputable def inducedMinimumTwoThirdsBalancedSeparatorSizes {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) : Finset Nat :=
  (inducedVertexSetsAtMost (ι := ι) scale).image
    (minimumTwoThirdsBalancedVertexSeparatorSize G)

/-- The finite set of measured induced-subgraph separator sizes is nonempty. -/
theorem inducedMinimumTwoThirdsBalancedSeparatorSizes_nonempty {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) :
    (inducedMinimumTwoThirdsBalancedSeparatorSizes G scale).Nonempty := by
  rcases inducedVertexSetsAtMost_nonempty (ι := ι) scale with ⟨vertices, hvertices⟩
  exact ⟨minimumTwoThirdsBalancedVertexSeparatorSize G vertices,
    Finset.mem_image.2 ⟨vertices, hvertices, rfl⟩⟩

/--
The exact `2/3` separation profile: the finite maximum of minimum separator
sizes over every induced subgraph with cardinality at most `scale`.
-/
noncomputable def twoThirdsSeparationProfile {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (scale : Nat) : Nat :=
  (inducedMinimumTwoThirdsBalancedSeparatorSizes G scale).max'
    (inducedMinimumTwoThirdsBalancedSeparatorSizes_nonempty G scale)

/-- The measured profile maximum is attained by an explicit induced vertex set. -/
theorem exists_inducedVertexSet_attaining_twoThirdsSeparationProfile
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (scale : Nat) :
    ∃ vertices : Finset ι,
      vertices ⊆ Finset.univ ∧ vertices.card ≤ scale ∧
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices =
          twoThirdsSeparationProfile G scale := by
  classical
  have hmem : twoThirdsSeparationProfile G scale ∈
      inducedMinimumTwoThirdsBalancedSeparatorSizes G scale := by
    exact Finset.max'_mem _ _
  rcases Finset.mem_image.1 hmem with ⟨vertices, hvertices, hvalue⟩
  rcases (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices with ⟨hsubset, hcard⟩
  exact ⟨vertices, hsubset, hcard, hvalue⟩

/-- Every induced graph below `scale` contributes a value bounded by the measured profile. -/
theorem minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (scale : Nat) (vertices : Finset ι)
    (hsubset : vertices ⊆ Finset.univ) (hcard : vertices.card ≤ scale) :
    minimumTwoThirdsBalancedVertexSeparatorSize G vertices ≤
      twoThirdsSeparationProfile G scale := by
  classical
  apply Finset.le_max'
  exact Finset.mem_image.2 ⟨vertices,
    (mem_inducedVertexSetsAtMost_iff scale vertices).2 ⟨hsubset, hcard⟩, rfl⟩

/-- The measured profile is monotone in its induced-subgraph cardinality bound. -/
theorem twoThirdsSeparationProfile_mono {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) {small large : Nat} (hscale : small ≤ large) :
    twoThirdsSeparationProfile G small ≤ twoThirdsSeparationProfile G large := by
  classical
  apply Finset.max'_le
  intro size hsize
  rcases Finset.mem_image.1 hsize with ⟨vertices, hvertices, hvalue⟩
  rw [← hvalue]
  have hsmallVertices := (mem_inducedVertexSetsAtMost_iff small vertices).1 hvertices
  exact minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
    G large vertices hsmallVertices.1 (hsmallVertices.2.trans hscale)

/--
An assumed upper-bound witness for the measured `2/3` separation profile.
This is a hypothesis interface; it does not define or alter the measured
profile.
-/
def AssumedTwoThirdsSeparationProfileUpperBound {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (bound : Nat → Nat) : Prop :=
  ∀ scale : Nat, twoThirdsSeparationProfile G scale ≤ bound scale

/-- An assumed BK-style exponent upper bound for the measured profile on explicit scales. -/
noncomputable def AssumedBKMeasuredProfileExponentUpperBound
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (cMax : ℝ) : Prop :=
  ∀ scale : Nat, 1 ≤ scale → scale ≤ Fintype.card ι →
    (twoThirdsSeparationProfile G scale : ℝ) ≤ Real.rpow scale cMax

/-- An assumed BGKL-style power upper bound for the measured profile on explicit scales. -/
noncomputable def AssumedBGKLMeasuredProfilePowerUpperBound
    {ι : Type u} [Fintype ι] [DecidableEq ι] (G : ConnectivityGraph ι) (beta exponent : ℝ) : Prop :=
  1 ≤ beta ∧ 0 < exponent ∧ exponent ≤ 1 ∧
    ∀ scale : Nat, 1 ≤ scale → scale ≤ Fintype.card ι →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * Real.rpow scale exponent

end QEC.Locality

namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

open PauliSymplectic

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The fixed-generator interaction graph induced by an explicitly selected vertex set. -/
def fixedGeneratorInducedSubgraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι) :
    Locality.ConnectivityGraph {i : ι // i ∈ vertices} :=
  Locality.inducedSubgraph P.fixedGeneratorInteractionGraph vertices

/-- Induced adjacency retains the actual selected-generator support characterization. -/
theorem fixedGeneratorInducedSubgraph_adj_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι)
    (p q : {i : ι // i ∈ vertices}) :
    (P.fixedGeneratorInducedSubgraph vertices).adjacent p q ↔
      p.1 ≠ q.1 ∧ ∃ j : κ,
        p.1 ∈ support (P.generators j) ∧ q.1 ∈ support (P.generators j) :=
  P.fixedGeneratorInteractionGraph_adj_iff_actual_support p.1 q.1

/-- There is no fixed-generator interaction edge between the two finite regions. -/
def fixedGeneratorNoEdgeBetween
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) : Prop :=
  Locality.NoEdgeBetween P.fixedGeneratorInteractionGraph left right

/--
Finite-region nonadjacency is exactly the absence of common actual support in
every selected generator.
-/
theorem fixedGeneratorNoEdgeBetween_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) :
    P.fixedGeneratorNoEdgeBetween left right ↔
      ∀ ⦃p : ι⦄, p ∈ left → ∀ ⦃q : ι⦄, q ∈ right →
        ¬ (p ≠ q ∧ ∃ j : κ,
          p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · intro h p hp q hq hsupport
    apply h hp hq
    exact (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2 hsupport
  · intro h p hp q hq hadjacent
    exact h hp hq
      ((P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hadjacent)

/-- The fixed-generator version of the explicit `2/3` balanced separator predicate. -/
def IsFixedGeneratorTwoThirdsBalancedVertexSeparator
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices separator : Finset ι) : Prop :=
  Locality.IsTwoThirdsBalancedVertexSeparator P.fixedGeneratorInteractionGraph vertices separator

/--
The fixed-generator `2/3` separator predicate is exactly a finite
partition-after-deletion with no common actual generator support across the
two retained regions.
-/
theorem isFixedGeneratorTwoThirdsBalancedVertexSeparator_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices separator : Finset ι) :
    P.IsFixedGeneratorTwoThirdsBalancedVertexSeparator vertices separator ↔
      ∃ left right : Finset ι,
        separator ⊆ vertices ∧
          left ∪ right = vertices \ separator ∧
          Disjoint left right ∧
          3 * left.card ≤ 2 * vertices.card ∧
          3 * right.card ≤ 2 * vertices.card ∧
          ∀ ⦃p : ι⦄, p ∈ left → ∀ ⦃q : ι⦄, q ∈ right →
            ¬ (p ≠ q ∧ ∃ j : κ,
              p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · rintro ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright, hnoedge⟩
    exact ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright,
      (P.fixedGeneratorNoEdgeBetween_iff_actual_support left right).1 hnoedge⟩
  · rintro ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright, hnoedge⟩
    exact ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright,
      (P.fixedGeneratorNoEdgeBetween_iff_actual_support left right).2 hnoedge⟩

/-- The finite minimum `2/3` separator size of one induced fixed-generator graph. -/
noncomputable def fixedGeneratorMinimumTwoThirdsBalancedVertexSeparatorSize
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (vertices : Finset ι) : Nat :=
  Locality.minimumTwoThirdsBalancedVertexSeparatorSize
    P.fixedGeneratorInteractionGraph vertices

/-- The exact measured `2/3` separation profile of the chosen fixed generator graph. -/
noncomputable def fixedGeneratorTwoThirdsSeparationProfile
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (scale : Nat) : Nat :=
  Locality.twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale

/-- The fixed-generator profile is the measured finite maximum, not an input bound. -/
theorem fixedGeneratorTwoThirdsSeparationProfile_eq_measured
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (scale : Nat) :
    P.fixedGeneratorTwoThirdsSeparationProfile scale =
      Locality.twoThirdsSeparationProfile P.fixedGeneratorInteractionGraph scale :=
  rfl

/-- A separate assumed upper-bound witness for the measured fixed-generator profile. -/
def AssumedFixedGeneratorTwoThirdsSeparationProfileUpperBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (bound : Nat → Nat) : Prop :=
  Locality.AssumedTwoThirdsSeparationProfileUpperBound
    P.fixedGeneratorInteractionGraph bound

/-- A separate BK-style hypothesis over the measured fixed-generator profile. -/
noncomputable def AssumedFixedGeneratorBKMeasuredProfileExponentUpperBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (cMax : ℝ) : Prop :=
  Locality.AssumedBKMeasuredProfileExponentUpperBound
    P.fixedGeneratorInteractionGraph cMax

/-- A separate BGKL-style hypothesis over the measured fixed-generator profile. -/
noncomputable def AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (beta exponent : ℝ) : Prop :=
  Locality.AssumedBGKLMeasuredProfilePowerUpperBound
    P.fixedGeneratorInteractionGraph beta exponent

end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

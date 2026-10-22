import QEC.Coding.FiberBundle.TwistGraphLTC

/-!
# Mixing events for the HHO20 twist graph

This module isolates the graph-theoretic part of HHO20 Theorem `thm:ltc`.
It proves that the theorem's small global word bound forces the displayed
`.00005` heavy-layer and `.9999` light-layer cardinality bounds.  It also
states the two integer-cleared oriented-edge estimates supplied by the
Expander Mixing Lemma.

The edge-mixing predicate is an internal event of the sampled type twists.
The final construction must prove it from the explicit random twist sampler;
it is not accepted by the public qLDPC family theorem.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators

/-- Oriented in/out neighbor incidences from `source` into `target`. -/
noncomputable def neighborEdgeCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (source target : Finset (ZMod ell)) : Nat :=
  ∑ u ∈ source, neighborIncidenceCount twistSample target u

/-- The three HHO20 layer classes contain every layer exactly once. -/
theorem card_light_add_medium_add_heavy
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (lightLayerSet Delta w).card +
        (mediumLayerSet Delta w).card +
        (heavyLayerSet Delta w).card =
      ell := by
  have hLM :
      Disjoint (lightLayerSet Delta w) (mediumLayerSet Delta w) := by
    refine Finset.disjoint_left.mpr ?_
    intro u hu hv
    rw [mem_lightLayerSet_iff] at hu
    rw [mem_mediumLayerSet_iff] at hv
    omega
  calc
    _ = (lightLayerSet Delta w ∪ mediumLayerSet Delta w).card +
          (heavyLayerSet Delta w).card := by
      rw [Finset.card_union_of_disjoint hLM]
    _ = (nonheavyLayerSet Delta w).card +
          (heavyLayerSet Delta w).card := by
      rw [lightLayerSet_union_mediumLayerSet]
    _ = (nonheavyLayerSet Delta w ∪ heavyLayerSet Delta w).card := by
      rw [Finset.card_union_of_disjoint
        (disjoint_nonheavyLayerSet_heavyLayerSet Delta w)]
    _ = ell := by
      rw [nonheavyLayerSet_union_heavyLayerSet]
      simp

/--
The small global word bound forces the cardinality estimates used before the
two cases of HHO20 `thm:ltc`:

* `|H| / ell ≤ .00005`;
* `|L| / ell ≥ .9999`.
-/
theorem layer_cardinality_bounds_of_small
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hsmall :
      5000 * Delta * HammingWeight w ≤ ell * (4 * r)) :
    20000 * (heavyLayerSet Delta w).card ≤ ell ∧
      9999 * ell ≤ 10000 * (lightLayerSet Delta w).card := by
  let lightCount := (lightLayerSet Delta w).card
  let mediumCount := (mediumLayerSet Delta w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let n := 4 * r
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne r))
  have hHeavyMass :
      4 * n * heavyCount ≤ Delta * HammingWeight w := by
    calc
      4 * n * heavyCount =
          ∑ _u ∈ heavyLayerSet Delta w, 4 * n := by
        simp [heavyCount, Nat.mul_comm]
      _ ≤ ∑ u ∈ heavyLayerSet Delta w,
          Delta * HammingWeight (layerWord w u) := by
        apply Finset.sum_le_sum
        intro u hu
        simpa [n] using (mem_heavyLayerSet_iff Delta w u).mp hu
      _ = Delta *
          (∑ u ∈ heavyLayerSet Delta w,
            HammingWeight (layerWord w u)) := by
        rw [Finset.mul_sum]
      _ ≤ Delta * HammingWeight w := by
        rw [hammingWeight_eq_nonheavy_add_heavy Delta w]
        exact Nat.mul_le_mul_left Delta (Nat.le_add_left _ _)
  have hHeavyScaled :
      n * (20000 * heavyCount) ≤ n * ell := by
    calc
      n * (20000 * heavyCount) =
          5000 * (4 * n * heavyCount) := by ring
      _ ≤ 5000 * (Delta * HammingWeight w) :=
        Nat.mul_le_mul_left 5000 hHeavyMass
      _ = 5000 * Delta * HammingWeight w := by ring
      _ ≤ ell * (4 * r) := hsmall
      _ = n * ell := by simp [n, Nat.mul_comm]
  have hHeavyCard :
      20000 * heavyCount ≤ ell :=
    Nat.le_of_mul_le_mul_left hHeavyScaled hn
  have hMediumHeavyMass :
      2 * n * (mediumCount + heavyCount) ≤
        Delta * HammingWeight w := by
    have hMH :
        Disjoint (mediumLayerSet Delta w) (heavyLayerSet Delta w) := by
      refine Finset.disjoint_left.mpr ?_
      intro u hu hv
      rw [mem_mediumLayerSet_iff] at hu
      rw [mem_heavyLayerSet_iff] at hv
      omega
    calc
      2 * n * (mediumCount + heavyCount) =
          (∑ _u ∈ mediumLayerSet Delta w, 2 * n) +
            ∑ _u ∈ heavyLayerSet Delta w, 2 * n := by
        rw [Finset.sum_const_nat (fun _ _ => rfl),
          Finset.sum_const_nat (fun _ _ => rfl)]
        dsimp only [mediumCount, heavyCount]
        ring
      _ = ∑ _u ∈ mediumLayerSet Delta w ∪ heavyLayerSet Delta w,
            2 * n := by
        exact (Finset.sum_union hMH).symm
      _ ≤ ∑ u ∈ mediumLayerSet Delta w ∪ heavyLayerSet Delta w,
          Delta * HammingWeight (layerWord w u) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Finset.mem_union] at hu
        rcases hu with hu | hu
        · exact Nat.le_of_lt
            ((mem_mediumLayerSet_iff Delta w u).mp hu).1
        · have hhu := (mem_heavyLayerSet_iff Delta w u).mp hu
          omega
      _ ≤ ∑ u : ZMod ell,
          Delta * HammingWeight (layerWord w u) := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = Delta * HammingWeight w := by
        rw [← Finset.mul_sum, hammingWeight_eq_sum_layerWord]
  have hNonlightScaled :
      n * (10000 * (mediumCount + heavyCount)) ≤ n * ell := by
    calc
      n * (10000 * (mediumCount + heavyCount)) =
          5000 * (2 * n * (mediumCount + heavyCount)) := by ring
      _ ≤ 5000 * (Delta * HammingWeight w) :=
        Nat.mul_le_mul_left 5000 hMediumHeavyMass
      _ = 5000 * Delta * HammingWeight w := by ring
      _ ≤ ell * (4 * r) := hsmall
      _ = n * ell := by simp [n, Nat.mul_comm]
  have hNonlight :
      10000 * (mediumCount + heavyCount) ≤ ell :=
    Nat.le_of_mul_le_mul_left hNonlightScaled hn
  have hPartition :
      lightCount + mediumCount + heavyCount = ell := by
    exact card_light_add_medium_add_heavy Delta w
  refine ⟨?_, ?_⟩
  · exact hHeavyCard
  · omega

/--
The two oriented-edge estimates obtained from the Expander Mixing Lemma after
substituting the `.00005` heavy and `.9999` light cardinality bounds.

The upper estimate is the paper's `1.1 theta_H` bound, and the lower estimate
is its `.999` light-neighbor bound in the heavy case.  Denominators are
cleared over the exact `2 * typeCount` directed neighbor incidences.
-/
def HasHHO20EdgeMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ w : Word (ZMod 2) (ZMod ell × Fin (4 * r)),
    20000 * (heavyLayerSet Delta w).card ≤ ell →
    9999 * ell ≤ 10000 * (lightLayerSet Delta w).card →
      10 * ell *
          neighborEdgeCount twistSample
            (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) ≤
        22 * typeCount *
          (nonheavyLayerSet Delta w).card *
          (heavyLayerSet Delta w).card ∧
      ((mediumLayerSet Delta w).card <
          1000 * (heavyLayerSet Delta w).card →
        1998 * typeCount * (heavyLayerSet Delta w).card ≤
          1000 *
            neighborEdgeCount twistSample
              (heavyLayerSet Delta w) (lightLayerSet Delta w))

/-- Every layer has exactly two directed incidences per type. -/
theorem neighborIncidenceCount_univ
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : ZMod ell) :
    neighborIncidenceCount twistSample Finset.univ u =
      2 * typeCount := by
  simp [neighborIncidenceCount, Nat.mul_comm]

/-- Neighbor-incidence counts add across disjoint target sets. -/
theorem neighborIncidenceCount_union
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (left right : Finset (ZMod ell))
    (hdisjoint : Disjoint left right)
    (u : ZMod ell) :
    neighborIncidenceCount twistSample (left ∪ right) u =
      neighborIncidenceCount twistSample left u +
        neighborIncidenceCount twistSample right u := by
  simp only [neighborIncidenceCount, Finset.mem_union]
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro τ
  have hout :
      ¬(outNeighbor twistSample τ u ∈ left ∧
        outNeighbor twistSample τ u ∈ right) := by
    exact fun h =>
      (Finset.disjoint_left.mp hdisjoint) h.1 h.2
  have hin :
      ¬(inNeighbor twistSample τ u ∈ left ∧
        inNeighbor twistSample τ u ∈ right) := by
    exact fun h =>
      (Finset.disjoint_left.mp hdisjoint) h.1 h.2
  by_cases hol : outNeighbor twistSample τ u ∈ left <;>
    by_cases hor : outNeighbor twistSample τ u ∈ right <;>
    by_cases hil : inNeighbor twistSample τ u ∈ left <;>
    by_cases hir : inNeighbor twistSample τ u ∈ right <;>
    simp_all

/-- Edge count is monotone in its source set. -/
theorem neighborEdgeCount_mono_source
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (source₁ source₂ target : Finset (ZMod ell))
    (hsubset : source₁ ⊆ source₂) :
    neighborEdgeCount twistSample source₁ target ≤
      neighborEdgeCount twistSample source₂ target := by
  exact Finset.sum_le_sum_of_subset hsubset

/--
At an unusable nonheavy layer, at least `.9` of the `2 * typeCount`
incidences enter the heavy set.
-/
theorem nine_typeCount_le_five_heavyIncidences_of_badNonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell)
    (hu : u ∈ badNonheavyLayerSet Delta twistSample w) :
    9 * typeCount ≤
      5 *
        neighborIncidenceCount twistSample
          (heavyLayerSet Delta w) u := by
  have hu' := (mem_badNonheavyLayerSet_iff
    Delta twistSample w u).mp hu
  have hnotUsable :
      ¬ typeCount ≤
        5 *
          neighborIncidenceCount twistSample
            (nonheavyLayerSet Delta w) u := by
    intro h
    exact hu'.2 ((mem_usableNonheavyLayerSet_iff
      Delta twistSample w u).mpr ⟨hu'.1, h⟩)
  have hpartition :=
    neighborIncidenceCount_union twistSample
      (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
      (disjoint_nonheavyLayerSet_heavyLayerSet Delta w) u
  rw [nonheavyLayerSet_union_heavyLayerSet,
    neighborIncidenceCount_univ] at hpartition
  omega

/-- Summed `.9` heavy-neighbor bound over all unusable nonheavy layers. -/
theorem nine_typeCount_mul_badNonheavy_card_le_five_edges
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    9 * typeCount *
        (badNonheavyLayerSet Delta twistSample w).card ≤
      5 *
        neighborEdgeCount twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (heavyLayerSet Delta w) := by
  calc
    9 * typeCount *
        (badNonheavyLayerSet Delta twistSample w).card =
        ∑ _u ∈ badNonheavyLayerSet Delta twistSample w,
          9 * typeCount := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      ring
    _ ≤ ∑ u ∈ badNonheavyLayerSet Delta twistSample w,
        5 *
          neighborIncidenceCount twistSample
            (heavyLayerSet Delta w) u := by
      apply Finset.sum_le_sum
      intro u hu
      exact
        nine_typeCount_le_five_heavyIncidences_of_badNonheavy
          Delta twistSample w u hu
    _ = 5 *
        neighborEdgeCount twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (heavyLayerSet Delta w) := by
      rw [neighborEdgeCount, Finset.mul_sum]

/--
The upper oriented-edge mixing estimate implies the paper's
`1.25 |H|` unusable-nonheavy bound.
-/
theorem badNonheavy_card_bound_of_upperEdgeMixing
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hUpper :
      10 * ell *
          neighborEdgeCount twistSample
            (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) ≤
        22 * typeCount *
          (nonheavyLayerSet Delta w).card *
          (heavyLayerSet Delta w).card) :
    4 * (badNonheavyLayerSet Delta twistSample w).card ≤
      5 * (heavyLayerSet Delta w).card := by
  let badCount := (badNonheavyLayerSet Delta twistSample w).card
  let heavyCount := (heavyLayerSet Delta w).card
  let nonheavyCount := (nonheavyLayerSet Delta w).card
  let edges :=
    neighborEdgeCount twistSample
      (nonheavyLayerSet Delta w) (heavyLayerSet Delta w)
  have hBadSubset :
      badNonheavyLayerSet Delta twistSample w ⊆
        nonheavyLayerSet Delta w := by
    intro u hu
    exact ((mem_badNonheavyLayerSet_iff
      Delta twistSample w u).mp hu).1
  have hBadEdges :
      9 * typeCount * badCount ≤ 5 * edges := by
    calc
      _ ≤ 5 *
          neighborEdgeCount twistSample
            (badNonheavyLayerSet Delta twistSample w)
            (heavyLayerSet Delta w) :=
        nine_typeCount_mul_badNonheavy_card_le_five_edges
          Delta twistSample w
      _ ≤ 5 * edges := Nat.mul_le_mul_left 5
        (neighborEdgeCount_mono_source twistSample
          (badNonheavyLayerSet Delta twistSample w)
          (nonheavyLayerSet Delta w)
          (heavyLayerSet Delta w) hBadSubset)
  have hNonheavyCard : nonheavyCount ≤ ell := by
    calc
      nonheavyCount = (nonheavyLayerSet Delta w).card := rfl
      _ ≤ (Finset.univ : Finset (ZMod ell)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = ell := by simp
  have hCombined :
      (10 * typeCount * ell) * (9 * badCount) ≤
        (10 * typeCount * ell) * (11 * heavyCount) := by
    calc
      (10 * typeCount * ell) * (9 * badCount) =
          10 * ell * (9 * typeCount * badCount) := by ring
      _ ≤ 10 * ell * (5 * edges) :=
        Nat.mul_le_mul_left (10 * ell) hBadEdges
      _ = 5 * (10 * ell * edges) := by ring
      _ ≤ 5 *
          (22 * typeCount * nonheavyCount * heavyCount) :=
        Nat.mul_le_mul_left 5 hUpper
      _ = 110 * typeCount * nonheavyCount * heavyCount := by ring
      _ ≤ 110 * typeCount * ell * heavyCount := by
        exact Nat.mul_le_mul_right heavyCount
          (Nat.mul_le_mul_left (110 * typeCount) hNonheavyCard)
      _ = (10 * typeCount * ell) * (11 * heavyCount) := by ring
  have hNine : 9 * badCount ≤ 11 * heavyCount :=
    Nat.le_of_mul_le_mul_left hCombined
      (Nat.mul_pos
        (Nat.mul_pos (by omega)
          (Nat.pos_of_ne_zero (NeZero.ne typeCount)))
        (Nat.pos_of_ne_zero (NeZero.ne ell)))
  change 4 * badCount ≤ 5 * heavyCount
  omega

/-- Heavy layers that fail the `.98 typeCount` two-sided-light condition. -/
noncomputable def badHeavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) :=
  heavyLayerSet Delta w \ usableHeavyLayerSet Delta twistSample w

@[simp]
theorem mem_badHeavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ badHeavyLayerSet Delta twistSample w ↔
      u ∈ heavyLayerSet Delta w ∧
        u ∉ usableHeavyLayerSet Delta twistSample w := by
  classical
  simp [badHeavyLayerSet]

/-- No target set can receive more than two incidences per type. -/
theorem neighborIncidenceCount_le_two_mul_typeCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (target : Finset (ZMod ell))
    (u : ZMod ell) :
    neighborIncidenceCount twistSample target u ≤ 2 * typeCount := by
  rw [neighborIncidenceCount]
  calc
    _ ≤ ∑ _τ : Fin typeCount, 2 := by
      apply Finset.sum_le_sum
      intro τ hτ
      split <;> split <;> omega
    _ = 2 * typeCount := by simp [Nat.mul_comm]

/--
Light-neighbor incidences are at most one per type, plus one extra precisely
for each two-sided-light type.
-/
theorem lightIncidences_le_typeCount_add_twoSidedLight_card
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    neighborIncidenceCount twistSample (lightLayerSet Delta w) u ≤
      typeCount +
        (twoSidedLightTypeSet Delta twistSample w u).card := by
  have hcard :
      (twoSidedLightTypeSet Delta twistSample w u).card =
        ∑ τ : Fin typeCount,
          if outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
              inNeighbor twistSample τ u ∈ lightLayerSet Delta w
            then 1 else 0 := by
    classical
    rw [twoSidedLightTypeSet, Finset.card_filter]
  rw [neighborIncidenceCount, hcard]
  calc
    _ ≤ ∑ τ : Fin typeCount,
        (1 +
          if outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
              inNeighbor twistSample τ u ∈ lightLayerSet Delta w
            then 1 else 0) := by
      apply Finset.sum_le_sum
      intro τ hτ
      by_cases hout :
          outNeighbor twistSample τ u ∈ lightLayerSet Delta w <;>
        by_cases hin :
          inNeighbor twistSample τ u ∈ lightLayerSet Delta w <;>
        simp only [hout, hin, if_true, if_false, true_and, false_and,
          and_false] <;> omega
    _ = typeCount +
        ∑ τ : Fin typeCount,
          if outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
              inNeighbor twistSample τ u ∈ lightLayerSet Delta w
            then 1 else 0 := by
      rw [Finset.sum_add_distrib]
      simp

/--
An unusable heavy layer has strictly less than `.99` of its `2 * typeCount`
incidences entering the light set.
-/
theorem badHeavy_lightIncidences_strict
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell)
    (hu : u ∈ badHeavyLayerSet Delta twistSample w) :
    100 *
        neighborIncidenceCount twistSample (lightLayerSet Delta w) u <
      198 * typeCount := by
  have hu' := (mem_badHeavyLayerSet_iff
    Delta twistSample w u).mp hu
  have htypes :
      ¬ 98 * typeCount ≤
        100 * (twoSidedLightTypeSet Delta twistSample w u).card := by
    intro h
    exact hu'.2 ((mem_usableHeavyLayerSet_iff
      Delta twistSample w u).mpr ⟨hu'.1, h⟩)
  have hinc :=
    lightIncidences_le_typeCount_add_twoSidedLight_card
      Delta twistSample w u
  omega

/-- Summed strict light-incidence bound over unusable heavy layers. -/
theorem badHeavy_lightEdges_bound
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    100 *
        neighborEdgeCount twistSample
          (badHeavyLayerSet Delta twistSample w)
          (lightLayerSet Delta w) +
        (badHeavyLayerSet Delta twistSample w).card ≤
      198 * typeCount *
        (badHeavyLayerSet Delta twistSample w).card := by
  let bad := badHeavyLayerSet Delta twistSample w
  calc
    100 *
          neighborEdgeCount twistSample bad (lightLayerSet Delta w) +
        bad.card =
        (∑ u ∈ bad,
          100 *
            neighborIncidenceCount twistSample
              (lightLayerSet Delta w) u) +
          ∑ _u ∈ bad, 1 := by
      rw [neighborEdgeCount, Finset.mul_sum]
      simp
    _ = ∑ u ∈ bad,
        (100 *
            neighborIncidenceCount twistSample
              (lightLayerSet Delta w) u + 1) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ _u ∈ bad, 198 * typeCount := by
      apply Finset.sum_le_sum
      intro u hu
      exact Nat.add_one_le_iff.mpr
        (badHeavy_lightIncidences_strict
          Delta twistSample w u hu)
    _ = 198 * typeCount * bad.card := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      ring

/-- Summed trivial `2 * typeCount` bound over usable heavy layers. -/
theorem usableHeavy_lightEdges_bound
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    100 *
        neighborEdgeCount twistSample
          (usableHeavyLayerSet Delta twistSample w)
          (lightLayerSet Delta w) ≤
      200 * typeCount *
        (usableHeavyLayerSet Delta twistSample w).card := by
  let good := usableHeavyLayerSet Delta twistSample w
  calc
    100 *
        neighborEdgeCount twistSample good (lightLayerSet Delta w) =
        ∑ u ∈ good,
          100 *
            neighborIncidenceCount twistSample
              (lightLayerSet Delta w) u := by
      rw [neighborEdgeCount, Finset.mul_sum]
    _ ≤ ∑ _u ∈ good, 100 * (2 * typeCount) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Nat.mul_le_mul_left 100
        (neighborIncidenceCount_le_two_mul_typeCount
          twistSample (lightLayerSet Delta w) u)
    _ = 200 * typeCount * good.card := by
      rw [Finset.sum_const_nat (fun _ _ => rfl)]
      ring

/--
The lower `.999` oriented-edge estimate implies that at least `.9 |H|`
heavy layers satisfy the two-sided `.98 typeCount` condition.
-/
theorem usableHeavy_card_bound_of_lowerEdgeMixing
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLower :
      1998 * typeCount * (heavyLayerSet Delta w).card ≤
        1000 *
          neighborEdgeCount twistSample
            (heavyLayerSet Delta w) (lightLayerSet Delta w)) :
    9 * (heavyLayerSet Delta w).card ≤
      10 * (usableHeavyLayerSet Delta twistSample w).card := by
  let good : Finset (ZMod ell) :=
    usableHeavyLayerSet Delta twistSample w
  let bad : Finset (ZMod ell) :=
    badHeavyLayerSet Delta twistSample w
  let heavy : Finset (ZMod ell) := heavyLayerSet Delta w
  let light : Finset (ZMod ell) := lightLayerSet Delta w
  let goodCount : Nat := good.card
  let badCount : Nat := bad.card
  let heavyCount : Nat := heavy.card
  let goodEdges : Nat := neighborEdgeCount twistSample good light
  let badEdges : Nat := neighborEdgeCount twistSample bad light
  let heavyEdges : Nat := neighborEdgeCount twistSample heavy light
  have hGoodSubset : good ⊆ heavy := by
    intro u hu
    exact ((mem_usableHeavyLayerSet_iff
      Delta twistSample w u).mp hu).1
  have hDisjoint : Disjoint good bad := by
    refine Finset.disjoint_left.mpr ?_
    intro u hgood hbad
    exact ((mem_badHeavyLayerSet_iff
      Delta twistSample w u).mp hbad).2 hgood
  have hUnion : good ∪ bad = heavy :=
    Finset.union_sdiff_of_subset hGoodSubset
  have hCard : goodCount + badCount = heavyCount := by
    dsimp only [goodCount, badCount, heavyCount]
    rw [← Finset.card_union_of_disjoint hDisjoint, hUnion]
  have hEdges : goodEdges + badEdges = heavyEdges := by
    dsimp only [goodEdges, badEdges, heavyEdges]
    rw [← hUnion, neighborEdgeCount]
    exact (Finset.sum_union hDisjoint).symm
  have hGoodUpper :
      100 * goodEdges ≤ 200 * typeCount * goodCount := by
    exact usableHeavy_lightEdges_bound Delta twistSample w
  have hBadUpper :
      100 * badEdges + badCount ≤
        198 * typeCount * badCount := by
    exact badHeavy_lightEdges_bound Delta twistSample w
  have hEdgeUpper :
      1000 * heavyEdges + 10 * badCount ≤
        2000 * typeCount * goodCount +
          1980 * typeCount * badCount := by
    calc
      1000 * heavyEdges + 10 * badCount =
          10 *
            ((100 * goodEdges) +
              (100 * badEdges + badCount)) := by
        rw [← hEdges]
        ring
      _ ≤ 10 *
          ((200 * typeCount * goodCount) +
            (198 * typeCount * badCount)) :=
        Nat.mul_le_mul_left 10 (Nat.add_le_add hGoodUpper hBadUpper)
      _ = 2000 * typeCount * goodCount +
          1980 * typeCount * badCount := by ring
  let goodMass := typeCount * goodCount
  let badMass := typeCount * badCount
  let heavyMass := typeCount * heavyCount
  have hMassCard : heavyMass = goodMass + badMass := by
    dsimp only [heavyMass, goodMass, badMass]
    rw [← hCard, Nat.mul_add]
  have hLowerLet :
      1998 * heavyMass ≤ 1000 * heavyEdges := by
    calc
      1998 * heavyMass =
          1998 * typeCount * heavyCount := by
        dsimp only [heavyMass]
        ring
      _ ≤ 1000 * heavyEdges := hLower
  have hEdgeUpperMass :
      1000 * heavyEdges + 10 * badCount ≤
        2000 * goodMass + 1980 * badMass := by
    calc
      _ ≤ 2000 * typeCount * goodCount +
          1980 * typeCount * badCount := hEdgeUpper
      _ = 2000 * goodMass + 1980 * badMass := by
        dsimp only [goodMass, badMass]
        ring
  have hCompareMass :
      1998 * heavyMass + 10 * badCount ≤
        2000 * goodMass + 1980 * badMass := by
    exact
      (Nat.add_le_add_right hLowerLet (10 * badCount)).trans
        hEdgeUpperMass
  have hMass : 18 * badMass ≤ 2 * goodMass := by
    rw [hMassCard] at hCompareMass
    rw [Nat.mul_add] at hCompareMass
    omega
  have hCore :
      (2 * typeCount) * (9 * badCount) ≤
        (2 * typeCount) * goodCount := by
    convert hMass using 1 <;> dsimp [goodMass, badMass] <;> ring
  have hNineBad : 9 * badCount ≤ goodCount :=
    Nat.le_of_mul_le_mul_left hCore
      (Nat.mul_pos (by omega)
        (Nat.pos_of_ne_zero (NeZero.ne typeCount)))
  change 9 * heavyCount ≤ 10 * goodCount
  omega

/-- The two edge-mixing estimates imply the word-indexed layer event. -/
theorem hasHHO20LayerMixing_of_edgeMixing
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hEdge : HasHHO20EdgeMixing Delta twistSample) :
    HasHHO20LayerMixing Delta twistSample := by
  intro w hsmall
  have hcards := layer_cardinality_bounds_of_small Delta w hsmall
  have hmixed := hEdge w hcards.1 hcards.2
  refine ⟨
    badNonheavy_card_bound_of_upperEdgeMixing
      Delta twistSample w hmixed.1, ?_⟩
  intro hcase
  exact usableHeavy_card_bound_of_lowerEdgeMixing
    Delta twistSample w (hmixed.2 hcase)

end QEC.Coding.FiberBundle.TwistGraph

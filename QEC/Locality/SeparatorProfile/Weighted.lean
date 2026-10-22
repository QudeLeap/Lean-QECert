import QEC.Locality.ConnectivityTradeoff.RecursiveSeparator
import QEC.Locality.SeparatorProfile.Quantitative
/-!
# Boundary-marked separator spines

The ordinary measured separator is cardinality-balanced.  To rebalance a
carried boundary, this module follows only the unique child containing more
than two thirds of a marked set.  The siblings exposed by the spine are already
marked-balanced, and the exact separator charge is geometric because the
spine's carrier cardinality still drops by the ordinary two-thirds bound.

This is the weighted-separator ingredient for the quantitative `r`-division
construction.  It deliberately records the charged spine rather than assuming
a weighted separator oracle.
-/

namespace QEC.Locality

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A marked subset cannot be heavy in both disjoint sides of one split. -/
private theorem not_both_marked_heavy
    (marked left right : Finset ι) (hdisjoint : Disjoint left right) :
    ¬ (2 * marked.card < 3 * (marked ∩ left).card ∧
      2 * marked.card < 3 * (marked ∩ right).card) := by
  intro hheavy
  have hleft : marked ∩ left ⊆ marked := Finset.inter_subset_left
  have hright : marked ∩ right ⊆ marked := Finset.inter_subset_left
  have hmarkDisjoint : Disjoint (marked ∩ left) (marked ∩ right) := by
    apply Finset.disjoint_left.mpr
    intro x hxleft hxright
    exact (Finset.disjoint_left.mp hdisjoint)
      (Finset.mem_inter.mp hxleft).2 (Finset.mem_inter.mp hxright).2
  have hsum : (marked ∩ left).card + (marked ∩ right).card ≤ marked.card := by
    rw [← Finset.card_union_of_disjoint hmarkDisjoint]
    exact Finset.card_le_card (Finset.union_subset hleft hright)
  omega

/-- The sibling of a marked-heavy side is marked-light. -/
private theorem marked_right_light_of_left_heavy
    (marked left right : Finset ι) (hdisjoint : Disjoint left right)
    (hleftHeavy : 2 * marked.card < 3 * (marked ∩ left).card) :
    3 * (marked ∩ right).card ≤ 2 * marked.card := by
  by_contra hrightLight
  have hrightHeavy : 2 * marked.card < 3 * (marked ∩ right).card := by omega
  exact not_both_marked_heavy marked left right hdisjoint ⟨hleftHeavy, hrightHeavy⟩

/-- The sibling of a marked-heavy side is marked-light. -/
private theorem marked_left_light_of_right_heavy
    (marked left right : Finset ι) (hdisjoint : Disjoint left right)
    (hrightHeavy : 2 * marked.card < 3 * (marked ∩ right).card) :
    3 * (marked ∩ left).card ≤ 2 * marked.card := by
  by_contra hleftLight
  have hleftHeavy : 2 * marked.card < 3 * (marked ∩ left).card := by omega
  exact not_both_marked_heavy marked left right hdisjoint ⟨hleftHeavy, hrightHeavy⟩

/-- A finite chain of exact measured splits following a marked-heavy child. -/
inductive MarkedSeparatorSpine (G : ConnectivityGraph ι) (marked : Finset ι) :
    Finset ι → Type u
  | stop {vertices left separator right : Finset ι}
      (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hleftLight : 3 * (marked ∩ left).card ≤ 2 * marked.card)
      (hrightLight : 3 * (marked ∩ right).card ≤ 2 * marked.card) :
      MarkedSeparatorSpine G marked vertices
  | followLeft {vertices left separator right : Finset ι}
      (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hleftHeavy : 2 * marked.card < 3 * (marked ∩ left).card)
      (subtree : MarkedSeparatorSpine G marked left) :
      MarkedSeparatorSpine G marked vertices
  | followRight {vertices left separator right : Finset ι}
      (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hrightHeavy : 2 * marked.card < 3 * (marked ∩ right).card)
      (subtree : MarkedSeparatorSpine G marked right) :
      MarkedSeparatorSpine G marked vertices

/-- The exact separators paid along a marked-heavy spine. -/
noncomputable def MarkedSeparatorSpine.separators
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → List (Finset ι)
  | @stop _ _ _ _ _ vertices left separator right hpartition hminimum hleftLight hrightLight =>
      [separator]
  | @followLeft _ _ _ _ _ vertices left separator right hpartition hminimum hleftHeavy subtree =>
      separator :: subtree.separators
  | @followRight _ _ _ _ _ vertices left separator right hpartition hminimum hrightHeavy subtree =>
      separator :: subtree.separators

/-- The final pair of exposed marked-light sides. -/
noncomputable def MarkedSeparatorSpine.stopSides
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → Finset ι × Finset ι
  | @stop _ _ _ _ _ vertices left separator right hpartition hminimum hleftLight hrightLight =>
      (left, right)
  | @followLeft _ _ _ _ _ vertices left separator right hpartition hminimum hleftHeavy subtree =>
      subtree.stopSides
  | @followRight _ _ _ _ _ vertices left separator right hpartition hminimum hrightHeavy subtree =>
      subtree.stopSides

/-- The light siblings exposed while following the unique marked-heavy side. -/
noncomputable def MarkedSeparatorSpine.exposedSide
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → Finset ι
  | .stop _ _ _ _ => ∅
  | @followLeft _ _ _ _ _ vertices left separator right hpartition hminimum hleftHeavy subtree =>
      right ∪ subtree.exposedSide
  | @followRight _ _ _ _ _ vertices left separator right hpartition hminimum hrightHeavy subtree =>
      left ∪ subtree.exposedSide

/-- The final carrier on which the marked-heavy walk stops. -/
noncomputable def MarkedSeparatorSpine.terminalCarrier
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → Finset ι
  | .stop _ _ _ _ => vertices
  | .followLeft _ _ _ subtree => subtree.terminalCarrier
  | .followRight _ _ _ subtree => subtree.terminalCarrier

@[simp] theorem MarkedSeparatorSpine.exposedSide_stop
    {G : ConnectivityGraph ι} {marked vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
    (hminimum : separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
    (hleftLight : 3 * (marked ∩ left).card ≤ 2 * marked.card)
    (hrightLight : 3 * (marked ∩ right).card ≤ 2 * marked.card) :
    (MarkedSeparatorSpine.stop hpartition hminimum hleftLight hrightLight).exposedSide = ∅ := rfl

private theorem markedSpine_split_cover
    {G : ConnectivityGraph ι} {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    separator ∪ (left ∪ right) = vertices := by
  rw [hpartition.2.1]
  exact Finset.union_sdiff_of_subset hpartition.1

private theorem markedSpine_left_subset
    {G : ConnectivityGraph ι} {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    left ⊆ vertices := by
  intro x hx
  exact (Finset.mem_sdiff.mp (by rw [← hpartition.2.1]; exact Finset.mem_union_left _ hx)).1

private theorem markedSpine_right_subset
    {G : ConnectivityGraph ι} {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right) :
    right ⊆ vertices := by
  intro x hx
  exact (Finset.mem_sdiff.mp (by rw [← hpartition.2.1]; exact Finset.mem_union_right _ hx)).1

theorem MarkedSeparatorSpine.terminalCarrier_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.terminalCarrier ⊆ vertices := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight => exact Finset.Subset.rfl
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      exact ih.trans (markedSpine_left_subset hpartition)
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      exact ih.trans (markedSpine_right_subset hpartition)

theorem MarkedSeparatorSpine.exposedSide_subset
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.exposedSide ⊆ vertices := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight => simp [exposedSide]
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      exact Finset.union_subset (markedSpine_right_subset hpartition)
        (ih.trans (markedSpine_left_subset hpartition))
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      exact Finset.union_subset (markedSpine_left_subset hpartition)
        (ih.trans (markedSpine_right_subset hpartition))

/-- Exposed siblings never meet the final marked-heavy carrier. -/
private theorem MarkedSeparatorSpine.exposedSide_disjoint_terminalCarrier
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    Disjoint spine.exposedSide spine.terminalCarrier := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      simpa [exposedSide, terminalCarrier] using
        (Finset.disjoint_empty_left vertices)
  | @followLeft vertices left separator right hpartition hminimum hleftHeavy subtree ih =>
      apply Finset.disjoint_left.mpr
      intro x hxexposed hxterminal
      rcases Finset.mem_union.mp hxexposed with hxright | hxsub
      · have hxleft := subtree.terminalCarrier_subset hxterminal
        exact (Finset.disjoint_left.mp hpartition.2.2.1) hxleft hxright
      · exact (Finset.disjoint_left.mp ih) hxsub hxterminal
  | @followRight vertices left separator right hpartition hminimum hrightHeavy subtree ih =>
      apply Finset.disjoint_left.mpr
      intro x hxexposed hxterminal
      rcases Finset.mem_union.mp hxexposed with hxleft | hxsub
      · have hxright := subtree.terminalCarrier_subset hxterminal
        exact (Finset.disjoint_left.mp hpartition.2.2.1) hxleft hxright
      · exact (Finset.disjoint_left.mp ih) hxsub hxterminal

/-- The terminal carrier is the root or retains more than two thirds of the marks. -/
private theorem MarkedSeparatorSpine.terminalCarrier_eq_or_marked_heavy
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.terminalCarrier = vertices ∨
      2 * marked.card < 3 * (marked ∩ spine.terminalCarrier).card := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      exact Or.inl rfl
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      rcases ih with hterminal | hterminal
      · exact Or.inr (by simpa [terminalCarrier, hterminal] using hleftHeavy)
      · exact Or.inr (by simpa [terminalCarrier] using hterminal)
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      rcases ih with hterminal | hterminal
      · exact Or.inr (by simpa [terminalCarrier, hterminal] using hrightHeavy)
      · exact Or.inr (by simpa [terminalCarrier] using hterminal)

/-- The aggregate exposed side is marked-light (in fact, below one third). -/
theorem MarkedSeparatorSpine.exposedSide_marked_light
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    3 * (marked ∩ spine.exposedSide).card ≤ 2 * marked.card := by
  rcases spine.terminalCarrier_eq_or_marked_heavy with hterminal | hheavy
  · have hempty : spine.exposedSide = ∅ := by
      by_contra hne
      have hnonempty : spine.exposedSide.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases hnonempty with ⟨x, hx⟩
      exact (Finset.disjoint_left.mp spine.exposedSide_disjoint_terminalCarrier)
        hx (by rw [hterminal]; exact spine.exposedSide_subset hx)
    simp [hempty]
  · have hdisjoint : Disjoint (marked ∩ spine.exposedSide)
        (marked ∩ spine.terminalCarrier) := by
      exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
        spine.exposedSide_disjoint_terminalCarrier
    have hunion : (marked ∩ spine.exposedSide).card +
        (marked ∩ spine.terminalCarrier).card ≤ marked.card := by
      rw [← Finset.card_union_of_disjoint hdisjoint]
      exact Finset.card_le_card (Finset.union_subset
        Finset.inter_subset_left Finset.inter_subset_left)
    omega

theorem MarkedSeparatorSpine.stopSides_subset_terminalCarrier
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.stopSides.1 ⊆ spine.terminalCarrier ∧
      spine.stopSides.2 ⊆ spine.terminalCarrier := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      exact ⟨markedSpine_left_subset hpartition, markedSpine_right_subset hpartition⟩
  | followLeft hpartition hminimum hleftHeavy subtree ih => simpa [stopSides, terminalCarrier]
  | followRight hpartition hminimum hrightHeavy subtree ih => simpa [stopSides, terminalCarrier]

theorem MarkedSeparatorSpine.stopSides_disjoint
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    Disjoint spine.stopSides.1 spine.stopSides.2 := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      simpa [stopSides] using hpartition.2.2.1
  | followLeft hpartition hminimum hleftHeavy subtree ih => simpa [stopSides]
  | followRight hpartition hminimum hrightHeavy subtree ih => simpa [stopSides]

theorem MarkedSeparatorSpine.exposedSide_disjoint_stopSides
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    Disjoint spine.exposedSide spine.stopSides.1 ∧
      Disjoint spine.exposedSide spine.stopSides.2 := by
  have hterminal := spine.exposedSide_disjoint_terminalCarrier
  have hsides := spine.stopSides_subset_terminalCarrier
  exact ⟨Disjoint.mono_right hsides.1 hterminal,
    Disjoint.mono_right hsides.2 hterminal⟩

private theorem noEdgeBetween_union_left
    {G : ConnectivityGraph ι} {first second target : Finset ι}
    (hfirst : NoEdgeBetween G first target)
    (hsecond : NoEdgeBetween G second target) :
    NoEdgeBetween G (first ∪ second) target := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hxfirst | hxsecond
  · exact hfirst hxfirst hy
  · exact hsecond hxsecond hy

theorem MarkedSeparatorSpine.threeSides_noEdge
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    NoEdgeBetween G spine.exposedSide spine.stopSides.1 ∧
      NoEdgeBetween G spine.exposedSide spine.stopSides.2 ∧
      NoEdgeBetween G spine.stopSides.1 spine.stopSides.2 := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      refine ⟨?_, ?_, ?_⟩
      · simp [exposedSide, NoEdgeBetween]
      · simp [exposedSide, NoEdgeBetween]
      · simpa [stopSides] using hpartition.2.2.2.2.2
  | @followLeft vertices left separator right hpartition hminimum hleftHeavy subtree ih =>
      have hsides := subtree.stopSides_subset_terminalCarrier
      have hstopLeft : subtree.stopSides.1 ⊆ left :=
        hsides.1.trans subtree.terminalCarrier_subset
      have hstopRight : subtree.stopSides.2 ⊆ left :=
        hsides.2.trans subtree.terminalCarrier_subset
      have hcross := hpartition.2.2.2.2.2
      refine ⟨?_, ?_, ih.2.2⟩
      · exact noEdgeBetween_union_left
          (hcross.symm.mono Finset.Subset.rfl hstopLeft) ih.1
      · exact noEdgeBetween_union_left
          (hcross.symm.mono Finset.Subset.rfl hstopRight) ih.2.1
  | @followRight vertices left separator right hpartition hminimum hrightHeavy subtree ih =>
      have hsides := subtree.stopSides_subset_terminalCarrier
      have hstopLeft : subtree.stopSides.1 ⊆ right :=
        hsides.1.trans subtree.terminalCarrier_subset
      have hstopRight : subtree.stopSides.2 ⊆ right :=
        hsides.2.trans subtree.terminalCarrier_subset
      have hcross := hpartition.2.2.2.2.2
      refine ⟨?_, ?_, ih.2.2⟩
      · exact noEdgeBetween_union_left
          (hcross.mono Finset.Subset.rfl hstopLeft) ih.1
      · exact noEdgeBetween_union_left
          (hcross.mono Finset.Subset.rfl hstopRight) ih.2.1

/-- The finite separator charge of a marked-heavy spine. -/
private noncomputable def markedSpineSeparatorCardSum
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) : Nat :=
  (spine.separators.map Finset.card).sum

/-- The set of vertices charged by a marked-heavy spine. -/
noncomputable def markedSpineSeparatorUnion
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) : Finset ι :=
  spine.separators.foldr (· ∪ ·) ∅

/--
The exposed side, the two terminal sides, and the accumulated separators cover
the original spine carrier exactly.
-/
theorem MarkedSeparatorSpine.exposed_stopSides_separatorUnion
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    spine.exposedSide ∪ spine.stopSides.1 ∪ spine.stopSides.2 ∪
      markedSpineSeparatorUnion spine = vertices := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      simpa [exposedSide, stopSides, markedSpineSeparatorUnion, separators,
        Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using
        markedSpine_split_cover hpartition
  | @followLeft vertices left separator right hpartition hminimum hleftHeavy subtree ih =>
      have hcover := markedSpine_split_cover hpartition
      simp only [exposedSide, stopSides, markedSpineSeparatorUnion, separators,
        List.foldr_cons, List.foldr_nil]
      calc
        (right ∪ subtree.exposedSide) ∪ subtree.stopSides.1 ∪
              subtree.stopSides.2 ∪
            (separator ∪ markedSpineSeparatorUnion subtree) =
            separator ∪
              ((subtree.exposedSide ∪ subtree.stopSides.1 ∪
                subtree.stopSides.2 ∪ markedSpineSeparatorUnion subtree) ∪ right) := by
          ac_rfl
        _ = separator ∪ (left ∪ right) := by rw [ih]
        _ = vertices := hcover
  | @followRight vertices left separator right hpartition hminimum hrightHeavy subtree ih =>
      have hcover := markedSpine_split_cover hpartition
      simp only [exposedSide, stopSides, markedSpineSeparatorUnion, separators,
        List.foldr_cons, List.foldr_nil]
      calc
        (left ∪ subtree.exposedSide) ∪ subtree.stopSides.1 ∪
              subtree.stopSides.2 ∪
            (separator ∪ markedSpineSeparatorUnion subtree) =
            separator ∪
              (left ∪ (subtree.exposedSide ∪ subtree.stopSides.1 ∪
                subtree.stopSides.2 ∪ markedSpineSeparatorUnion subtree)) := by
          ac_rfl
        _ = separator ∪ (left ∪ right) := by rw [ih]
        _ = vertices := hcover

private theorem separatorUnion_card_le_cardSum (separators : List (Finset ι)) :
    (separators.foldr (· ∪ ·) ∅).card ≤ (separators.map Finset.card).sum := by
  induction separators with
  | nil => simp
  | cons separator separators ih =>
      simpa only [List.foldr_cons, List.map_cons, List.sum_cons] using
        (Finset.card_union_le separator (separators.foldr (· ∪ ·) ∅)).trans
          (Nat.add_le_add_left ih separator.card)

private theorem markedSpineSeparatorUnion_card_le_sum
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    (markedSpineSeparatorUnion spine).card ≤ markedSpineSeparatorCardSum spine := by
  exact separatorUnion_card_le_cardSum spine.separators

/-- The geometric decay caused by the fixed two-thirds cardinality balance. -/
noncomputable def markedSpineDecayRatio (exponent : ℝ) : ℝ :=
  Real.rpow (2 / 3 : ℝ) exponent

private theorem markedSpineDecayRatio_nonneg (exponent : ℝ) :
    0 ≤ markedSpineDecayRatio exponent := by
  exact Real.rpow_nonneg (by norm_num) _

theorem markedSpineDecayRatio_lt_one {exponent : ℝ} (hexponent : 0 < exponent) :
    markedSpineDecayRatio exponent < 1 := by
  rw [markedSpineDecayRatio, ← Real.one_rpow exponent]
  exact Real.rpow_lt_rpow (by norm_num) (by norm_num) hexponent

private theorem split_side_rpow_le_markedSpineDecay
    {vertices side : Finset ι} {exponent : ℝ}
    (hbalance : 3 * side.card ≤ 2 * vertices.card) (hexponent : 0 ≤ exponent) :
    Real.rpow side.card exponent ≤
      markedSpineDecayRatio exponent * Real.rpow vertices.card exponent := by
  have hcard : (side.card : ℝ) ≤ (2 / 3 : ℝ) * vertices.card := by
    have hcast : (3 : ℝ) * side.card ≤ 2 * vertices.card := by
      exact_mod_cast hbalance
    linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hcard hexponent
  simpa [markedSpineDecayRatio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (Nat.cast_nonneg vertices.card)] using hpow

private theorem markedSpine_separator_add_childPotential_le
    {vertices child separator : Finset ι} {beta exponent : ℝ}
    (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    (hseparator : (separator.card : ℝ) ≤ beta * Real.rpow vertices.card exponent)
    (hchild : Real.rpow child.card exponent ≤
      markedSpineDecayRatio exponent * Real.rpow vertices.card exponent) :
    (separator.card : ℝ) + beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow child.card exponent ≤
      beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow vertices.card exponent := by
  have hratio := markedSpineDecayRatio_lt_one hexponent
  have hden : 0 < 1 - markedSpineDecayRatio exponent := sub_pos.mpr hratio
  have hpotential : 0 ≤ beta / (1 - markedSpineDecayRatio exponent) :=
    div_nonneg (zero_le_one.trans hbeta) hden.le
  have hscaled := mul_le_mul_of_nonneg_left hchild hpotential
  have hid : beta + beta / (1 - markedSpineDecayRatio exponent) *
      markedSpineDecayRatio exponent = beta / (1 - markedSpineDecayRatio exponent) := by
    field_simp
    ring
  calc
    (separator.card : ℝ) + beta / (1 - markedSpineDecayRatio exponent) *
          Real.rpow child.card exponent
        ≤ beta * Real.rpow vertices.card exponent +
            beta / (1 - markedSpineDecayRatio exponent) *
              Real.rpow child.card exponent :=
      add_le_add hseparator le_rfl
    _ ≤ beta * Real.rpow vertices.card exponent +
          beta / (1 - markedSpineDecayRatio exponent) *
            (markedSpineDecayRatio exponent * Real.rpow vertices.card exponent) :=
      by simpa only [add_comm] using
        (add_le_add_left hscaled (beta * Real.rpow vertices.card exponent))
    _ = (beta + beta / (1 - markedSpineDecayRatio exponent) *
          markedSpineDecayRatio exponent) * Real.rpow vertices.card exponent := by ring
    _ = beta / (1 - markedSpineDecayRatio exponent) *
          Real.rpow vertices.card exponent := by rw [hid]

/--
The exact separator mass of the marked-heavy spine is bounded by a
graph-uniform geometric potential.  This is the charging lemma used when a
boundary-heavy region is refined before the final `r`-region aggregation.
-/
private theorem MarkedSeparatorSpine.separatorCardSum_le_profilePotential
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ} (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) :
    (markedSpineSeparatorCardSum spine : ℝ) ≤
      beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow vertices.card exponent := by
  have hbeta : 1 ≤ beta := hProfile.1
  have hexponent : 0 < exponent := hProfile.2.1
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      rename_i vertices left separator right
      simp only [markedSpineSeparatorCardSum, separators, List.map_cons, List.sum_cons,
        List.map_nil, List.sum_nil, Nat.cast_ofNat, Nat.cast_add]
      have hseparator := minimumSeparator_card_real_le_profilePower
        G beta exponent hProfile vertices separator hvertices hminimum
      have hratio := markedSpineDecayRatio_lt_one hexponent
      have hden : 0 < 1 - markedSpineDecayRatio exponent := sub_pos.mpr hratio
      have hcoefficient : beta ≤ beta / (1 - markedSpineDecayRatio exponent) := by
        apply (le_div_iff₀ hden).2
        have hratioNonneg := markedSpineDecayRatio_nonneg exponent
        nlinarith
      simpa using hseparator.trans
        (mul_le_mul_of_nonneg_right hcoefficient
          (Real.rpow_nonneg (Nat.cast_nonneg vertices.card) _))
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      rename_i vertices left separator right
      have hleftPositive : 0 < left.card := by
        have : 0 < (marked ∩ left).card := by omega
        exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
      have hleftCard : 1 ≤ left.card := by omega
      have hseparator := minimumSeparator_card_real_le_profilePower
        G beta exponent hProfile vertices separator hvertices hminimum
      have hchild := split_side_rpow_le_markedSpineDecay hpartition.2.2.2.1 hexponent.le
      have hstep := markedSpine_separator_add_childPotential_le hbeta hexponent hseparator hchild
      simp only [markedSpineSeparatorCardSum, separators, List.map_cons, List.sum_cons,
        Nat.cast_add] at ih ⊢
      linarith [ih hleftCard]
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      rename_i vertices left separator right
      have hrightPositive : 0 < right.card := by
        have : 0 < (marked ∩ right).card := by omega
        exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
      have hrightCard : 1 ≤ right.card := by omega
      have hseparator := minimumSeparator_card_real_le_profilePower
        G beta exponent hProfile vertices separator hvertices hminimum
      have hchild := split_side_rpow_le_markedSpineDecay hpartition.2.2.2.2.1 hexponent.le
      have hstep := markedSpine_separator_add_childPotential_le hbeta hexponent hseparator hchild
      simp only [markedSpineSeparatorCardSum, separators, List.map_cons, List.sum_cons,
        Nat.cast_add] at ih ⊢
      linarith [ih hrightCard]

private theorem MarkedSeparatorSpine.separatorUnion_card_le_profilePotential
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ} (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) :
    ((markedSpineSeparatorUnion spine).card : ℝ) ≤
      beta / (1 - markedSpineDecayRatio exponent) *
        Real.rpow vertices.card exponent := by
  exact (Nat.cast_le.2 (markedSpineSeparatorUnion_card_le_sum spine)).trans
    (spine.separatorCardSum_le_profilePotential hProfile hvertices)

/-- Graph-uniform ceiling for one weighted-spine separator at scale `r`. -/
noncomputable def weightedSpineSeparatorBudget
    (beta exponent : ℝ) (r : Nat) : Nat :=
  Nat.ceil (beta / (1 - markedSpineDecayRatio exponent) * Real.rpow r exponent)

theorem weightedSpineSeparatorBudget_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {r : Nat} (hr : 1 ≤ r) :
    0 < weightedSpineSeparatorBudget beta exponent r := by
  rw [weightedSpineSeparatorBudget, Nat.ceil_pos]
  have hdenominator : 0 < 1 - markedSpineDecayRatio exponent :=
    sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent)
  exact mul_pos (div_pos (zero_lt_one.trans_le hbeta) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hr) exponent)

theorem MarkedSeparatorSpine.separatorUnion_card_le_weightedSpineSeparatorBudget
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices)
    {beta exponent : ℝ}
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hvertices : 1 ≤ vertices.card) {r : Nat} (hcard : vertices.card ≤ r) :
    (markedSpineSeparatorUnion spine).card ≤
      weightedSpineSeparatorBudget beta exponent r := by
  have hexponent : 0 ≤ exponent := hProfile.2.1.le
  have hpow : Real.rpow vertices.card exponent ≤ Real.rpow r exponent := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hcard) hexponent
  have hcoefficient : 0 ≤ beta / (1 - markedSpineDecayRatio exponent) := by
    exact div_nonneg (zero_le_one.trans hProfile.1)
      (sub_nonneg.mpr (markedSpineDecayRatio_lt_one hProfile.2.1).le)
  have hscaled := mul_le_mul_of_nonneg_left hpow hcoefficient
  have hreal := (spine.separatorUnion_card_le_profilePotential hProfile hvertices).trans hscaled
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-- Local boundary cap with slack for the three-way weighted refinement. -/
noncomputable def weightedProfileBoundaryBudget
    (beta exponent : ℝ) (r : Nat) : Nat :=
  6 * weightedSpineSeparatorBudget beta exponent r

theorem MarkedSeparatorSpine.stopSides_marked_light
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) :
    3 * (marked ∩ spine.stopSides.1).card ≤ 2 * marked.card ∧
      3 * (marked ∩ spine.stopSides.2).card ≤ 2 * marked.card := by
  induction spine with
  | stop hpartition hminimum hleftLight hrightLight =>
      simpa [stopSides] using And.intro hleftLight hrightLight
  | followLeft hpartition hminimum hleftHeavy subtree ih =>
      simpa [stopSides] using ih
  | followRight hpartition hminimum hrightHeavy subtree ih =>
      simpa [stopSides] using ih

private theorem measured_left_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (hpositive : 0 < vertices.card) :
    (measuredTwoThirdsLeft G vertices).card < vertices.card := by
  have hnonempty : vertices.Nonempty := Finset.card_pos.mp hpositive
  exact measuredTwoThirdsLeft_card_lt G vertices hnonempty

private theorem measured_right_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (hpositive : 0 < vertices.card) :
    (measuredTwoThirdsRight G vertices).card < vertices.card := by
  have hnonempty : vertices.Nonempty := Finset.card_pos.mp hpositive
  exact measuredTwoThirdsRight_card_lt G vertices hnonempty

/-- Construct the marked-heavy spine by strong descent of its carrier. -/
noncomputable def buildMarkedSeparatorSpine
    (G : ConnectivityGraph ι) (marked vertices : Finset ι) :
    MarkedSeparatorSpine G marked vertices := by
  classical
  let left := measuredTwoThirdsLeft G vertices
  let separator := measuredTwoThirdsSeparator G vertices
  let right := measuredTwoThirdsRight G vertices
  have hpartition :
      TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right :=
    measuredTwoThirdsSplit_spec G vertices
  have hminimum : separator.card =
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices :=
    (measuredTwoThirdsSeparator_spec G vertices).2.2
  by_cases hleftHeavy : 2 * marked.card < 3 * (marked ∩ left).card
  · have hleftPositive : 0 < left.card := by
      have : 0 < (marked ∩ left).card := by omega
      exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
    exact .followLeft hpartition hminimum hleftHeavy
      (buildMarkedSeparatorSpine G marked left)
  · by_cases hrightHeavy : 2 * marked.card < 3 * (marked ∩ right).card
    · have hrightPositive : 0 < right.card := by
        have : 0 < (marked ∩ right).card := by omega
        exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
      exact .followRight hpartition hminimum hrightHeavy
        (buildMarkedSeparatorSpine G marked right)
    · refine .stop hpartition hminimum ?_ ?_
      · omega
      · omega
termination_by vertices.card
decreasing_by
  · apply measured_left_card_lt G vertices
    exact hleftPositive.trans_le
      (Finset.card_le_card (measuredTwoThirdsLeft_subset G vertices))
  · apply measured_right_card_lt G vertices
    exact hrightPositive.trans_le
      (Finset.card_le_card (measuredTwoThirdsRight_subset G vertices))

end QEC.Locality

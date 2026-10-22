import QEC.Coding.FiberBundle.RandomBase.Distance

/-!
# Small-set expansion for the HHO20 random base

This module formalizes the base-graph property used by the cohomology-distance
argument.  We use a `0.92 Delta` local expansion target, slightly stronger
than the paper's displayed `0.9 Delta` target.  Together with the paper's
`1.01 Delta` check-degree upper window this gives the stated `0.09 Delta`
non-counique-neighbor bound by exact integer arithmetic.
-/

namespace QEC.Coding.FiberBundle.RandomBase

open scoped BigOperators

/-- Number of selected checks incident to one variable. -/
def selectedCheckCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r)) : Nat :=
  (S.filter fun a => sample (a, b)).card

/-- Variables neighboring at least one check in `S`. -/
def checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Finset (Fin (4 * r)) :=
  Finset.univ.filter fun b => 0 < selectedCheckCount sample S b

/-- Variables neighboring exactly one selected check. -/
def couniqueNeighbors
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Finset (Fin (4 * r)) :=
  Finset.univ.filter fun b => selectedCheckCount sample S b = 1

/-- Variables neighboring at least two selected checks. -/
def nonCouniqueNeighbors
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Finset (Fin (4 * r)) :=
  Finset.univ.filter fun b => 2 ≤ selectedCheckCount sample S b

/--
Membership in the counique-neighbor set means that exactly one selected check
is incident to the variable.
-/
theorem mem_couniqueNeighbors_iff_exists_unique
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (b : Fin (4 * r)) :
    b ∈ couniqueNeighbors sample S ↔
      ∃ a ∈ S,
        sample (a, b) = true ∧
          ∀ a' ∈ S, sample (a', b) = true → a' = a := by
  constructor
  · intro hb
    have hcard :
        (S.filter fun a => sample (a, b)).card = 1 := by
      exact (Finset.mem_filter.mp hb).2
    rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
    have haMem : a ∈ S.filter fun a => sample (a, b) := by
      rw [ha]
      simp
    refine ⟨a, (Finset.mem_filter.mp haMem).1,
      (Finset.mem_filter.mp haMem).2, ?_⟩
    intro a' ha'S ha'Edge
    have ha'Mem : a' ∈ S.filter fun a => sample (a, b) :=
      Finset.mem_filter.mpr ⟨ha'S, ha'Edge⟩
    rw [ha] at ha'Mem
    simpa using ha'Mem
  · rintro ⟨a, haS, haEdge, haUnique⟩
    have hfilter :
        S.filter (fun a' => sample (a', b)) = {a} := by
      ext a'
      constructor
      · intro ha'
        have ha'S := (Finset.mem_filter.mp ha').1
        have ha'Edge := (Finset.mem_filter.mp ha').2
        simp [haUnique a' ha'S ha'Edge]
      · intro ha'
        have ha'eq : a' = a := by simpa using ha'
        subst a'
        exact Finset.mem_filter.mpr ⟨haS, haEdge⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (S.filter fun a' => sample (a', b)).card = 1
    rw [hfilter, Finset.card_singleton]

/-- Counique neighbors are neighbors. -/
theorem couniqueNeighbors_subset_checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    couniqueNeighbors sample S ⊆ checkSetNeighborhood sample S := by
  intro b hb
  simp only [couniqueNeighbors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hb
  simp only [checkSetNeighborhood, Finset.mem_filter, Finset.mem_univ,
    true_and]
  omega

/-- Non-counique neighbors are neighbors. -/
theorem nonCouniqueNeighbors_subset_checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    nonCouniqueNeighbors sample S ⊆ checkSetNeighborhood sample S := by
  intro b hb
  simp only [nonCouniqueNeighbors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hb
  simp only [checkSetNeighborhood, Finset.mem_filter, Finset.mem_univ,
    true_and]
  omega

/-- The counique and non-counique neighbor sets are disjoint. -/
theorem disjoint_couniqueNeighbors_nonCouniqueNeighbors
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    Disjoint (couniqueNeighbors sample S) (nonCouniqueNeighbors sample S) := by
  rw [Finset.disjoint_left]
  intro b hCounique hNon
  simp only [couniqueNeighbors, nonCouniqueNeighbors, Finset.mem_filter,
    Finset.mem_univ, true_and] at hCounique hNon
  omega

/-- Every neighbor is either counique or non-counique. -/
theorem checkSetNeighborhood_eq_union
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    checkSetNeighborhood sample S =
      couniqueNeighbors sample S ∪ nonCouniqueNeighbors sample S := by
  ext b
  simp only [checkSetNeighborhood, couniqueNeighbors, nonCouniqueNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  omega

/-- Exact cardinality partition of a selected check set's neighborhood. -/
theorem card_checkSetNeighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (checkSetNeighborhood sample S).card =
      (couniqueNeighbors sample S).card +
        (nonCouniqueNeighbors sample S).card := by
  rw [checkSetNeighborhood_eq_union]
  exact Finset.card_union_of_disjoint
    (disjoint_couniqueNeighbors_nonCouniqueNeighbors sample S)

/-- Count incidences between a selected check set and all variables. -/
def selectedIncidenceCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) : Nat :=
  ∑ a ∈ S, checkDegree sample a

/-- Double-count selected incidences by checks or by variables. -/
theorem selectedIncidenceCount_eq_sum_selectedCheckCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    selectedIncidenceCount sample S =
      ∑ b : Fin (4 * r), selectedCheckCount sample S b := by
  classical
  simp only [selectedIncidenceCount, checkDegree, selectedCheckCount,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Variables outside the neighborhood contribute zero selected incidences. -/
theorem selectedIncidenceCount_eq_sum_neighborhood
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    selectedIncidenceCount sample S =
      ∑ b ∈ checkSetNeighborhood sample S,
        selectedCheckCount sample S b := by
  rw [selectedIncidenceCount_eq_sum_selectedCheckCount]
  rw [checkSetNeighborhood, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : 0 < selectedCheckCount sample S b
  · simp [hb]
  · have hzero : selectedCheckCount sample S b = 0 := by omega
    simp [hzero]

/--
The selected incidence count is at least one token per neighbor plus one
additional token per non-counique neighbor.
-/
theorem card_neighborhood_add_nonCounique_le_selectedIncidenceCount
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (checkSetNeighborhood sample S).card +
        (nonCouniqueNeighbors sample S).card ≤
      selectedIncidenceCount sample S := by
  rw [selectedIncidenceCount_eq_sum_neighborhood,
    card_checkSetNeighborhood]
  calc
    (couniqueNeighbors sample S).card +
        (nonCouniqueNeighbors sample S).card +
        (nonCouniqueNeighbors sample S).card =
      (∑ _b ∈ couniqueNeighbors sample S, 1) +
        ∑ _b ∈ nonCouniqueNeighbors sample S, 2 := by simp; omega
    _ ≤
      (∑ b ∈ couniqueNeighbors sample S,
        selectedCheckCount sample S b) +
        ∑ b ∈ nonCouniqueNeighbors sample S,
          selectedCheckCount sample S b := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro b hb
        have hbCount : selectedCheckCount sample S b = 1 := by
          simpa [couniqueNeighbors] using hb
        omega
      · apply Finset.sum_le_sum
        intro b hb
        have hbCount : 2 ≤ selectedCheckCount sample S b := by
          simpa [nonCouniqueNeighbors] using hb
        exact hbCount
    _ = ∑ b ∈ checkSetNeighborhood sample S,
        selectedCheckCount sample S b := by
      rw [checkSetNeighborhood_eq_union, Finset.sum_union
        (disjoint_couniqueNeighbors_nonCouniqueNeighbors sample S)]

/--
The strengthened small-set expansion property used by the deterministic
cohomology-distance closure.  `100000` is HHO20's `XConst`.
-/
def HasStrongSmallSetExpansion
    {r Delta : Nat} (sample : Sample r) : Prop :=
  ∀ S : Finset (Fin (3 * r)),
    100000 * Delta * S.card ≤ 3 * r →
      92 * Delta * S.card ≤
        100 * (checkSetNeighborhood sample S).card

/-- The check-degree upper window bounds selected incidences. -/
theorem selectedIncidenceCount_upper
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) :
    100 * selectedIncidenceCount sample S ≤
      101 * Delta * S.card := by
  rw [selectedIncidenceCount]
  calc
    100 * (∑ a ∈ S, checkDegree sample a) =
        ∑ a ∈ S, 100 * checkDegree sample a := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _a ∈ S, 101 * Delta := by
      exact Finset.sum_le_sum fun a _ => (hDegree.1 a).2
    _ = 101 * Delta * S.card := by
      simp [Nat.mul_comm]

/--
Strong small-set expansion plus the degree window gives the paper's
`0.09 Delta |S|` non-counique-neighbor bound.
-/
theorem nonCouniqueNeighbors_bound
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    100 * (nonCouniqueNeighbors sample S).card ≤
      9 * Delta * S.card := by
  have hTokens :=
    card_neighborhood_add_nonCounique_le_selectedIncidenceCount sample S
  have hIncidence := selectedIncidenceCount_upper hDegree S
  have hNeighborhood := hExpansion S hSmall
  have hTokens100 := Nat.mul_le_mul_left 100 hTokens
  ring_nf at hTokens100 hIncidence hNeighborhood ⊢
  omega

/-- At least `0.83 Delta |S|` neighbors are counique. -/
theorem couniqueNeighbors_lower
    {r Delta : Nat} {sample : Sample r}
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    83 * Delta * S.card ≤
      100 * (couniqueNeighbors sample S).card := by
  have hNeighborhood := hExpansion S hSmall
  have hNon := nonCouniqueNeighbors_bound hDegree hExpansion S hSmall
  rw [card_checkSetNeighborhood] at hNeighborhood
  ring_nf at hNeighborhood hNon ⊢
  omega

/-- Number of counique neighbors belonging to one selected check. -/
def couniqueDegree
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) (a : Fin (3 * r)) : Nat :=
  ((couniqueNeighbors sample S).filter fun b => sample (a, b)).card

/-- Counique degrees double-count to exactly the number of counique variables. -/
theorem sum_couniqueDegree
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r))) :
    (∑ a ∈ S, couniqueDegree sample S a) =
      (couniqueNeighbors sample S).card := by
  classical
  calc
    (∑ a ∈ S, couniqueDegree sample S a) =
        ∑ a ∈ S, ∑ b ∈ couniqueNeighbors sample S,
          if sample (a, b) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [couniqueDegree, Finset.card_eq_sum_ones]
      exact sum_filter_eq_sum_ite
        (couniqueNeighbors sample S)
        (fun b => sample (a, b))
        (fun _ => 1)
    _ = ∑ b ∈ couniqueNeighbors sample S, ∑ a ∈ S,
          if sample (a, b) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ couniqueNeighbors sample S,
          selectedCheckCount sample S b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [selectedCheckCount, Finset.card_eq_sum_ones]
      exact (sum_filter_eq_sum_ite
        S
        (fun a => sample (a, b))
        (fun _ => 1)).symm
    _ = ∑ _b ∈ couniqueNeighbors sample S, 1 := by
      apply Finset.sum_congr rfl
      intro b hb
      simpa [couniqueNeighbors] using hb
    _ = _ := by simp

/--
Every nonempty sufficiently small check set contains a check with more than
`0.81 Delta` counique neighbors.
-/
theorem exists_check_many_couniqueNeighbors
    {r Delta : Nat} {sample : Sample r}
    (hDelta : 0 < Delta)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) (hS : S.Nonempty)
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    ∃ a ∈ S, 81 * Delta < 100 * couniqueDegree sample S a := by
  have hCounique :=
    couniqueNeighbors_lower hDegree hExpansion S hSmall
  by_contra hExists
  push Not at hExists
  have hUpper :
      100 * (∑ a ∈ S, couniqueDegree sample S a) ≤
        81 * Delta * S.card := by
    calc
      100 * (∑ a ∈ S, couniqueDegree sample S a) =
          ∑ a ∈ S, 100 * couniqueDegree sample S a := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _a ∈ S, 81 * Delta := by
        exact Finset.sum_le_sum fun a ha => hExists a ha
      _ = 81 * Delta * S.card := by
        simp [Nat.mul_comm]
  rw [sum_couniqueDegree] at hUpper
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  have hProduct : 0 < Delta * S.card := Nat.mul_pos hDelta hScard
  ring_nf at hCounique hUpper hProduct
  omega

/--
The selected check from the preceding lemma has a strict `4/5` counique
fraction of its whole neighborhood.
-/
theorem exists_check_four_fifths_counique
    {r Delta : Nat} {sample : Sample r}
    (hDelta : 0 < Delta)
    (hDegree : HasDegreeWindows (Delta := Delta) sample)
    (hExpansion : HasStrongSmallSetExpansion (Delta := Delta) sample)
    (S : Finset (Fin (3 * r))) (hS : S.Nonempty)
    (hSmall : 100000 * Delta * S.card ≤ 3 * r) :
    ∃ a ∈ S,
      4 * checkDegree sample a < 5 * couniqueDegree sample S a := by
  rcases exists_check_many_couniqueNeighbors
      hDelta hDegree hExpansion S hS hSmall with
    ⟨a, haS, haCounique⟩
  refine ⟨a, haS, ?_⟩
  have haDegree := (hDegree.1 a).2
  ring_nf at haDegree haCounique ⊢
  nlinarith

/-! ## Exact probability of a fixed small-set expansion witness -/

/--
All incidences from `S` to variables outside `T` are absent.  Equivalently,
the neighborhood of `S` is contained in `T`.
-/
def AvoidsOutside
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) (sample : Sample r) : Prop :=
  ∀ edge : Fin (3 * r) × Fin (4 * r),
    if edge.1 ∈ S ∧ edge.2 ∉ T then sample edge = false else True

instance instDecidablePredAvoidsOutside
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    DecidablePred (AvoidsOutside S T) := by
  intro sample
  unfold AvoidsOutside
  infer_instance

/-- Avoiding all outside incidences is exactly neighborhood containment. -/
theorem avoidsOutside_iff_neighborhood_subset
    {r : Nat} (sample : Sample r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    AvoidsOutside S T sample ↔
      checkSetNeighborhood sample S ⊆ T := by
  constructor
  · intro h b hb
    simp only [checkSetNeighborhood, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb
    have hbNonempty :
        (S.filter fun a => sample (a, b)).Nonempty := by
      exact Finset.card_pos.mp hb
    rcases hbNonempty with ⟨a, haFiltered⟩
    have haS : a ∈ S := (Finset.mem_filter.mp haFiltered).1
    have haEdge : sample (a, b) = true :=
      (Finset.mem_filter.mp haFiltered).2
    by_contra hbT
    have hOutside := h (a, b)
    simp [haS, hbT, haEdge] at hOutside
  · intro h edge
    by_cases hConstraint : edge.1 ∈ S ∧ edge.2 ∉ T
    · rw [if_pos hConstraint]
      apply Bool.eq_false_iff.mpr
      intro hEdge
      have hbNeighborhood : edge.2 ∈ checkSetNeighborhood sample S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply Finset.card_pos.mpr
        exact ⟨edge.1, Finset.mem_filter.mpr ⟨hConstraint.1, hEdge⟩⟩
      exact hConstraint.2 (h hbNeighborhood)
    · rw [if_neg hConstraint]
      trivial

/-- The constrained edge set is the Cartesian product `S × (univ \ T)`. -/
theorem constrainedEdges_filter
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    (Finset.univ.filter fun edge : Fin (3 * r) × Fin (4 * r) =>
      edge.1 ∈ S ∧ edge.2 ∉ T) =
      S ×ˢ ((Finset.univ : Finset (Fin (4 * r))) \ T) := by
  ext edge
  simp

/-- Exact number of constrained incidences from `S` to outside `T`. -/
theorem card_constrainedEdges
    {r : Nat} (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    (Finset.univ.filter fun edge : Fin (3 * r) × Fin (4 * r) =>
      edge.1 ∈ S ∧ edge.2 ∉ T).card =
      S.card * (4 * r - T.card) := by
  rw [constrainedEdges_filter, Finset.card_product, Finset.card_sdiff]
  simp

/-- Mass of the `false` outcome of the construction's Bernoulli coordinate. -/
theorem bernoulli_false_eventMass
    (p : NNReal) (hp : p ≤ 1) :
    eventMass (PMF.bernoulli p hp) (fun bit => bit = false) =
      ((1 - p : NNReal) : ENNReal) := by
  classical
  rw [eventMass, show (Finset.univ : Finset Bool) = {false, true} by decide]
  rw [show ({false, true} : Finset Bool).filter
    (fun bit => bit = false) = {false} by decide]
  simp only [Finset.sum_singleton, PMF.bernoulli_apply, Bool.cond_false]

/-- The sure event under one Bernoulli coordinate has mass one. -/
theorem bernoulli_true_eventMass
    (p : NNReal) (hp : p ≤ 1) :
    eventMass (PMF.bernoulli p hp) (fun _bit => True) = 1 := by
  classical
  rw [eventMass, show (Finset.univ : Finset Bool) = {false, true} by decide]
  rw [show ({false, true} : Finset Bool).filter
    (fun _bit => True) = {false, true} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, Bool.false_eq_true,
    not_false_eq_true, Finset.sum_singleton, PMF.bernoulli_apply,
    Bool.cond_false, Bool.cond_true]
  rw [ENNReal.coe_sub]
  exact tsub_add_cancel_of_le (by exact_mod_cast hp)

/-- Finite event mass respects pointwise logical equivalence. -/
theorem eventMass_congr
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (left right : Ω → Prop)
    [DecidablePred left] [DecidablePred right]
    (h : ∀ ω, left ω ↔ right ω) :
    eventMass p left = eventMass p right := by
  rw [eventMass_eq_toMeasure, eventMass_eq_toMeasure]
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  exact h ω

/--
Exact probability of a fixed neighborhood-containment witness.  This is the
Bernoulli analogue of the paper's regular-model counting step.
-/
theorem avoidsOutside_eventMass
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (AvoidsOutside S T) =
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        (S.card * (4 * r - T.card))) := by
  classical
  let coordinateEvent :
      (Fin (3 * r) × Fin (4 * r)) → Bool → Prop :=
    fun edge bit =>
      if edge.1 ∈ S ∧ edge.2 ∉ T then bit = false else True
  calc
    _ = ∏ edge : Fin (3 * r) × Fin (4 * r),
        eventMass
          (PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
          (coordinateEvent edge) := by
      rw [distribution]
      exact eventMass_independentProduct_forall
        (fun _ : Fin (3 * r) × Fin (4 * r) =>
          PMF.bernoulli
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta))
        coordinateEvent
    _ = ∏ edge : Fin (3 * r) × Fin (4 * r),
        if edge.1 ∈ S ∧ edge.2 ∉ T then
          ((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal)
        else 1 := by
      apply Fintype.prod_congr
      intro edge
      by_cases hConstraint : edge.1 ∈ S ∧ edge.2 ∉ T
      · rw [if_pos hConstraint]
        calc
          eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (coordinateEvent edge) =
            eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (fun bit => bit = false) := by
            apply eventMass_congr
            intro bit
            dsimp [coordinateEvent]
            rw [if_pos hConstraint]
          _ = _ := bernoulli_false_eventMass
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta)
      · rw [if_neg hConstraint]
        calc
          eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (coordinateEvent edge) =
            eventMass
              (PMF.bernoulli
                (incidenceProbability (4 * r) Delta)
                (incidenceProbability_le_one hDelta))
              (fun _bit => True) := by
            apply eventMass_congr
            intro bit
            dsimp [coordinateEvent]
            rw [if_neg hConstraint]
          _ = _ := bernoulli_true_eventMass
            (incidenceProbability (4 * r) Delta)
            (incidenceProbability_le_one hDelta)
    _ = ∏ edge ∈
        (Finset.univ.filter fun edge : Fin (3 * r) × Fin (4 * r) =>
          edge.1 ∈ S ∧ edge.2 ∉ T),
        ((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) := by
      rw [Finset.prod_ite]
      simp
    _ = _ := by
      rw [Finset.prod_const, card_constrainedEdges]

/-- A check set and too-small containing variable set witness expansion failure. -/
def ExpansionWitness (r Delta : Nat) :=
  {pair :
      Finset (Fin (3 * r)) × Finset (Fin (4 * r)) //
    100000 * Delta * pair.1.card ≤ 3 * r ∧
      100 * pair.2.card < 92 * Delta * pair.1.card}

noncomputable instance instFintypeExpansionWitness (r Delta : Nat) :
    Fintype (ExpansionWitness r Delta) :=
  Fintype.subtype
    (Finset.univ.filter fun pair :
      Finset (Fin (3 * r)) × Finset (Fin (4 * r)) =>
        100000 * Delta * pair.1.card ≤ 3 * r ∧
          100 * pair.2.card < 92 * Delta * pair.1.card)
    (by simp)

noncomputable instance instDecidablePredHasStrongSmallSetExpansion
    (r Delta : Nat) :
    DecidablePred
      (fun sample : Sample r =>
        HasStrongSmallSetExpansion (Delta := Delta) sample) :=
  Classical.decPred _

/-- Every failed expansion instance produces a finite containment witness. -/
theorem exists_expansionWitness_of_not_hasStrongSmallSetExpansion
    {r Delta : Nat} {sample : Sample r}
    (h : ¬HasStrongSmallSetExpansion (Delta := Delta) sample) :
    ∃ witness : ExpansionWitness r Delta,
      AvoidsOutside witness.1.1 witness.1.2 sample := by
  rw [HasStrongSmallSetExpansion] at h
  push Not at h
  rcases h with ⟨S, hSmall, hExpansion⟩
  let T := checkSetNeighborhood sample S
  have hAvoids : AvoidsOutside S T sample := by
    rw [avoidsOutside_iff_neighborhood_subset]
  exact ⟨⟨(S, T), hSmall, hExpansion⟩, hAvoids⟩

/--
Expansion failure is bounded by the exact sum over all finite containment
witnesses.
-/
theorem strongSmallSetExpansion_failureMass_le_exact_sum
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    failureMass
        (distribution r Delta hDelta)
        (fun sample =>
          HasStrongSmallSetExpansion (Delta := Delta) sample) ≤
      ∑ witness : ExpansionWitness r Delta,
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          (witness.1.1.card * (4 * r - witness.1.2.card))) := by
  calc
    _ ≤ ∑ witness : ExpansionWitness r Delta,
        eventMass
          (distribution r Delta hDelta)
          (AvoidsOutside witness.1.1 witness.1.2) := by
      apply failureMass_le_sum_eventMass
      intro sample hsample
      exact exists_expansionWitness_of_not_hasStrongSmallSetExpansion hsample
    _ = _ := by
      apply Fintype.sum_congr
      intro witness
      exact avoidsOutside_eventMass
        r Delta hDelta witness.1.1 witness.1.2

end QEC.Coding.FiberBundle.RandomBase

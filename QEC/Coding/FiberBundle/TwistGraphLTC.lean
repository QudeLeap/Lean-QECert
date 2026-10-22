import QEC.Coding.FiberBundle.TwistGraph

/-!
# Local testability events for the HHO20 twist graph

This module formalizes the deterministic event interfaces from
`hastings-haah-odonnell-2020-fiber-bundle/bundle.tex:1095-1234`:
Proposition `prop:chi`, Lemma `lem:key-light`, and Lemma `thm:key-heavy`.

All decimal constants are represented by integer-cleared inequalities.  The
predicates below are internal events of the explicit random base/head-tail
sampler.  The final construction theorem must prove that a sampled pair
satisfies them; it does not accept them from a caller.
-/

namespace QEC.Coding.FiberBundle.TwistGraph

open scoped BigOperators

private theorem sum_card_type_partition
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (p : A → Prop) [DecidablePred p] :
    (∑ b : B, (Finset.univ.filter fun a => f a = b ∧ p a).card) =
      (Finset.univ.filter p).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hp : p a <;> simp [hp]

/--
The HHO20 type check imposed on a pair `(y,z)`: tail incidences read `y` and
head incidences read `z`.
-/
noncomputable def pairCheckSyndrome
    {r typeCount ell : Nat}
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) : ZMod 2 :=
  ∑ b : Fin (4 * r),
    RandomBase.boundary baseSample a b *
      if RandomTwist.isTail twistSample a b then y b else z b

/-- Violated checks of one fixed partition type on `(y,z)`. -/
noncomputable def typeViolationSet
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    Finset (Fin (3 * r)) := by
  classical
  exact Finset.univ.filter fun a =>
    RandomTwist.checkType typeCount a = τ ∧
      pairCheckSyndrome baseSample twistSample y z a ≠ 0

/-- Number of violated type-`τ` checks on `(y,z)`. -/
noncomputable def typeViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) : Nat :=
  (typeViolationSet baseSample twistSample τ y z).card

theorem mem_typeViolationSet_iff
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    a ∈ typeViolationSet baseSample twistSample τ y z ↔
      RandomTwist.checkType typeCount a = τ ∧
        pairCheckSyndrome baseSample twistSample y z a ≠ 0 := by
  classical
  simp [typeViolationSet]

/--
A graph check is definitionally the corresponding type check on its source
and target layer words.
-/
theorem checkSyndrome_eq_pairCheckSyndrome
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) :
    checkSyndrome baseSample twistSample w u a =
      pairCheckSyndrome baseSample twistSample
        (layerWord w u)
        (layerWord w
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u))
        a := by
  rfl

/--
Violations of the type-`τ` checks whose directed twist edge leaves `u`.
-/
noncomputable def outgoingTypeViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) : Nat :=
  typeViolationCount baseSample twistSample τ
    (layerWord w u)
    (layerWord w (outNeighbor twistSample τ u))

/--
Violations of the type-`τ` checks whose directed twist edge enters `u`.
-/
noncomputable def incomingTypeViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) : Nat :=
  typeViolationCount baseSample twistSample τ
    (layerWord w (inNeighbor twistSample τ u))
    (layerWord w u)

/-- Number of all violated checks incident to one twist-graph layer. -/
noncomputable def incidentViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) : Nat :=
  ∑ τ : Fin typeCount,
    (outgoingTypeViolationCount baseSample twistSample w u τ +
      incomingTypeViolationCount baseSample twistSample w u τ)

/--
The outgoing type count is the corresponding fiber of the global violated
checks at source layer `u`.
-/
theorem outgoingTypeViolationCount_eq_card_filter
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) :
    outgoingTypeViolationCount baseSample twistSample w u τ =
      (Finset.univ.filter fun a : Fin (3 * r) =>
        RandomTwist.checkType typeCount a = τ ∧
          checkSyndrome baseSample twistSample w u a ≠ 0).card := by
  classical
  rw [outgoingTypeViolationCount, typeViolationCount]
  apply congrArg Finset.card
  ext a
  simp only [mem_typeViolationSet_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨htype, hviol⟩
    refine ⟨htype, ?_⟩
    rw [checkSyndrome_eq_pairCheckSyndrome, htype]
    exact hviol
  · rintro ⟨htype, hviol⟩
    refine ⟨htype, ?_⟩
    rw [checkSyndrome_eq_pairCheckSyndrome, htype] at hviol
    exact hviol

/-- At a fixed layer, summing over types gives all outgoing violations. -/
theorem sum_outgoingTypeViolationCount_eq_card_filter
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    (∑ τ : Fin typeCount,
      outgoingTypeViolationCount baseSample twistSample w u τ) =
      (Finset.univ.filter fun a : Fin (3 * r) =>
        checkSyndrome baseSample twistSample w u a ≠ 0).card := by
  classical
  simp_rw [outgoingTypeViolationCount_eq_card_filter]
  exact sum_card_type_partition
    (RandomTwist.checkType typeCount)
    (fun a => checkSyndrome baseSample twistSample w u a ≠ 0)

/-- Every violated check is counted once at the source of its twist edge. -/
theorem sum_outgoingTypeViolationCount_eq_violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell, ∑ τ : Fin typeCount,
      outgoingTypeViolationCount baseSample twistSample w u τ) =
        violationCount baseSample twistSample w := by
  classical
  simp_rw [sum_outgoingTypeViolationCount_eq_card_filter]
  simp only [violationCount, violationSet, Finset.card_filter,
    Fintype.sum_prod_type]

/-- An incoming count is the outgoing count at the unique source layer. -/
theorem incomingTypeViolationCount_eq_outgoing_inNeighbor
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) :
    incomingTypeViolationCount baseSample twistSample w u τ =
      outgoingTypeViolationCount baseSample twistSample w
        (inNeighbor twistSample τ u) τ := by
  simp [incomingTypeViolationCount, outgoingTypeViolationCount]

/-- Every violated check is counted once at the target of its twist edge. -/
theorem sum_incomingTypeViolationCount_eq_violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell, ∑ τ : Fin typeCount,
      incomingTypeViolationCount baseSample twistSample w u τ) =
        violationCount baseSample twistSample w := by
  calc
    _ = ∑ τ : Fin typeCount, ∑ u : ZMod ell,
        incomingTypeViolationCount baseSample twistSample w u τ := by
          rw [Finset.sum_comm]
    _ = ∑ τ : Fin typeCount, ∑ u : ZMod ell,
        outgoingTypeViolationCount baseSample twistSample w
          (inNeighbor twistSample τ u) τ := by
          simp_rw [incomingTypeViolationCount_eq_outgoing_inNeighbor]
    _ = ∑ τ : Fin typeCount, ∑ u : ZMod ell,
        outgoingTypeViolationCount baseSample twistSample w u τ := by
          apply Fintype.sum_congr
          intro τ
          exact (typeTranslation twistSample τ).symm.sum_comp
            (fun u =>
              outgoingTypeViolationCount baseSample twistSample w u τ)
    _ = ∑ u : ZMod ell, ∑ τ : Fin typeCount,
        outgoingTypeViolationCount baseSample twistSample w u τ := by
          rw [Finset.sum_comm]
    _ = violationCount baseSample twistSample w :=
      sum_outgoingTypeViolationCount_eq_violationCount
        baseSample twistSample w

/--
The exact double-counting identity used in HHO20 `thm:ltc`: each violated
twist check is incident to its source and target layers, and hence is counted
exactly twice.
-/
theorem sum_incidentViolationCount_eq_two_mul_violationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell,
      incidentViolationCount baseSample twistSample w u) =
        2 * violationCount baseSample twistSample w := by
  simp only [incidentViolationCount, Finset.sum_add_distrib]
  rw [sum_outgoingTypeViolationCount_eq_violationCount,
    sum_incomingTypeViolationCount_eq_violationCount]
  omega

/-- Layers with word weight at most `2n / Delta`, where `n = 4r`. -/
noncomputable def lightLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    Delta * HammingWeight (layerWord w u) ≤ 2 * (4 * r)

/-- Layers with word weight strictly between `2n / Delta` and `4n / Delta`. -/
noncomputable def mediumLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    2 * (4 * r) < Delta * HammingWeight (layerWord w u) ∧
      Delta * HammingWeight (layerWord w u) < 4 * (4 * r)

/-- Layers with word weight at least `4n / Delta`. -/
noncomputable def heavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    4 * (4 * r) ≤ Delta * HammingWeight (layerWord w u)

/-- The union of the light and medium layers, expressed by one inequality. -/
noncomputable def nonheavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact Finset.univ.filter fun u =>
    Delta * HammingWeight (layerWord w u) < 4 * (4 * r)

@[simp]
theorem mem_lightLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ lightLayerSet Delta w ↔
      Delta * HammingWeight (layerWord w u) ≤ 2 * (4 * r) := by
  classical
  simp only [lightLayerSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_mediumLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ mediumLayerSet Delta w ↔
      2 * (4 * r) < Delta * HammingWeight (layerWord w u) ∧
        Delta * HammingWeight (layerWord w u) < 4 * (4 * r) := by
  classical
  simp only [mediumLayerSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_heavyLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ heavyLayerSet Delta w ↔
      4 * (4 * r) ≤ Delta * HammingWeight (layerWord w u) := by
  classical
  simp only [heavyLayerSet, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_nonheavyLayerSet_iff
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ nonheavyLayerSet Delta w ↔
      Delta * HammingWeight (layerWord w u) < 4 * (4 * r) := by
  classical
  simp only [nonheavyLayerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The light/medium union is exactly the set of nonheavy layers. -/
theorem lightLayerSet_union_mediumLayerSet
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    lightLayerSet Delta w ∪ mediumLayerSet Delta w =
      nonheavyLayerSet Delta w := by
  classical
  ext u
  simp only [Finset.mem_union, mem_lightLayerSet_iff,
    mem_mediumLayerSet_iff, mem_nonheavyLayerSet_iff]
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  omega

/-- Every layer is uniquely nonheavy or heavy. -/
theorem nonheavyLayerSet_union_heavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    nonheavyLayerSet Delta w ∪ heavyLayerSet Delta w = Finset.univ := by
  classical
  ext u
  simp only [Finset.mem_union, mem_nonheavyLayerSet_iff,
    mem_heavyLayerSet_iff, Finset.mem_univ, iff_true]
  omega

theorem disjoint_nonheavyLayerSet_heavyLayerSet
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Disjoint (nonheavyLayerSet Delta w) (heavyLayerSet Delta w) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro u hnonheavy hheavy
  rw [mem_nonheavyLayerSet_iff] at hnonheavy
  rw [mem_heavyLayerSet_iff] at hheavy
  omega

/-- Number of directed in/out type incidences from `u` landing in `layers`. -/
noncomputable def neighborIncidenceCount
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (layers : Finset (ZMod ell))
    (u : ZMod ell) : Nat :=
  ∑ τ : Fin typeCount,
    ((if outNeighbor twistSample τ u ∈ layers then 1 else 0) +
      (if inNeighbor twistSample τ u ∈ layers then 1 else 0))

/--
Nonheavy layers with at least one tenth of their `2 * typeCount` directed
neighbor incidences also nonheavy.
-/
noncomputable def usableNonheavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact (nonheavyLayerSet Delta w).filter fun u =>
    typeCount ≤
      5 * neighborIncidenceCount twistSample
        (nonheavyLayerSet Delta w) u

/-- The nonheavy layers lacking the one-tenth usable-neighbor guarantee. -/
noncomputable def badNonheavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) :=
  nonheavyLayerSet Delta w \ usableNonheavyLayerSet Delta twistSample w

/-- Types for which both directed neighbors of `u` are light. -/
noncomputable def twoSidedLightTypeSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) : Finset (Fin typeCount) := by
  classical
  exact Finset.univ.filter fun τ =>
    outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
      inNeighbor twistSample τ u ∈ lightLayerSet Delta w

/--
Heavy layers for which at least `.98 typeCount` types have both neighboring
layers light.
-/
noncomputable def usableHeavyLayerSet
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    Finset (ZMod ell) := by
  classical
  exact (heavyLayerSet Delta w).filter fun u =>
    98 * typeCount ≤
      100 * (twoSidedLightTypeSet Delta twistSample w u).card

@[simp]
theorem mem_usableNonheavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ usableNonheavyLayerSet Delta twistSample w ↔
      u ∈ nonheavyLayerSet Delta w ∧
        typeCount ≤
          5 * neighborIncidenceCount twistSample
            (nonheavyLayerSet Delta w) u := by
  classical
  simp [usableNonheavyLayerSet]

@[simp]
theorem mem_badNonheavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ badNonheavyLayerSet Delta twistSample w ↔
      u ∈ nonheavyLayerSet Delta w ∧
        u ∉ usableNonheavyLayerSet Delta twistSample w := by
  classical
  simp [badNonheavyLayerSet]

@[simp]
theorem mem_twoSidedLightTypeSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (τ : Fin typeCount) :
    τ ∈ twoSidedLightTypeSet Delta twistSample w u ↔
      outNeighbor twistSample τ u ∈ lightLayerSet Delta w ∧
        inNeighbor twistSample τ u ∈ lightLayerSet Delta w := by
  classical
  simp [twoSidedLightTypeSet]

@[simp]
theorem mem_usableHeavyLayerSet_iff
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    u ∈ usableHeavyLayerSet Delta twistSample w ↔
      u ∈ heavyLayerSet Delta w ∧
        98 * typeCount ≤
          100 * (twoSidedLightTypeSet Delta twistSample w u).card := by
  classical
  simp [usableHeavyLayerSet]

/--
The exact graph-mixing consequences consumed by deterministic HHO20
`thm:ltc`.

The first conclusion bounds unusable nonheavy layers by `1.25 |H|`.  In the
second (heavy) case, at least `.9 |H|` heavy layers have `.98 typeCount`
two-sided light types.  This is an internal event: the construction must
derive it from the sampled twist graph's spectral bound.
-/
def HasHHO20LayerMixing
    {r typeCount ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ w : Word (ZMod 2) (ZMod ell × Fin (4 * r)),
    5000 * Delta * HammingWeight w ≤ ell * (4 * r) →
      4 * (badNonheavyLayerSet Delta twistSample w).card ≤
          5 * (heavyLayerSet Delta w).card ∧
        ((mediumLayerSet Delta w).card <
            1000 * (heavyLayerSet Delta w).card →
          9 * (heavyLayerSet Delta w).card ≤
            10 * (usableHeavyLayerSet Delta twistSample w).card)

/--
Integer-cleared conclusion of HHO20 Lemma `lem:key-light`.

The hypotheses say `|y|,|z| ≤ 4n/Delta`, with `n = 4r`.  The conclusion is
`violations ≥ .01 * (Delta/typeCount) * (|y|+|z|)`.
-/
def HasHHO20LightChecks
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ (τ : Fin typeCount)
      (y z : Word (ZMod 2) (Fin (4 * r))),
    Delta * HammingWeight y ≤ 4 * (4 * r) →
    Delta * HammingWeight z ≤ 4 * (4 * r) →
      Delta * (HammingWeight y + HammingWeight z) ≤
        100 * typeCount *
          typeViolationCount baseSample twistSample τ y z

/--
Total violations in the two type-check families incident to a proposed heavy
layer word `x`.
-/
noncomputable def heavyIncidentViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (types : Finset (Fin typeCount))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r))) : Nat :=
  ∑ τ ∈ types,
    (typeViolationCount baseSample twistSample τ x (outWord τ) +
      typeViolationCount baseSample twistSample τ (inWord τ) x)

/--
Integer-cleared conclusion of HHO20 Lemma `thm:key-heavy`.

`x` has weight at least `4n/Delta`; at least `.98 typeCount` types have light
in- and out-neighbor words of weight at most `2n/Delta`; the incident checks
then contain at least `.01n` violations.
-/
def HasHHO20HeavyChecks
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∀ (x : Word (ZMod 2) (Fin (4 * r)))
      (types : Finset (Fin typeCount))
      (outWord inWord :
        Fin typeCount → Word (ZMod 2) (Fin (4 * r))),
    4 * (4 * r) ≤ Delta * HammingWeight x →
    98 * typeCount ≤ 100 * types.card →
    (∀ τ ∈ types,
      Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
      Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r)) →
      4 * r ≤
        100 *
          heavyIncidentViolationCount baseSample twistSample
            x types outWord inWord

/-- The two partitioned-base events consumed by deterministic `thm:ltc`. -/
def HasHHO20PartitionedChecks
    {r typeCount ell : Nat}
    [NeZero typeCount]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell) : Prop :=
  HasHHO20LightChecks Delta baseSample twistSample ∧
    HasHHO20HeavyChecks Delta baseSample twistSample

/-- A nonheavy-to-nonheavy outgoing incidence pays for the source weight. -/
theorem layerWeight_le_outgoingTypeViolationCount_of_nonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell) (τ : Fin typeCount)
    (hu : u ∈ nonheavyLayerSet Delta w)
    (hv :
      outNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w) :
    Delta * HammingWeight (layerWord w u) ≤
      100 * typeCount *
        outgoingTypeViolationCount baseSample twistSample w u τ := by
  have hu' :
      Delta * HammingWeight (layerWord w u) ≤ 4 * (4 * r) :=
    Nat.le_of_lt (mem_nonheavyLayerSet_iff Delta w u |>.mp hu)
  have hv' :
      Delta *
          HammingWeight
            (layerWord w (outNeighbor twistSample τ u)) ≤
        4 * (4 * r) :=
    Nat.le_of_lt
      (mem_nonheavyLayerSet_iff Delta w
        (outNeighbor twistSample τ u) |>.mp hv)
  have hpair := hLight τ
    (layerWord w u)
    (layerWord w (outNeighbor twistSample τ u))
    hu' hv'
  calc
    Delta * HammingWeight (layerWord w u) ≤
        Delta * HammingWeight (layerWord w u) +
          Delta *
            HammingWeight
              (layerWord w (outNeighbor twistSample τ u)) :=
      Nat.le_add_right _ _
    _ = Delta *
        (HammingWeight (layerWord w u) +
          HammingWeight
            (layerWord w (outNeighbor twistSample τ u))) := by
      rw [Nat.mul_add]
    _ ≤ 100 * typeCount *
        outgoingTypeViolationCount baseSample twistSample w u τ := by
      simpa [outgoingTypeViolationCount] using hpair

/-- A nonheavy-to-nonheavy incoming incidence pays for the target weight. -/
theorem layerWeight_le_incomingTypeViolationCount_of_nonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell) (τ : Fin typeCount)
    (hu : u ∈ nonheavyLayerSet Delta w)
    (hv :
      inNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w) :
    Delta * HammingWeight (layerWord w u) ≤
      100 * typeCount *
        incomingTypeViolationCount baseSample twistSample w u τ := by
  have hu' :
      Delta * HammingWeight (layerWord w u) ≤ 4 * (4 * r) :=
    Nat.le_of_lt (mem_nonheavyLayerSet_iff Delta w u |>.mp hu)
  have hv' :
      Delta *
          HammingWeight
            (layerWord w (inNeighbor twistSample τ u)) ≤
        4 * (4 * r) :=
    Nat.le_of_lt
      (mem_nonheavyLayerSet_iff Delta w
        (inNeighbor twistSample τ u) |>.mp hv)
  have hpair := hLight τ
    (layerWord w (inNeighbor twistSample τ u))
    (layerWord w u)
    hv' hu'
  calc
    Delta * HammingWeight (layerWord w u) ≤
        Delta *
            HammingWeight
              (layerWord w (inNeighbor twistSample τ u)) +
          Delta * HammingWeight (layerWord w u) :=
      Nat.le_add_left _ _
    _ = Delta *
        (HammingWeight
            (layerWord w (inNeighbor twistSample τ u)) +
          HammingWeight (layerWord w u)) := by
      rw [Nat.mul_add]
    _ ≤ 100 * typeCount *
        incomingTypeViolationCount baseSample twistSample w u τ := by
      simpa [incomingTypeViolationCount] using hpair

/--
Summing the light-check lemma over all usable directed incidences at one
nonheavy layer.
-/
theorem neighborIncidenceCount_mul_layerWeight_le_incidentViolationCount
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell)
    (hu : u ∈ nonheavyLayerSet Delta w) :
    neighborIncidenceCount twistSample (nonheavyLayerSet Delta w) u *
        (Delta * HammingWeight (layerWord w u)) ≤
      100 * typeCount *
        incidentViolationCount baseSample twistSample w u := by
  rw [neighborIncidenceCount, incidentViolationCount, Finset.sum_mul]
  calc
    (∑ τ : Fin typeCount,
      ((if outNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w
          then 1 else 0) +
        (if inNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w
          then 1 else 0)) *
        (Delta * HammingWeight (layerWord w u))) =
        ∑ τ : Fin typeCount,
          ((if outNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w
              then Delta * HammingWeight (layerWord w u) else 0) +
            (if inNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w
              then Delta * HammingWeight (layerWord w u) else 0)) := by
      apply Fintype.sum_congr
      intro τ
      by_cases hout :
          outNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w <;>
        by_cases hin :
          inNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w <;>
        simp only [hout, hin, if_true, if_false, Nat.add_mul, one_mul,
          zero_mul, zero_add, add_zero]
    _ ≤ ∑ τ : Fin typeCount,
        (100 * typeCount *
            outgoingTypeViolationCount baseSample twistSample w u τ +
          100 * typeCount *
            incomingTypeViolationCount baseSample twistSample w u τ) := by
      apply Finset.sum_le_sum
      intro τ hτ
      apply Nat.add_le_add
      · by_cases hout :
            outNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w
        · rw [if_pos hout]
          exact
            layerWeight_le_outgoingTypeViolationCount_of_nonheavy
              Delta baseSample twistSample w hLight u τ hu hout
        · rw [if_neg hout]
          exact Nat.zero_le _
      · by_cases hin :
            inNeighbor twistSample τ u ∈ nonheavyLayerSet Delta w
        · rw [if_pos hin]
          exact
            layerWeight_le_incomingTypeViolationCount_of_nonheavy
              Delta baseSample twistSample w hLight u τ hu hin
        · rw [if_neg hin]
          exact Nat.zero_le _
    _ = 100 * typeCount *
        (∑ τ : Fin typeCount,
          (outgoingTypeViolationCount baseSample twistSample w u τ +
            incomingTypeViolationCount baseSample twistSample w u τ)) := by
      simp only [Nat.mul_add, Finset.mul_sum]

/-- The local `.002 Delta` bound for a usable nonheavy layer. -/
theorem layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (u : ZMod ell)
    (hu : u ∈ usableNonheavyLayerSet Delta twistSample w) :
    Delta * HammingWeight (layerWord w u) ≤
      500 * incidentViolationCount baseSample twistSample w u := by
  have hu' := mem_usableNonheavyLayerSet_iff
    Delta twistSample w u |>.mp hu
  have hinc :=
    neighborIncidenceCount_mul_layerWeight_le_incidentViolationCount
      Delta baseSample twistSample w hLight u hu'.1
  have hmul :
      typeCount * (Delta * HammingWeight (layerWord w u)) ≤
        typeCount *
          (500 * incidentViolationCount baseSample twistSample w u) := by
    calc
      typeCount * (Delta * HammingWeight (layerWord w u)) ≤
          (5 *
              neighborIncidenceCount twistSample
                (nonheavyLayerSet Delta w) u) *
            (Delta * HammingWeight (layerWord w u)) :=
        Nat.mul_le_mul_right _ hu'.2
      _ = 5 *
          (neighborIncidenceCount twistSample
              (nonheavyLayerSet Delta w) u *
            (Delta * HammingWeight (layerWord w u))) := by ring
      _ ≤ 5 *
          (100 * typeCount *
            incidentViolationCount baseSample twistSample w u) :=
        Nat.mul_le_mul_left 5 hinc
      _ = typeCount *
          (500 * incidentViolationCount baseSample twistSample w u) := by
        ring
  exact Nat.le_of_mul_le_mul_left hmul
    (Nat.pos_of_ne_zero (NeZero.ne typeCount))

/-- The local `.01n` bound for a usable heavy layer. -/
theorem four_r_le_100_mul_incidentViolationCount_of_usableHeavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hHeavy : HasHHO20HeavyChecks Delta baseSample twistSample)
    (u : ZMod ell)
    (hu : u ∈ usableHeavyLayerSet Delta twistSample w) :
    4 * r ≤
      100 * incidentViolationCount baseSample twistSample w u := by
  have hu' := mem_usableHeavyLayerSet_iff
    Delta twistSample w u |>.mp hu
  let types := twoSidedLightTypeSet Delta twistSample w u
  let outWord : Fin typeCount → Word (ZMod 2) (Fin (4 * r)) :=
    fun τ => layerWord w (outNeighbor twistSample τ u)
  let inWord : Fin typeCount → Word (ZMod 2) (Fin (4 * r)) :=
    fun τ => layerWord w (inNeighbor twistSample τ u)
  have hneighbors :
      ∀ τ ∈ types,
        Delta * HammingWeight (outWord τ) ≤ 2 * (4 * r) ∧
          Delta * HammingWeight (inWord τ) ≤ 2 * (4 * r) := by
    intro τ hτ
    have hτ' := mem_twoSidedLightTypeSet_iff
      Delta twistSample w u τ |>.mp hτ
    exact ⟨
      mem_lightLayerSet_iff Delta w
        (outNeighbor twistSample τ u) |>.mp hτ'.1,
      mem_lightLayerSet_iff Delta w
        (inNeighbor twistSample τ u) |>.mp hτ'.2⟩
  have hbase := hHeavy
    (layerWord w u) types outWord inWord
    (mem_heavyLayerSet_iff Delta w u |>.mp hu'.1)
    hu'.2 hneighbors
  have hsub :
      heavyIncidentViolationCount baseSample twistSample
          (layerWord w u) types outWord inWord ≤
        incidentViolationCount baseSample twistSample w u := by
    simp only [heavyIncidentViolationCount, incidentViolationCount,
      outWord, inWord, outgoingTypeViolationCount,
      incomingTypeViolationCount]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ types)
  exact hbase.trans (Nat.mul_le_mul_left 100 hsub)

/-- A layer word has at most `n = 4r` nonzero coordinates. -/
theorem hammingWeight_layerWord_le_four_r
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) :
    HammingWeight (layerWord w u) ≤ 4 * r := by
  unfold HammingWeight
  simpa using
    (Finset.card_le_card
      (Finset.subset_univ (hammingSupport (layerWord w u))))

/-- Sum of layer weights over a set is at most `n` times its cardinality. -/
theorem sum_hammingWeight_layerWord_le_card_mul_four_r
    {r ell : Nat}
    [NeZero ell]
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (layers : Finset (ZMod ell)) :
    (∑ u ∈ layers, HammingWeight (layerWord w u)) ≤
      layers.card * (4 * r) := by
  calc
    _ ≤ ∑ _u ∈ layers, 4 * r := by
      apply Finset.sum_le_sum
      intro u hu
      exact hammingWeight_layerWord_le_four_r w u
    _ = layers.card * (4 * r) := by simp

/-- Total word weight splits exactly across nonheavy and heavy layers. -/
theorem hammingWeight_eq_nonheavy_add_heavy
    {r ell : Nat}
    [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    HammingWeight w =
      (∑ u ∈ nonheavyLayerSet Delta w,
        HammingWeight (layerWord w u)) +
      (∑ u ∈ heavyLayerSet Delta w,
        HammingWeight (layerWord w u)) := by
  rw [hammingWeight_eq_sum_layerWord]
  rw [← nonheavyLayerSet_union_heavyLayerSet Delta w]
  exact Finset.sum_union
    (disjoint_nonheavyLayerSet_heavyLayerSet Delta w)

/-- Incident violations split exactly across nonheavy and heavy layers. -/
theorem sum_incidentViolationCount_eq_nonheavy_add_heavy
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    (∑ u : ZMod ell,
      incidentViolationCount baseSample twistSample w u) =
      (∑ u ∈ nonheavyLayerSet Delta w,
        incidentViolationCount baseSample twistSample w u) +
      (∑ u ∈ heavyLayerSet Delta w,
        incidentViolationCount baseSample twistSample w u) := by
  rw [← nonheavyLayerSet_union_heavyLayerSet Delta w]
  exact Finset.sum_union
    (disjoint_nonheavyLayerSet_heavyLayerSet Delta w)

/-- Medium layers contribute at least `2n / Delta` each. -/
theorem two_mul_four_r_mul_medium_card_le_nonheavy_weight
    {r ell : Nat}
    [NeZero r] [NeZero ell]
    (Delta : Nat)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r))) :
    2 * (4 * r) * (mediumLayerSet Delta w).card ≤
      Delta *
        (∑ u ∈ nonheavyLayerSet Delta w,
          HammingWeight (layerWord w u)) := by
  have hMN :
      mediumLayerSet Delta w ⊆ nonheavyLayerSet Delta w := by
    intro u hu
    exact (mem_nonheavyLayerSet_iff Delta w u).mpr
      ((mem_mediumLayerSet_iff Delta w u).mp hu).2
  calc
    2 * (4 * r) * (mediumLayerSet Delta w).card =
        ∑ _u ∈ mediumLayerSet Delta w, 2 * (4 * r) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ mediumLayerSet Delta w,
        Delta * HammingWeight (layerWord w u) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Nat.le_of_lt
        (mem_mediumLayerSet_iff Delta w u |>.mp hu).1
    _ = Delta *
        (∑ u ∈ mediumLayerSet Delta w,
          HammingWeight (layerWord w u)) := by
      rw [Finset.mul_sum]
    _ ≤ Delta *
        (∑ u ∈ nonheavyLayerSet Delta w,
          HammingWeight (layerWord w u)) := by
      exact Nat.mul_le_mul_left Delta
        (Finset.sum_le_sum_of_subset hMN)

/--
Aggregate form of HHO20 equation `ineq:mainsub`, with all decimals cleared:
`Delta * W_nonheavy ≤ 500 I_nonheavy + 5 n |H|`.
-/
theorem nonheavy_weight_le_incident_add_heavy_error
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hLight : HasHHO20LightChecks Delta baseSample twistSample)
    (hBad :
      4 * (badNonheavyLayerSet Delta twistSample w).card ≤
        5 * (heavyLayerSet Delta w).card) :
    Delta *
        (∑ u ∈ nonheavyLayerSet Delta w,
          HammingWeight (layerWord w u)) ≤
      500 *
          (∑ u ∈ nonheavyLayerSet Delta w,
            incidentViolationCount baseSample twistSample w u) +
        5 * (4 * r) * (heavyLayerSet Delta w).card := by
  let usable := usableNonheavyLayerSet Delta twistSample w
  let bad := badNonheavyLayerSet Delta twistSample w
  let nonheavy := nonheavyLayerSet Delta w
  have hUN : usable ⊆ nonheavy := by
    intro u hu
    exact (mem_usableNonheavyLayerSet_iff
      Delta twistSample w u |>.mp hu).1
  have hUB : Disjoint usable bad := by
    refine Finset.disjoint_left.mpr ?_
    intro u hu hbad
    exact (mem_badNonheavyLayerSet_iff
      Delta twistSample w u |>.mp hbad).2 hu
  have hUnion : usable ∪ bad = nonheavy := by
    exact Finset.union_sdiff_of_subset hUN
  have hUsable :
      Delta *
          (∑ u ∈ usable, HammingWeight (layerWord w u)) ≤
        500 *
          (∑ u ∈ nonheavy,
            incidentViolationCount baseSample twistSample w u) := by
    calc
      _ = ∑ u ∈ usable,
          Delta * HammingWeight (layerWord w u) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ u ∈ usable,
          500 * incidentViolationCount baseSample twistSample w u := by
        apply Finset.sum_le_sum
        intro u hu
        exact
          layerWeight_le_500_mul_incidentViolationCount_of_usableNonheavy
            Delta baseSample twistSample w hLight u hu
      _ = 500 *
          (∑ u ∈ usable,
            incidentViolationCount baseSample twistSample w u) := by
        rw [Finset.mul_sum]
      _ ≤ 500 *
          (∑ u ∈ nonheavy,
            incidentViolationCount baseSample twistSample w u) := by
        exact Nat.mul_le_mul_left 500
          (Finset.sum_le_sum_of_subset hUN)
  have hBadWeight :
      Delta * (∑ u ∈ bad, HammingWeight (layerWord w u)) ≤
        5 * (4 * r) * (heavyLayerSet Delta w).card := by
    calc
      _ = ∑ u ∈ bad,
          Delta * HammingWeight (layerWord w u) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _u ∈ bad, 4 * (4 * r) := by
        apply Finset.sum_le_sum
        intro u hu
        have hun := (mem_badNonheavyLayerSet_iff
          Delta twistSample w u |>.mp hu).1
        exact Nat.le_of_lt
          (mem_nonheavyLayerSet_iff Delta w u |>.mp hun)
      _ = bad.card * (4 * (4 * r)) := by simp
      _ = (4 * bad.card) * (4 * r) := by ring
      _ ≤ (5 * (heavyLayerSet Delta w).card) * (4 * r) :=
        Nat.mul_le_mul_right (4 * r) hBad
      _ = 5 * (4 * r) * (heavyLayerSet Delta w).card := by ring
  change
    Delta *
        (∑ u ∈ nonheavy, HammingWeight (layerWord w u)) ≤
      500 *
          (∑ u ∈ nonheavy,
            incidentViolationCount baseSample twistSample w u) +
        5 * (4 * r) * (heavyLayerSet Delta w).card
  have hWeightSplit :
      (∑ u ∈ nonheavy, HammingWeight (layerWord w u)) =
        (∑ u ∈ usable, HammingWeight (layerWord w u)) +
          ∑ u ∈ bad, HammingWeight (layerWord w u) := by
    rw [← hUnion, Finset.sum_union hUB]
  rw [hWeightSplit, Nat.mul_add]
  exact Nat.add_le_add hUsable hBadWeight

/-- Aggregate `.01n` payment from all usable heavy layers. -/
theorem four_r_mul_usableHeavy_card_le_heavy_incident
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (hHeavy : HasHHO20HeavyChecks Delta baseSample twistSample) :
    (4 * r) * (usableHeavyLayerSet Delta twistSample w).card ≤
      100 *
        (∑ u ∈ heavyLayerSet Delta w,
          incidentViolationCount baseSample twistSample w u) := by
  have hUH :
      usableHeavyLayerSet Delta twistSample w ⊆ heavyLayerSet Delta w := by
    intro u hu
    exact (mem_usableHeavyLayerSet_iff
      Delta twistSample w u |>.mp hu).1
  calc
    (4 * r) * (usableHeavyLayerSet Delta twistSample w).card =
        ∑ _u ∈ usableHeavyLayerSet Delta twistSample w, 4 * r := by
      simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ usableHeavyLayerSet Delta twistSample w,
        100 * incidentViolationCount baseSample twistSample w u := by
      apply Finset.sum_le_sum
      intro u hu
      exact four_r_le_100_mul_incidentViolationCount_of_usableHeavy
        Delta baseSample twistSample w hHeavy u hu
    _ = 100 *
        (∑ u ∈ usableHeavyLayerSet Delta twistSample w,
          incidentViolationCount baseSample twistSample w u) := by
      rw [Finset.mul_sum]
    _ ≤ 100 *
        (∑ u ∈ heavyLayerSet Delta w,
          incidentViolationCount baseSample twistSample w u) := by
      exact Nat.mul_le_mul_left 100
        (Finset.sum_le_sum_of_subset hUH)

/--
Deterministic HHO20 Theorem `thm:ltc`.

The partitioned light/heavy check events and the explicit layer-mixing
consequences imply the exact local-testability event used by the bundle
homology proof.  No probabilistic or matrix certificate is accepted here;
those internal events must subsequently be established for a sample selected
by the construction.
-/
theorem hasHHO20LocalTestability_of_partitionedChecks_and_layerMixing
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 40 ≤ Delta)
    (hChecks :
      HasHHO20PartitionedChecks Delta baseSample twistSample)
    (hMixing : HasHHO20LayerMixing Delta twistSample) :
    HasHHO20LocalTestability Delta baseSample twistSample := by
  intro w hsmall
  let nonheavyWeight :=
    ∑ u ∈ nonheavyLayerSet Delta w,
      HammingWeight (layerWord w u)
  let heavyWeight :=
    ∑ u ∈ heavyLayerSet Delta w,
      HammingWeight (layerWord w u)
  let nonheavyIncident :=
    ∑ u ∈ nonheavyLayerSet Delta w,
      incidentViolationCount baseSample twistSample w u
  let heavyIncident :=
    ∑ u ∈ heavyLayerSet Delta w,
      incidentViolationCount baseSample twistSample w u
  let heavyCount := (heavyLayerSet Delta w).card
  let mediumCount := (mediumLayerSet Delta w).card
  let usableHeavyCount :=
    (usableHeavyLayerSet Delta twistSample w).card
  let n := 4 * r
  let P := Delta * nonheavyWeight
  let Q := n * heavyCount
  have hWeight :
      HammingWeight w = nonheavyWeight + heavyWeight := by
    exact hammingWeight_eq_nonheavy_add_heavy Delta w
  have hIncident :
      nonheavyIncident + heavyIncident =
        2 * violationCount baseSample twistSample w := by
    calc
      _ = ∑ u : ZMod ell,
          incidentViolationCount baseSample twistSample w u := by
        symm
        exact sum_incidentViolationCount_eq_nonheavy_add_heavy
          Delta baseSample twistSample w
      _ = 2 * violationCount baseSample twistSample w :=
        sum_incidentViolationCount_eq_two_mul_violationCount
          baseSample twistSample w
  have hHeavyWeight : heavyWeight ≤ Q := by
    change
      (∑ u ∈ heavyLayerSet Delta w,
        HammingWeight (layerWord w u)) ≤
        (4 * r) * (heavyLayerSet Delta w).card
    calc
      _ ≤ (heavyLayerSet Delta w).card * (4 * r) :=
        sum_hammingWeight_layerWord_le_card_mul_four_r
          w (heavyLayerSet Delta w)
      _ = (4 * r) * (heavyLayerSet Delta w).card := by ring
  have hMedium :
      2 * n * mediumCount ≤ P := by
    exact two_mul_four_r_mul_medium_card_le_nonheavy_weight
      Delta w
  have hMix := hMixing w hsmall
  have hMain : P ≤ 500 * nonheavyIncident + 5 * Q := by
    simpa [P, Q, n, nonheavyWeight, nonheavyIncident, heavyCount,
      Nat.mul_assoc] using
      (nonheavy_weight_le_incident_add_heavy_error
        Delta baseSample twistSample w hChecks.1 hMix.1)
  have hFortyWeight : 40 * nonheavyWeight ≤ P := by
    change 40 * nonheavyWeight ≤ Delta * nonheavyWeight
    exact Nat.mul_le_mul_right nonheavyWeight hDelta
  have hEight :
      8 * (nonheavyWeight + heavyWeight) ≤
        1000 * (nonheavyIncident + heavyIncident) := by
    by_cases hHeavyCase : mediumCount < 1000 * heavyCount
    · have hGoodCount :
          9 * heavyCount ≤ 10 * usableHeavyCount :=
        hMix.2 hHeavyCase
      have hHeavyPay :
          n * usableHeavyCount ≤ 100 * heavyIncident := by
        exact four_r_mul_usableHeavy_card_le_heavy_incident
          Delta baseSample twistSample w hChecks.2
      have hNineQ : 9 * Q ≤ 1000 * heavyIncident := by
        calc
          9 * Q = n * (9 * heavyCount) := by ring
          _ ≤ n * (10 * usableHeavyCount) :=
            Nat.mul_le_mul_left n hGoodCount
          _ = 10 * (n * usableHeavyCount) := by ring
          _ ≤ 10 * (100 * heavyIncident) :=
            Nat.mul_le_mul_left 10 hHeavyPay
          _ = 1000 * heavyIncident := by ring
      have hFortyFiveQ :
          45 * Q ≤ 5000 * heavyIncident := by
        calc
          45 * Q = 5 * (9 * Q) := by ring
          _ ≤ 5 * (1000 * heavyIncident) :=
            Nat.mul_le_mul_left 5 hNineQ
          _ = 5000 * heavyIncident := by ring
      have hFortyHeavy : 40 * heavyWeight ≤ 40 * Q :=
        Nat.mul_le_mul_left 40 hHeavyWeight
      have hScaled :
          40 * (nonheavyWeight + heavyWeight) ≤
            5000 * (nonheavyIncident + heavyIncident) := by
        calc
          40 * (nonheavyWeight + heavyWeight) =
              40 * nonheavyWeight + 40 * heavyWeight := by ring
          _ ≤ P + 40 * Q :=
            Nat.add_le_add hFortyWeight hFortyHeavy
          _ ≤ (500 * nonheavyIncident + 5 * Q) + 40 * Q :=
            Nat.add_le_add_right hMain (40 * Q)
          _ = 500 * nonheavyIncident + 45 * Q := by ring
          _ ≤ 500 * nonheavyIncident + 5000 * heavyIncident :=
            Nat.add_le_add_left hFortyFiveQ (500 * nonheavyIncident)
          _ ≤ 5000 * nonheavyIncident + 5000 * heavyIncident := by
            omega
          _ = 5000 * (nonheavyIncident + heavyIncident) := by ring
      have hmul :
          5 * (8 * (nonheavyWeight + heavyWeight)) ≤
            5 * (1000 * (nonheavyIncident + heavyIncident)) := by
        convert hScaled using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
    · have hLightCase : 1000 * heavyCount ≤ mediumCount := by
        omega
      have hTwoThousandQ : 2000 * Q ≤ P := by
        calc
          2000 * Q = 2 * n * (1000 * heavyCount) := by ring
          _ ≤ 2 * n * mediumCount :=
            Nat.mul_le_mul_left (2 * n) hLightCase
          _ ≤ P := hMedium
      have hTenQ : 10 * Q ≤ P := by
        calc
          10 * Q ≤ 2000 * Q :=
            Nat.mul_le_mul_right Q (by omega)
          _ ≤ P := hTwoThousandQ
      have hP : P ≤ 1000 * nonheavyIncident := by
        omega
      have hThreeTwentyNonheavy :
          320 * nonheavyWeight ≤ 8 * P := by
        calc
          320 * nonheavyWeight = 8 * (40 * nonheavyWeight) := by
            ring
          _ ≤ 8 * P := Nat.mul_le_mul_left 8 hFortyWeight
      have hThreeTwentyHeavy :
          320 * heavyWeight ≤ P := by
        calc
          320 * heavyWeight ≤ 2000 * heavyWeight :=
            Nat.mul_le_mul_right heavyWeight (by omega)
          _ ≤ 2000 * Q :=
            Nat.mul_le_mul_left 2000 hHeavyWeight
          _ ≤ P := hTwoThousandQ
      have hScaled :
          320 * (nonheavyWeight + heavyWeight) ≤
            40000 * (nonheavyIncident + heavyIncident) := by
        calc
          320 * (nonheavyWeight + heavyWeight) =
              320 * nonheavyWeight + 320 * heavyWeight := by ring
          _ ≤ 8 * P + P :=
            Nat.add_le_add hThreeTwentyNonheavy hThreeTwentyHeavy
          _ = 9 * P := by ring
          _ ≤ 9 * (1000 * nonheavyIncident) :=
            Nat.mul_le_mul_left 9 hP
          _ = 9000 * nonheavyIncident := by ring
          _ ≤ 40000 * (nonheavyIncident + heavyIncident) := by
            omega
      have hmul :
          40 * (8 * (nonheavyWeight + heavyWeight)) ≤
            40 * (1000 * (nonheavyIncident + heavyIncident)) := by
        convert hScaled using 1 <;> ring
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
  rw [hWeight]
  have hmul :
      8 * (nonheavyWeight + heavyWeight) ≤
        8 * (250 * violationCount baseSample twistSample w) := by
    calc
      8 * (nonheavyWeight + heavyWeight) ≤
          1000 * (nonheavyIncident + heavyIncident) := hEight
      _ = 1000 *
          (2 * violationCount baseSample twistSample w) := by
        rw [hIncident]
      _ = 8 *
          (250 * violationCount baseSample twistSample w) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

end QEC.Coding.FiberBundle.TwistGraph

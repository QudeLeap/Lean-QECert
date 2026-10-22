import QEC.Coding.QuantumTanner.CayleyLink
import QEC.Coding.QuantumTanner.NormalViews
import QEC.Coding.QuantumTanner.ViewAssembly
import QEC.Coding.ExpanderCodes.MixingDegree

/-!
# Heavy Cayley edges and their opposite vertices

Keep multiplicities of left and right generator labels. A heavy shared
row/column forces many actual neighbors in the support set on the other
side. These are the finite incidence facts behind [LZ22, Claim claim:degreeT].
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open Classical QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- The weighted union of the actual left/right Cayley edges. The Boolean
side is omitted from the vertex type; each edge changes that side. -/
def unionCayleyGraph (X : LeftRightCayleySquareComplex G A B Square) : WeightedGraph G :=
  fun g h => (Finset.univ.filter fun a => X.leftGenerator a * g = h).card +
    (Finset.univ.filter fun b => g * X.rightGenerator b = h).card

/-- Count generator labels entering a vertex set, without discarding multiplicity. -/
theorem sum_unionCayleyGraph_eq_labels
    (X : LeftRightCayleySquareComplex G A B Square) (g : G) (T : Finset G) :
    (∑ h ∈ T, X.unionCayleyGraph g h) =
      (Finset.univ.filter fun a => X.leftGenerator a * g ∈ T).card +
      (Finset.univ.filter fun b => g * X.rightGenerator b ∈ T).card := by
  simp only [unionCayleyGraph, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·)
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ T (fun a => X.leftGenerator a * g))
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ T (fun b => g * X.rightGenerator b))

/-- The union has the sum of the local generator degrees. -/
theorem unionCayleyGraph_regular (X : LeftRightCayleySquareComplex G A B Square) :
    IsRegular X.unionCayleyGraph (Fintype.card A + Fintype.card B) := by
  intro g
  rw [X.sum_unionCayleyGraph_eq_labels]
  simp

/-- Inverse generator labels reverse the actual weighted edges. -/
theorem unionCayleyGraph_symmetric
    (X : LeftRightCayleySquareComplex G A B Square) (g h : G) :
    X.unionCayleyGraph g h = X.unionCayleyGraph h g := by
  simp only [unionCayleyGraph, Finset.card_filter]
  congr 1
  · apply Fintype.sum_equiv X.leftInverse
    intro a
    have hi : X.leftGenerator (X.leftInverse a) * h = g ↔
        X.leftGenerator a * g = h := by
      rw [X.leftGenerator_inverse]
      exact eq_comm.trans eq_inv_mul_iff_mul_eq
    simp only [hi]
  · apply Fintype.sum_equiv X.rightInverse
    intro b
    have hi : h * X.rightGenerator (X.rightInverse b) = g ↔
        g * X.rightGenerator b = h := by
      rw [X.rightGenerator_inverse]
      exact eq_comm.trans eq_mul_inv_iff_mul_eq
    simp only [hi]

/-- Every target receives one edge per generator label, counting multiplicities. -/
theorem unionCayleyGraph_incoming_regular
    (X : LeftRightCayleySquareComplex G A B Square) (h : G) :
    (∑ g : G, X.unionCayleyGraph g h) = Fintype.card A + Fintype.card B := by
  have hLeft (a : A) : (∑ g : G, if X.leftGenerator a * g = h then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    have hSet : (Finset.univ.filter fun g => X.leftGenerator a * g = h) =
        {((X.leftGenerator a)⁻¹ * h)} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_inv_mul_iff_mul_eq.symm
    rw [hSet]
    simp
  have hRight (b : B) : (∑ g : G, if g * X.rightGenerator b = h then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    have hSet : (Finset.univ.filter fun g => g * X.rightGenerator b = h) =
        {h * (X.rightGenerator b)⁻¹} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_mul_inv_iff_mul_eq.symm
    rw [hSet]
    simp
  simp only [unionCayleyGraph, Finset.sum_add_distrib, Finset.card_filter]
  rw [Finset.sum_comm (f := fun g a => if X.leftGenerator a * g = h then 1 else 0),
    Finset.sum_comm (f := fun g b => if g * X.rightGenerator b = h then 1 else 0)]
  simp only [hLeft, hRight, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

/-- The cross count cannot exceed the full incoming degree at its right set. -/
theorem crossCount_unionCayleyGraph_le_degree_card_right
    (X : LeftRightCayleySquareComplex G A B Square) (S T : Finset G) :
    crossCount X.unionCayleyGraph S T ≤
      (Fintype.card A + Fintype.card B) * T.card := by
  unfold crossCount
  rw [Finset.sum_comm]
  calc
    (∑ h ∈ T, ∑ g ∈ S, X.unionCayleyGraph g h) ≤
        ∑ h ∈ T, ∑ g : G, X.unionCayleyGraph g h := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro g hg hNot
      exact Nat.zero_le _
    _ = (Fintype.card A + Fintype.card B) * T.card := by
      simp [X.unionCayleyGraph_incoming_regular, Nat.mul_comm]

/-- Each nonzero link entry has an actually active left neighbor. -/
theorem left_neighbor_mem_active_of_entry_ne_zero
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) (b : B)
    (hEntry : X.localRestriction (g, side) x (a, b) ≠ 0) :
    X.leftGenerator a * g ∈ X.activeVerticesOnSide (!side) x := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hZero
  apply hEntry
  change x (X.link (g, side) (a, b)) = 0
  rw [hX.1 g side a b]
  exact congrFun hZero (X.leftInverse a, b)

/-- Each nonzero link entry has an actually active right neighbor. -/
theorem right_neighbor_mem_active_of_entry_ne_zero
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) (b : B)
    (hEntry : X.localRestriction (g, side) x (a, b) ≠ 0) :
    g * X.rightGenerator b ∈ X.activeVerticesOnSide (!side) x := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hZero
  apply hEntry
  change x (X.link (g, side) (a, b)) = 0
  rw [hX.2 g side a b]
  exact congrFun hZero (a, X.rightInverse b)

/-- Nonzero entries in one row supply that many right-edge labels into the
actual opposite-side support. No simple-graph assumption is required. -/
theorem rowWeight_le_unionDegree_active
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (a : A) :
    HammingWeight (rowRestriction a (X.localRestriction (g, side) x)) ≤
      ∑ h ∈ X.activeVerticesOnSide (!side) x, X.unionCayleyGraph g h := by
  rw [X.sum_unionCayleyGraph_eq_labels]
  have hSubset : hammingSupport (rowRestriction a (X.localRestriction (g, side) x)) ⊆
      Finset.univ.filter (fun b => g * X.rightGenerator b ∈
        X.activeVerticesOnSide (!side) x) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      X.right_neighbor_mem_active_of_entry_ne_zero hX x g side a b
        (Finset.mem_filter.mp hb).2⟩
  exact (Finset.card_le_card hSubset).trans (Nat.le_add_left _ _)

/-- The corresponding column count uses left-edge labels. -/
theorem columnWeight_le_unionDegree_active
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (x : Word (ZMod 2) Square) (g : G) (side : Bool) (b : B) :
    HammingWeight (columnRestriction b (X.localRestriction (g, side) x)) ≤
      ∑ h ∈ X.activeVerticesOnSide (!side) x, X.unionCayleyGraph g h := by
  rw [X.sum_unionCayleyGraph_eq_labels]
  have hSubset : hammingSupport (columnRestriction b (X.localRestriction (g, side) x)) ⊆
      Finset.univ.filter (fun a => X.leftGenerator a * g ∈
        X.activeVerticesOnSide (!side) x) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      X.left_neighbor_mem_active_of_entry_ne_zero hX x g side a b
        (Finset.mem_filter.mp ha).2⟩
  exact (Finset.card_le_card hSubset).trans (Nat.le_add_right _ _)

/-- Keep precisely the generator labels whose shared line reaches `cutoff`. -/
def heavyUnionGraph (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) : WeightedGraph G := fun g h =>
  (Finset.univ.filter fun a => X.leftGenerator a * g = h ∧
    cutoff ≤ HammingWeight (rowRestriction a (X.localRestriction (g, side) x))).card +
  (Finset.univ.filter fun b => g * X.rightGenerator b = h ∧
    cutoff ≤ HammingWeight (columnRestriction b (X.localRestriction (g, side) x))).card

/-- Reversing a realized Cayley edge preserves its shared-line weight. -/
theorem heavyUnionGraph_reverse
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (g h : G) :
    X.heavyUnionGraph side x cutoff g h = X.heavyUnionGraph (!side) x cutoff h g := by
  simp only [heavyUnionGraph, Finset.card_filter]
  congr 1
  · apply Fintype.sum_equiv X.leftInverse
    intro a
    have hEdge : X.leftGenerator (X.leftInverse a) * h = g ↔
        X.leftGenerator a * g = h := by
      rw [X.leftGenerator_inverse]
      exact eq_comm.trans eq_inv_mul_iff_mul_eq
    have hIff : (X.leftGenerator a * g = h ∧ cutoff ≤
        HammingWeight (rowRestriction a (X.localRestriction (g, side) x))) ↔
        (X.leftGenerator (X.leftInverse a) * h = g ∧ cutoff ≤
        HammingWeight (rowRestriction (X.leftInverse a) (X.localRestriction (h, !side) x))) := by
      constructor
      · rintro ⟨he, hw⟩
        refine ⟨hEdge.mpr he, ?_⟩
        have ht := X.rowRestriction_localRestriction_rebase_left hX x g side a
        rw [he] at ht
        rwa [← ht]
      · rintro ⟨he, hw⟩
        have he' := hEdge.mp he
        refine ⟨he', ?_⟩
        have ht := X.rowRestriction_localRestriction_rebase_left hX x g side a
        rw [he'] at ht
        rwa [ht]
    simp only [hIff]
  · apply Fintype.sum_equiv X.rightInverse
    intro b
    have hEdge : h * X.rightGenerator (X.rightInverse b) = g ↔
        g * X.rightGenerator b = h := by
      rw [X.rightGenerator_inverse]
      exact eq_comm.trans eq_mul_inv_iff_mul_eq
    have hIff : (g * X.rightGenerator b = h ∧ cutoff ≤
        HammingWeight (columnRestriction b (X.localRestriction (g, side) x))) ↔
        (h * X.rightGenerator (X.rightInverse b) = g ∧ cutoff ≤
        HammingWeight (columnRestriction (X.rightInverse b) (X.localRestriction (h, !side) x))) := by
      constructor
      · rintro ⟨he, hw⟩
        refine ⟨hEdge.mpr he, ?_⟩
        have ht := X.columnRestriction_localRestriction_rebase_right hX x g side b
        rw [he] at ht
        rwa [← ht]
      · rintro ⟨he, hw⟩
        have he' := hEdge.mp he
        refine ⟨he', ?_⟩
        have ht := X.columnRestriction_localRestriction_rebase_right hX x g side b
        rw [he'] at ht
        rwa [ht]
    simp only [hIff]

/-- The total heavy degree counts precisely the heavy row and column labels. -/
theorem sum_heavyUnionGraph_eq_labels
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (g : G) :
    (∑ h : G, X.heavyUnionGraph side x cutoff g h) =
      (Finset.univ.filter fun a => cutoff ≤
        HammingWeight (rowRestriction a (X.localRestriction (g, side) x))).card +
      (Finset.univ.filter fun b => cutoff ≤
        HammingWeight (columnRestriction b (X.localRestriction (g, side) x))).card := by
  have hLeft (a : A) :
      (∑ h : G, if X.leftGenerator a * g = h ∧ cutoff ≤
        HammingWeight (rowRestriction a (X.localRestriction (g, side) x)) then 1 else 0) =
      if cutoff ≤ HammingWeight (rowRestriction a (X.localRestriction (g, side) x))
        then 1 else 0 := by
    by_cases hw : cutoff ≤ HammingWeight (rowRestriction a (X.localRestriction (g, side) x))
    · simp only [hw, and_true, ite_true]
      simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp only [hw, and_false, ite_false, Finset.sum_const_zero]
  have hRight (b : B) :
      (∑ h : G, if g * X.rightGenerator b = h ∧ cutoff ≤
        HammingWeight (columnRestriction b (X.localRestriction (g, side) x)) then 1 else 0) =
      if cutoff ≤ HammingWeight (columnRestriction b (X.localRestriction (g, side) x))
        then 1 else 0 := by
    by_cases hw : cutoff ≤ HammingWeight (columnRestriction b (X.localRestriction (g, side) x))
    · simp only [hw, and_true, ite_true]
      simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp only [hw, and_false, ite_false, Finset.sum_const_zero]
  simp only [heavyUnionGraph, Finset.card_filter, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun h a => if X.leftGenerator a * g = h ∧ cutoff ≤
      HammingWeight (rowRestriction a (X.localRestriction (g, side) x)) then 1 else 0),
    Finset.sum_comm (f := fun h b => if g * X.rightGenerator b = h ∧ cutoff ≤
      HammingWeight (columnRestriction b (X.localRestriction (g, side) x)) then 1 else 0)]
  simp only [hLeft, hRight]

/-- Heavy incidences at a vertex are paid for by twice its actual local weight. -/
theorem cutoff_mul_heavyDegree_le_twice_localWeight
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (g : G) :
    cutoff * (∑ h : G, X.heavyUnionGraph side x cutoff g h) ≤
      2 * HammingWeight (X.localRestriction (g, side) x) := by
  have hCount {ι : Type v} [Fintype ι] (weight : ι → Nat) :
      cutoff * (Finset.univ.filter fun i => cutoff ≤ weight i).card ≤ ∑ i, weight i := by
    calc
      cutoff * (Finset.univ.filter fun i => cutoff ≤ weight i).card =
          ∑ _i ∈ Finset.univ.filter (fun i => cutoff ≤ weight i), cutoff := by
        simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => cutoff ≤ weight i), weight i :=
        Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
      _ ≤ ∑ i, weight i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i hi hNot
        exact Nat.zero_le _
  rw [X.sum_heavyUnionGraph_eq_labels, Nat.mul_add]
  have hRow := hCount (fun a => HammingWeight (rowRestriction a (X.localRestriction (g, side) x)))
  have hColumn := hCount (fun b => HammingWeight (columnRestriction b (X.localRestriction (g, side) x)))
  rw [← hammingWeight_matrix_eq_sum_rows] at hRow
  rw [← hammingWeight_matrix_eq_sum_columns] at hColumn
  omega

/-- The incoming heavy edges from any selected set give the same weight lower
bound after actual link rebasing. -/
theorem cutoff_mul_incoming_heavyDegree_le_twice_localWeight
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) (h : G) :
    cutoff * (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
      2 * HammingWeight (X.localRestriction (h, !side) x) := by
  have hDegree : (∑ g ∈ normal, X.heavyUnionGraph side x cutoff g h) ≤
      ∑ g : G, X.heavyUnionGraph (!side) x cutoff h g := by
    simp_rw [X.heavyUnionGraph_reverse hX side x cutoff]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ normal)
    intro g hg hNot
    exact Nat.zero_le _
  exact (Nat.mul_le_mul_left cutoff hDegree).trans
    (X.cutoff_mul_heavyDegree_le_twice_localWeight (!side) x cutoff h)

theorem heavyUnionGraph_le_unionCayleyGraph
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) (g h : G) :
    X.heavyUnionGraph side x cutoff g h ≤ X.unionCayleyGraph g h := by
  apply Nat.add_le_add
  · apply Finset.card_le_card
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.1⟩
  · apply Finset.card_le_card
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩

/-- Opposite vertices joined to a selected normal set by a heavy edge. -/
def oppositeHeavySet (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) : Finset G :=
  Finset.univ.filter fun h => ∃ g ∈ normal, X.heavyUnionGraph side x cutoff g h ≠ 0

/-- A vertex reached by a heavy edge has the source's claimed support degree. -/
theorem oppositeHeavySet_degree_lower
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (h : G) (hh : h ∈ X.oppositeHeavySet side x cutoff normal) :
    cutoff ≤ ∑ g ∈ X.activeVerticesOnSide side x, X.unionCayleyGraph h g := by
  obtain ⟨g, hg, hHeavy⟩ := (Finset.mem_filter.mp hh).2
  have hPos : 0 < X.heavyUnionGraph side x cutoff g h := Nat.pos_of_ne_zero hHeavy
  change 0 < _ + _ at hPos
  rcases Nat.add_pos_iff_pos_or_pos.mp hPos with hLeft | hRight
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp hLeft
    obtain ⟨hNeighbor, hWeight⟩ := (Finset.mem_filter.mp ha).2
    have hTransport := X.rowRestriction_localRestriction_rebase_left hX x g side a
    rw [hNeighbor] at hTransport
    rw [hTransport] at hWeight
    have hDegree := X.rowWeight_le_unionDegree_active hX x h (!side) (X.leftInverse a)
    simpa only [Bool.not_not] using hWeight.trans hDegree
  · obtain ⟨b, hb⟩ := Finset.card_pos.mp hRight
    obtain ⟨hNeighbor, hWeight⟩ := (Finset.mem_filter.mp hb).2
    have hTransport := X.columnRestriction_localRestriction_rebase_right hX x g side b
    rw [hNeighbor] at hTransport
    rw [hTransport] at hWeight
    have hDegree := X.columnWeight_le_unionDegree_active hX x h (!side) (X.rightInverse b)
    simpa only [Bool.not_not] using hWeight.trans hDegree

/-- Sum the genuine support degrees over the actual opposite heavy set. -/
theorem cutoff_mul_oppositeHeavySet_card_le_crossCount
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) :
    cutoff * (X.oppositeHeavySet side x cutoff normal).card ≤
      crossCount X.unionCayleyGraph (X.oppositeHeavySet side x cutoff normal)
        (X.activeVerticesOnSide side x) := by
  apply degree_mul_card_le_crossCount
  exact X.oppositeHeavySet_degree_lower hX side x cutoff normal

/-- Every vertex with a heavy line contributes an actual edge into the
opposite heavy set, so the normal set is counted by heavy incidences. -/
theorem normal_card_le_heavy_crossCount
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (hHeavy : ∀ g ∈ normal,
      (∃ a, cutoff ≤ HammingWeight (rowRestriction a (X.localRestriction (g, side) x))) ∨
        ∃ b, cutoff ≤ HammingWeight (columnRestriction b (X.localRestriction (g, side) x))) :
    normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal) := by
  have hDegree : ∀ g ∈ normal, 1 ≤
      ∑ h ∈ X.oppositeHeavySet side x cutoff normal, X.heavyUnionGraph side x cutoff g h := by
    intro g hg
    have hEdge : ∃ h, 0 < X.heavyUnionGraph side x cutoff g h := by
      rcases hHeavy g hg with ⟨a, ha⟩ | ⟨b, hb⟩
      · refine ⟨X.leftGenerator a * g, ?_⟩
        have hPos : 0 < (Finset.univ.filter fun a' => X.leftGenerator a' * g =
            X.leftGenerator a * g ∧ cutoff ≤
              HammingWeight (rowRestriction a' (X.localRestriction (g, side) x))).card :=
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ha⟩⟩
        exact hPos.trans_le (Nat.le_add_right _ _)
      · refine ⟨g * X.rightGenerator b, ?_⟩
        have hPos : 0 < (Finset.univ.filter fun b' => g * X.rightGenerator b' =
            g * X.rightGenerator b ∧ cutoff ≤
              HammingWeight (columnRestriction b' (X.localRestriction (g, side) x))).card :=
          Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hb⟩⟩
        exact hPos.trans_le (Nat.le_add_left _ _)
    obtain ⟨h, hh⟩ := hEdge
    have hMem : h ∈ X.oppositeHeavySet side x cutoff normal :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg, Nat.ne_of_gt hh⟩
    exact hh.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hMem)
  simpa using degree_mul_card_le_crossCount (X.heavyUnionGraph side x cutoff) normal
    (X.oppositeHeavySet side x cutoff normal) 1 hDegree

/-- Actual small covers force a heavy line at every normal active vertex. -/
theorem normal_card_le_heavy_crossCount_of_covers
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (dA dB : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA) (hB : HasMinimumDistanceAtLeast CB dB)
    (hNormal : normal ⊆ X.activeVerticesOnSide side x)
    (hCovers : ∀ g ∈ normal, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      cutoff + columns.card ≤ dB ∧ cutoff + rows.card ≤ dA) :
    normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal) := by
  apply X.normal_card_le_heavy_crossCount side x cutoff normal
  intro g hg
  obtain ⟨rows, columns, hLocal, hCovered, hRows, hColumns, hCutoffRow, hCutoffColumn⟩ :=
    hCovers g hg
  exact exists_heavy_line_of_cover CA CB dA dB cutoff hA hB
    (X.localRestriction (g, side) x) hLocal (Finset.mem_filter.mp (hNormal hg)).2
    rows columns hRows hColumns hCovered hCutoffRow hCutoffColumn

/-- The actual opposite set obeys the finite high-degree mixing bound. -/
theorem oppositeHeavySet_card_bound_of_density_gap
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (spectral gap : ℝ) (hSpectral : 0 ≤ spectral) (hGap : 0 < gap)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) spectral)
    (hDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
        (X.activeVerticesOnSide side x).card + gap * Fintype.card G ≤
      (cutoff : ℝ) * Fintype.card G) :
    gap ^ 2 * (X.oppositeHeavySet side x cutoff normal).card ≤
      spectral ^ 2 * (X.activeVerticesOnSide side x).card := by
  apply highDegree_card_bound_of_density_gap X.unionCayleyGraph
    (Fintype.card A + Fintype.card B) spectral cutoff gap hSpectral hGap hMixing
    (X.oppositeHeavySet side x cutoff normal) (X.activeVerticesOnSide side x)
  · exact_mod_cast X.cutoff_mul_oppositeHeavySet_card_le_crossCount hX side x cutoff normal
  · exact hDensity

/-- The `64/(delta^2 Delta)` constant in [LZ22, equation eqn:T], after
the uniform-density term is absorbed into the explicit half-distance gap. -/
theorem oppositeHeavySet_card_bound_source
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (Delta : Nat) (hDelta : 0 < Delta) (delta : ℝ) (hDeltaDistance : 0 < delta)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) (4 * Real.sqrt Delta))
    (hDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
        (X.activeVerticesOnSide side x).card +
        (delta * Delta / 2) * Fintype.card G ≤ (cutoff : ℝ) * Fintype.card G) :
    (X.oppositeHeavySet side x cutoff normal).card ≤
      64 / (delta ^ 2 * Delta) * (X.activeVerticesOnSide side x).card := by
  have hd : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hGap : 0 < delta * Delta / 2 := by positivity
  have h := X.oppositeHeavySet_card_bound_of_density_gap hX side x cutoff normal
    (4 * Real.sqrt Delta) (delta * Delta / 2) (by positivity) hGap hMixing hDensity
  have hRoot : (Real.sqrt (Delta : ℝ)) ^ 2 = Delta := Real.sq_sqrt hd.le
  have hScaled : (Delta : ℝ) *
      (delta ^ 2 * Delta * (X.oppositeHeavySet side x cutoff normal).card) ≤
      (Delta : ℝ) * (64 * (X.activeVerticesOnSide side x).card) := by
    nlinarith
  have hCancel := le_of_mul_le_mul_left hScaled hd
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hDeltaDistance) hd)).mpr
  nlinarith

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

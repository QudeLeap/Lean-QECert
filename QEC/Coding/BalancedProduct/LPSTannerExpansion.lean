import QEC.Coding.BalancedProduct.LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Spectral expansion of the concrete BE20 LPS Tanner boundary

This module performs the support-graph double counting that connects the
graph-only `LPS401RayleighBound` to the primal and transpose Tanner maps.
No expansion, distance, or syndrome conclusion is accepted as input data.
-/

noncomputable section

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSTannerExpansion

open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus

/-- The spanning simple graph consisting exactly of the LPS edges on which
the edge word is nonzero. -/
def wordSupportGraph
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : SimpleGraph (Vertex401 q) where
  Adj g w := ∃ e : Edge401 q hq, e.1 = s(g, w) ∧ x e ≠ 0
  symm := by
    constructor
    rintro g w ⟨e, he, hx⟩
    refine ⟨e, ?_, hx⟩
    simpa only [Sym2.eq_swap] using he
  loopless := ⟨by
    rintro g ⟨e, he, _hx⟩
    have hadj : (lpsCayleyGraph401 q hq).Adj g g := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [he] using e.2
    exact (lpsCayleyGraph401 q hq).loopless.irrefl g hadj⟩

theorem wordSupportGraph_le_lps
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    wordSupportGraph q hq x ≤ lpsCayleyGraph401 q hq := by
  intro g w hgw
  rcases hgw with ⟨e, he, _hx⟩
  rw [← SimpleGraph.mem_edgeSet]
  simpa [he] using e.2

theorem mem_wordSupportGraph_edgeSet_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (a : Sym2 (Vertex401 q)) :
    a ∈ (wordSupportGraph q hq x).edgeSet ↔
      ∃ e : Edge401 q hq, e.1 = a ∧ x e ≠ 0 := by
  refine Sym2.inductionOn a ?_
  intro g w
  rw [SimpleGraph.mem_edgeSet]
  rfl

/-- The support edges of the spanning support graph are the nonzero global
edge coordinates, including proof-irrelevant subtype identification. -/
def supportEdgeEquiv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (wordSupportGraph q hq x).edgeSet ≃
      {e : Edge401 q hq // x e ≠ 0} where
  toFun e := by
    let a : Edge401 q hq :=
      ⟨e.1, SimpleGraph.edgeSet_mono (wordSupportGraph_le_lps q hq x) e.2⟩
    refine ⟨a, ?_⟩
    rcases (mem_wordSupportGraph_edgeSet_iff q hq x e.1).1 e.2 with
      ⟨b, hb, hxb⟩
    have hba : b = a := by
      apply Subtype.ext
      exact hb
    simpa [hba] using hxb
  invFun e := by
    refine ⟨e.1.1, ?_⟩
    exact (mem_wordSupportGraph_edgeSet_iff q hq x e.1.1).2
      ⟨e.1, rfl, e.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem card_wordSupportGraph_edges
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    Fintype.card (wordSupportGraph q hq x).edgeSet = HammingWeight x := by
  rw [Fintype.card_congr (supportEdgeEquiv q hq x)]
  simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- Reindexing the supported local coordinates at a vertex by the actual
incidence labelling gives precisely the neighbor set of the word-support
graph. -/
def localSupportEquivNeighborSet
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    {a : LocalCoordinate // localView q hq40 hq g x a ≠ 0} ≃
      (wordSupportGraph q hq x).neighborSet g := by
  let G := lpsCayleyGraph401 q hq
  let Λ := incidentCoordinateEquiv q hq40 hq g
  let E : LocalCoordinate ≃ G.neighborSet g :=
    Λ.symm.trans (G.incidenceSetEquivNeighborSet g)
  have hpred (a : LocalCoordinate) :
      localView q hq40 hq g x a ≠ 0 ↔
        (wordSupportGraph q hq x).Adj g (E a).1 := by
    let i := Λ.symm a
    have hi : i.1 = s(g, (G.incidenceSetEquivNeighborSet g i).1) := by
      have h := (G.incidenceSetEquivNeighborSet g).symm_apply_apply i
      exact (congrArg Subtype.val h).symm
    constructor
    · intro hx
      refine ⟨incidentAsEdge q hq i, hi, ?_⟩
      exact hx
    · rintro ⟨e, he, hxe⟩
      have hei : e = incidentAsEdge q hq i := by
        apply Subtype.ext
        exact he.trans hi.symm
      simpa [localView, E, i, Λ, hei] using hxe
  let e₁ :
      {a : LocalCoordinate // localView q hq40 hq g x a ≠ 0} ≃
        {w : G.neighborSet g //
          (wordSupportGraph q hq x).Adj g w.1} :=
    E.subtypeEquiv hpred
  let e₂ :
      {w : G.neighborSet g // (wordSupportGraph q hq x).Adj g w.1} ≃
        (wordSupportGraph q hq x).neighborSet g :=
    { toFun := fun w => ⟨w.1.1, w.2⟩
      invFun := fun w =>
        ⟨⟨w.1, (wordSupportGraph_le_lps q hq x) w.2⟩, w.2⟩
      left_inv := fun w => by ext; rfl
      right_inv := fun w => by ext; rfl }
  exact e₁.trans e₂

theorem localView_weight_eq_support_degree
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    HammingWeight (localView q hq40 hq g x) =
      (wordSupportGraph q hq x).degree g := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [← Fintype.card_congr (localSupportEquivNeighborSet q hq40 hq x g)]
  simp [HammingWeight, hammingSupport, Fintype.card_subtype]

/-- Exact handshake identity for the support of an edge word. -/
theorem sum_localView_weight_eq_twice_globalWeight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (∑ g, HammingWeight (localView q hq40 hq g x)) =
      2 * HammingWeight x := by
  simp_rw [localView_weight_eq_support_degree q hq40 hq x]
  rw [(wordSupportGraph q hq x).sum_degrees_eq_twice_card_edges]
  rw [SimpleGraph.edgeFinset_card, card_wordSupportGraph_edges q hq x]

/-- Every concrete LPS vertex has degree exactly 402. -/
theorem lpsCayleyGraph401_degree
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) :
    (lpsCayleyGraph401 q hq).degree g = 402 := by
  change ((lpsCayleyGraph401 q hq).neighborFinset g).card = 402
  rw [← LPSGraph.card_lpsNeighbors401 q hq40 hq g]
  apply congrArg Finset.card
  ext w
  simp [LPSGraph.mem_lpsNeighbors401_iff_adj]

/-- Correct edge/vertex handshake normalization for the 402-regular LPS
graph: `|X₁| = 201 |X₀|`. -/
theorem card_edge401_eq
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (Edge401 q hq) =
      201 * Fintype.card (Vertex401 q) := by
  have hsum :
      2 * Fintype.card (Edge401 q hq) =
        402 * Fintype.card (Vertex401 q) := by
    calc
      2 * Fintype.card (Edge401 q hq) =
          2 * (lpsCayleyGraph401 q hq).edgeFinset.card := by
        rw [SimpleGraph.edgeFinset_card]
      _ = ∑ g, (lpsCayleyGraph401 q hq).degree g :=
        (lpsCayleyGraph401 q hq).sum_degrees_eq_twice_card_edges.symm
      _ = ∑ _g : Vertex401 q, 402 := by
        apply Finset.sum_congr rfl
        intro g _hg
        rw [lpsCayleyGraph401_degree q hq40 hq g]
      _ = 402 * Fintype.card (Vertex401 q) := by
        simp [Nat.mul_comm]
  omega

/-- Vertices incident to at least one supported edge. -/
def primalSupportVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : Finset (Vertex401 q) :=
  Finset.univ.filter fun g => localView q hq40 hq g x ≠ 0

theorem mem_primalSupportVertices_iff
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    g ∈ primalSupportVertices q hq40 hq x ↔
      localView q hq40 hq g x ≠ 0 := by
  simp [primalSupportVertices]

theorem card_primalSupportVertices_le_twice_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (primalSupportVertices q hq40 hq x).card ≤
      2 * HammingWeight x := by
  let S := primalSupportVertices q hq40 hq x
  calc
    S.card = ∑ _g ∈ S, 1 := by simp
    _ ≤ ∑ g ∈ S, HammingWeight (localView q hq40 hq g x) := by
      apply Finset.sum_le_sum
      intro g hg
      exact Nat.one_le_iff_ne_zero.2 <|
        (HammingWeight_eq_zero_iff _).not.mpr <|
          (mem_primalSupportVertices_iff q hq40 hq x g).1 hg
    _ ≤ ∑ g, HammingWeight (localView q hq40 hq g x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro g _hg _hgS
      omega
    _ = 2 * HammingWeight x :=
      sum_localView_weight_eq_twice_globalWeight q hq40 hq x

/-- Every supported edge contributes both oriented incidences inside the set
of vertices incident to the edge support. -/
theorem twice_weight_le_insideAdjacency_primalSupport
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    2 * HammingWeight x ≤
      insideAdjacencyCount401 q hq
        (primalSupportVertices q hq40 hq x) := by
  let S := primalSupportVertices q hq40 hq x
  have hsumS :
      (∑ g ∈ S, HammingWeight (localView q hq40 hq g x)) =
        2 * HammingWeight x := by
    rw [← sum_localView_weight_eq_twice_globalWeight q hq40 hq x]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro g _hgUniv hgS
    have hzero : localView q hq40 hq g x = 0 := by
      by_contra hne
      exact hgS ((mem_primalSupportVertices_iff q hq40 hq x g).2 hne)
    rw [hzero]
    simp
  have hdegree (g : Vertex401 q) (hg : g ∈ S) :
      HammingWeight (localView q hq40 hq g x) ≤
        (lpsNeighborsIn401 q hq S g).card := by
    rw [localView_weight_eq_support_degree q hq40 hq x]
    apply Finset.card_le_card
    intro w hw
    have hsupport : (wordSupportGraph q hq x).Adj g w := by
      simpa using hw
    have hlps : (lpsCayleyGraph401 q hq).Adj g w :=
      (wordSupportGraph_le_lps q hq x) hsupport
    have hdegreePos : 0 < (wordSupportGraph q hq x).degree w :=
      SimpleGraph.Adj.degree_pos_right hsupport
    have hlocalPos : 0 < HammingWeight (localView q hq40 hq w x) := by
      rw [localView_weight_eq_support_degree q hq40 hq x]
      exact hdegreePos
    have hwS : w ∈ S :=
      (mem_primalSupportVertices_iff q hq40 hq x w).2 <|
        (HammingWeight_eq_zero_iff _).not.mp (Nat.ne_of_gt hlocalPos)
    exact Finset.mem_filter.2
      ⟨(LPSGraph.mem_lpsNeighbors401_iff_adj q hq g w).2 hlps, hwS⟩
  calc
    2 * HammingWeight x =
        ∑ g ∈ S, HammingWeight (localView q hq40 hq g x) := hsumS.symm
    _ ≤ ∑ g ∈ S, (lpsNeighborsIn401 q hq S g).card := by
      exact Finset.sum_le_sum fun g hg => hdegree g hg
    _ = insideAdjacencyCount401 q hq S := by
      rfl

/-- Supported vertices whose local edge support reaches the local distance
threshold. -/
def primalHeavyVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : Finset (Vertex401 q) :=
  (primalSupportVertices q hq40 hq x).filter fun g =>
    41 ≤ HammingWeight (localView q hq40 hq g x)

theorem primalSupport_card_eq_active_add_heavy
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (primalSupportVertices q hq40 hq x).card =
      (activeLightVertices q hq40 hq x).card +
        (primalHeavyVertices q hq40 hq x).card := by
  let A := activeLightVertices q hq40 hq x
  let H := primalHeavyVertices q hq40 hq x
  let S := primalSupportVertices q hq40 hq x
  have hdis : Disjoint A H := by
    rw [Finset.disjoint_left]
    intro g hgA hgH
    have hlight := (mem_activeLightVertices_iff q hq40 hq x g).1 hgA
    have hheavy : 41 ≤ HammingWeight (localView q hq40 hq g x) :=
      by
        change g ∈ primalHeavyVertices q hq40 hq x at hgH
        exact (Finset.mem_filter.1 hgH).2
    omega
  have hunion : A ∪ H = S := by
    ext g
    simp only [Finset.mem_union]
    rw [mem_activeLightVertices_iff q hq40 hq x g]
    simp only [H, primalHeavyVertices, Finset.mem_filter]
    rw [mem_primalSupportVertices_iff q hq40 hq x g]
    constructor
    · rintro (hlight | hheavy)
      · exact hlight.1
      · exact hheavy.1
    · intro hnonzero
      by_cases hlight : HammingWeight (localView q hq40 hq g x) < 41
      · exact Or.inl ⟨hnonzero, hlight⟩
      · exact Or.inr ⟨hnonzero, Nat.le_of_not_gt hlight⟩
  have hcard := Finset.card_union_of_disjoint hdis
  rw [hunion] at hcard
  simpa [A, H, S] using hcard

theorem fortyOne_mul_heavy_le_twice_weight
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    41 * (primalHeavyVertices q hq40 hq x).card ≤
      2 * HammingWeight x := by
  let H := primalHeavyVertices q hq40 hq x
  calc
    41 * H.card = ∑ _g ∈ H, 41 := by simp [Nat.mul_comm]
    _ ≤ ∑ g ∈ H, HammingWeight (localView q hq40 hq g x) := by
      apply Finset.sum_le_sum
      intro g hg
      exact (Finset.mem_filter.1 hg).2
    _ ≤ ∑ g, HammingWeight (localView q hq40 hq g x) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      intro g _hg _hgH
      omega
    _ = 2 * HammingWeight x :=
      sum_localView_weight_eq_twice_globalWeight q hq40 hq x

/-- The corrected `10^-7` primal-radius support estimate. -/
theorem activeLightVertices_expansion401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (x : Word (ZMod 2) (Edge401 q hq))
    (hx : 10000000 * HammingWeight x ≤
      Fintype.card (Edge401 q hq)) :
    44 * HammingWeight x ≤
      41123 * (activeLightVertices q hq40 hq x).card := by
  let S := primalSupportVertices q hq40 hq x
  let D := insideAdjacencyCount401 q hq S
  let A := activeLightVertices q hq40 hq x
  let H := primalHeavyVertices q hq40 hq x
  have hedgeCard := card_edge401_eq q hq40 hq
  have hSCard := card_primalSupportVertices_le_twice_weight q hq40 hq x
  have hSCard' : S.card ≤ 2 * HammingWeight x := by
    simpa [S] using hSCard
  have hsmall : 10000000 * S.card ≤
      402 * Fintype.card (Vertex401 q) := by
    rw [hedgeCard] at hx
    omega
  have hspectral : 25 * D ≤ 1003 * S.card :=
    smallSet_insideAdjacency401 q hq40 hq hLPS S hsmall
  have hedgeInside : 2 * HammingWeight x ≤ D :=
    twice_weight_le_insideAdjacency_primalSupport q hq40 hq x
  have hheavy : 41 * H.card ≤ 2 * HammingWeight x :=
    fortyOne_mul_heavy_le_twice_weight q hq40 hq x
  have hpartition : S.card = A.card + H.card :=
    by
      simpa [S, A, H] using
        primalSupport_card_eq_active_add_heavy q hq40 hq x
  have hresult : 44 * HammingWeight x ≤ 41123 * A.card := by
    omega
  simpa [A] using hresult

/-- Concrete primal BE20 Tanner expansion at the owner-approved repaired
radius `10^-7`. -/
theorem be20Tanner_boundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (tannerBoundary q hq40 hq).SmallSetExpandingAtRelativeRadius
      1 10000000 44 41123 := by
  apply tannerBoundary_smallSetExpandingAtRelativeRadius_of_activeLightVertices
    q hq40 hq 1 10000000 44 41123
  · norm_num
  · norm_num
  · intro x hx
    apply activeLightVertices_expansion401 q hq40 hq hLPS x
    simpa using hx

/-! ## Transpose expansion -/

private theorem hammingWeight_eq_sum_indicator
    {F : Type*} [Zero F] [DecidableEq F]
    {ι : Type*} [Fintype ι] (z : Word F ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]

theorem HammingWeight_eq_sum_checkBlock
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight y = ∑ g, HammingWeight (checkBlock q g y) := by
  rw [hammingWeight_eq_sum_indicator]
  simp_rw [hammingWeight_eq_sum_indicator]
  change (∑ p : Vertex401 q × Fin 200, if y p ≠ 0 then 1 else 0) =
    ∑ g : Vertex401 q, ∑ j : Fin 200, if y (g, j) ≠ 0 then 1 else 0
  exact Fintype.sum_prod_type _

/-- Vertices carrying at least one nonzero global check coordinate. -/
def dualSupportVertices
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) : Finset (Vertex401 q) :=
  Finset.univ.filter fun g => checkBlock q g y ≠ 0

theorem mem_dualSupportVertices_iff
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    g ∈ dualSupportVertices q y ↔ checkBlock q g y ≠ 0 := by
  simp [dualSupportVertices]

theorem card_dualSupportVertices_le_weight
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    (dualSupportVertices q y).card ≤ HammingWeight y := by
  let U := dualSupportVertices q y
  calc
    U.card = ∑ _g ∈ U, 1 := by simp
    _ ≤ ∑ g ∈ U, HammingWeight (checkBlock q g y) := by
      apply Finset.sum_le_sum
      intro g hg
      exact Nat.one_le_iff_ne_zero.2 <|
        (HammingWeight_eq_zero_iff _).not.mpr <|
          (mem_dualSupportVertices_iff q y g).1 hg
    _ ≤ ∑ g, HammingWeight (checkBlock q g y) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro g _hg _hgU
      omega
    _ = HammingWeight y := (HammingWeight_eq_sum_checkBlock q y).symm

theorem weight_le_200_mul_card_dualSupportVertices
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight y ≤ 200 * (dualSupportVertices q y).card := by
  let U := dualSupportVertices q y
  have hsumU :
      (∑ g ∈ U, HammingWeight (checkBlock q g y)) = HammingWeight y := by
    rw [HammingWeight_eq_sum_checkBlock q y]
    apply Finset.sum_subset (Finset.subset_univ U)
    intro g _hgUniv hgU
    have hzero : checkBlock q g y = 0 := by
      by_contra hne
      exact hgU ((mem_dualSupportVertices_iff q y g).2 hne)
    rw [hzero]
    simp
  calc
    HammingWeight y = ∑ g ∈ U, HammingWeight (checkBlock q g y) := hsumU.symm
    _ ≤ ∑ _g ∈ U, 200 := by
      apply Finset.sum_le_sum
      intro g _hg
      change (hammingSupport (checkBlock q g y)).card ≤ 200
      simpa using Finset.card_le_card
        (Finset.subset_univ (hammingSupport (checkBlock q g y)))
    _ = 200 * U.card := by simp [Nat.mul_comm]

/-- The fixed local-coordinate labelling followed by the incidence/neighbor
equivalence. -/
def localCoordinateNeighborEquiv
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) :
    LocalCoordinate ≃ (lpsCayleyGraph401 q hq).neighborSet g :=
  (incidentCoordinateEquiv q hq40 hq g).symm.trans
    ((lpsCayleyGraph401 q hq).incidenceSetEquivNeighborSet g)

/-- Neighbors selected by nonzero coordinates of the local dual codeword at
`g`. -/
def dualSupportedNeighbors
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) : Finset (Vertex401 q) :=
  let E := localCoordinateNeighborEquiv q hq40 hq g
  let emb : LocalCoordinate ↪ Vertex401 q :=
    E.toEmbedding.trans (Function.Embedding.subtype _)
  (hammingSupport
    (wordLinearMapTranspose localParityCheck (checkBlock q g y))).map emb

theorem card_dualSupportedNeighbors
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    (dualSupportedNeighbors q hq40 hq y g).card =
      HammingWeight
        (wordLinearMapTranspose localParityCheck (checkBlock q g y)) := by
  simp [dualSupportedNeighbors, HammingWeight]

theorem dualSupportedNeighbors_subset_lps
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    dualSupportedNeighbors q hq40 hq y g ⊆ lpsNeighbors401 q hq g := by
  intro w hw
  rcases Finset.mem_map.1 hw with ⟨a, ha, rfl⟩
  exact (LPSGraph.mem_lpsNeighbors401_iff_adj q hq g _).2
    (localCoordinateNeighborEquiv q hq40 hq g a).2

/-- A supported check block with fewer than 41 supported graph-neighbors has
an actual edge on which its local dual word is nonzero and the other endpoint
has zero check block. -/
theorem nonempty_dualExposure_of_inside_lt
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q)
    (hg : g ∈ dualSupportVertices q y)
    (hinside : (lpsNeighborsIn401 q hq (dualSupportVertices q y) g).card < 41) :
    Nonempty (DualExposureWitness q hq40 hq y g) := by
  let U := dualSupportVertices q y
  let z := wordLinearMapTranspose localParityCheck (checkBlock q g y)
  let N := dualSupportedNeighbors q hq40 hq y g
  have hblock : checkBlock q g y ≠ 0 :=
    (mem_dualSupportVertices_iff q y g).1 hg
  have hzWeight : 41 ≤ HammingWeight z :=
    localTranspose_weight_lower_bound (checkBlock q g y) hblock
  have hNCard : 41 ≤ N.card := by
    rw [card_dualSupportedNeighbors q hq40 hq y g]
    exact hzWeight
  have hnotSubset : ¬N ⊆ lpsNeighborsIn401 q hq U g := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    change (lpsNeighborsIn401 q hq U g).card < 41 at hinside
    omega
  rcases Finset.not_subset.mp hnotSubset with ⟨w, hwN, hwOutside⟩
  have hwLPS : w ∈ lpsNeighbors401 q hq g :=
    dualSupportedNeighbors_subset_lps q hq40 hq y g hwN
  have hwNotU : w ∉ U := by
    intro hwU
    exact hwOutside (Finset.mem_filter.2 ⟨hwLPS, hwU⟩)
  let E := localCoordinateNeighborEquiv q hq40 hq g
  let emb : LocalCoordinate ↪ Vertex401 q :=
    E.toEmbedding.trans (Function.Embedding.subtype _)
  change w ∈ (hammingSupport z).map emb at hwN
  rcases Finset.mem_map.1 hwN with ⟨a, ha, haw⟩
  have hza : z a ≠ 0 := by
    simpa [hammingSupport] using ha
  let Λ := incidentCoordinateEquiv q hq40 hq g
  let i := Λ.symm a
  let e : Edge401 q hq := incidentAsEdge q hq i
  have hendpoint : g ∈ e.1 := i.2.2
  have hedgeIncident : edgeAsIncident q hq e g hendpoint = i := by
    apply Subtype.ext
    rfl
  have hcoord : edgeLocalCoordinate q hq40 hq e g hendpoint = a := by
    change Λ (edgeAsIncident q hq e g hendpoint) = a
    rw [hedgeIncident]
    exact Λ.apply_symm_apply a
  have hi : i.1 = s(g, (E a).1) := by
    have h := ((lpsCayleyGraph401 q hq).incidenceSetEquivNeighborSet g).symm_apply_apply i
    exact (congrArg Subtype.val h).symm
  have hEa : (E a).1 = w := by
    exact haw
  have heval : e.1 = s(g, w) := by
    change i.1 = s(g, w)
    rw [hi, hEa]
  have hwBlockZero : checkBlock q w y = 0 := by
    by_contra hne
    exact hwNotU ((mem_dualSupportVertices_iff q y w).2 hne)
  refine ⟨{
    edge := e
    endpoint := hendpoint
    centerNonzero := hblock
    localNonzero := ?_
    otherZero := ?_ }⟩
  · rw [hcoord]
    exact hza
  · intro u hu hug
    have hu' : u ∈ s(g, w) := by simpa [heval] using hu
    rcases (Sym2.mem_iff.mp hu') with rfl | rfl
    · exact (hug rfl).elim
    · exact hwBlockZero

/-- Supported check-block vertices that do not expose an edge to the zero
block region. -/
def dualUnexposedSupportVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) : Finset (Vertex401 q) :=
  dualSupportVertices q y \ dualExposedVertices q hq40 hq y

theorem dualSupport_card_eq_exposed_add_unexposed
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    (dualSupportVertices q y).card =
      (dualExposedVertices q hq40 hq y).card +
        (dualUnexposedSupportVertices q hq40 hq y).card := by
  let U := dualSupportVertices q y
  let X := dualExposedVertices q hq40 hq y
  let B := dualUnexposedSupportVertices q hq40 hq y
  have hXU : X ⊆ U := by
    intro g hg
    rcases (mem_dualExposedVertices_iff q hq40 hq y g).1 hg with ⟨witness⟩
    exact (mem_dualSupportVertices_iff q y g).2 witness.centerNonzero
  have hdis : Disjoint X B := by
    rw [Finset.disjoint_left]
    intro g hgX hgB
    exact (Finset.mem_sdiff.1 hgB).2 hgX
  have hunion : X ∪ B = U := by
    ext g
    simp only [Finset.mem_union, B, dualUnexposedSupportVertices,
      Finset.mem_sdiff]
    constructor
    · rintro (hgX | ⟨hgU, _hgX⟩)
      · exact hXU hgX
      · exact hgU
    · intro hgU
      by_cases hgX : g ∈ X
      · exact Or.inl hgX
      · exact Or.inr ⟨hgU, hgX⟩
  have hcard := Finset.card_union_of_disjoint hdis
  rw [hunion] at hcard
  simpa [U, X, B] using hcard

theorem fortyOne_mul_unexposed_le_insideAdjacency
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) :
    41 * (dualUnexposedSupportVertices q hq40 hq y).card ≤
      insideAdjacencyCount401 q hq (dualSupportVertices q y) := by
  let U := dualSupportVertices q y
  let B := dualUnexposedSupportVertices q hq40 hq y
  have hinside (g : Vertex401 q) (hg : g ∈ B) :
      41 ≤ (lpsNeighborsIn401 q hq U g).card := by
    by_contra hlt
    have hgU : g ∈ U := (Finset.mem_sdiff.1 hg).1
    have hexposure := nonempty_dualExposure_of_inside_lt
      q hq40 hq y g hgU (by
        simpa [U] using (show (lpsNeighborsIn401 q hq U g).card < 41 by omega))
    have hgX : g ∈ dualExposedVertices q hq40 hq y :=
      (mem_dualExposedVertices_iff q hq40 hq y g).2 hexposure
    exact (Finset.mem_sdiff.1 hg).2 hgX
  calc
    41 * B.card = ∑ _g ∈ B, 41 := by simp [Nat.mul_comm]
    _ ≤ ∑ g ∈ B, (lpsNeighborsIn401 q hq U g).card := by
      exact Finset.sum_le_sum fun g hg => hinside g hg
    _ ≤ ∑ g ∈ U, (lpsNeighborsIn401 q hq U g).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro g hg
        exact (Finset.mem_sdiff.1 hg).1
      · intro g _hg _hgB
        omega
    _ = insideAdjacencyCount401 q hq U := by rfl

theorem card_check401_eq
    (q : ℕ) [Fact q.Prime] :
    Fintype.card (Check401 q) = 200 * Fintype.card (Vertex401 q) := by
  simp [Check401, Nat.mul_comm]

/-- The corrected `10^-7` transpose-radius exposure estimate. -/
theorem dualExposedVertices_expansion401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (y : Word (ZMod 2) (Check401 q))
    (hy : 10000000 * HammingWeight y ≤ Fintype.card (Check401 q)) :
    11 * HammingWeight y ≤
      102500 * (dualExposedVertices q hq40 hq y).card := by
  let U := dualSupportVertices q y
  let X := dualExposedVertices q hq40 hq y
  let B := dualUnexposedSupportVertices q hq40 hq y
  let D := insideAdjacencyCount401 q hq U
  have hUCard := card_dualSupportVertices_le_weight q y
  have hUCard' : U.card ≤ HammingWeight y := by simpa [U] using hUCard
  rw [card_check401_eq q] at hy
  have hsmall : 10000000 * U.card ≤
      402 * Fintype.card (Vertex401 q) := by
    omega
  have hspectral : 25 * D ≤ 1003 * U.card :=
    smallSet_insideAdjacency401 q hq40 hq hLPS U hsmall
  have hbad : 41 * B.card ≤ D := by
    simpa [B, D, U] using
      fortyOne_mul_unexposed_le_insideAdjacency q hq40 hq y
  have hpartition : U.card = X.card + B.card := by
    simpa [U, X, B] using
      dualSupport_card_eq_exposed_add_unexposed q hq40 hq y
  have hweight := weight_le_200_mul_card_dualSupportVertices q y
  have hweight' : HammingWeight y ≤ 200 * U.card := by simpa [U] using hweight
  have hresult : 11 * HammingWeight y ≤ 102500 * X.card := by
    omega
  simpa [X] using hresult

/-- Concrete transpose BE20 Tanner expansion at the owner-approved repaired
radius `10^-7`. -/
theorem be20Tanner_coboundary_expansion
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    (wordLinearMapTranspose (tannerBoundary q hq40 hq)).SmallSetExpandingAtRelativeRadius
      1 10000000 11 102500 := by
  apply transpose_tannerBoundary_smallSetExpandingAtRelativeRadius_of_dualExposed
    q hq40 hq 1 10000000 11 102500
  · norm_num
  · norm_num
  · intro y hy
    apply dualExposedVertices_expansion401 q hq40 hq hLPS y
    simpa using hy

end QEC.Coding.BalancedProduct.LPSTannerExpansion

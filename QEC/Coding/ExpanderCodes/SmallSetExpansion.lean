import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Small-set expansion counting for PK22

This module isolates the graph-counting endgame in the PK22 locally-minimal
cycle argument. A weighted graph records oriented-edge multiplicities, so it
also covers the length-two multigraph used in the paper. The main theorem
says that a labelled set must be empty when every labelled vertex expands in
one of two graphs and both graphs obey the corresponding small-set mixing
bounds.
-/

namespace QEC.Coding.SmallSetExpansion

universe u

variable {V : Type u}

/-- A finite directed multigraph, represented by its edge multiplicities. -/
abbrev WeightedGraph (V : Type u) := V → V → Nat

/-- Number of oriented edges, with multiplicity, from `S` to `T`. -/
def crossCount (M : WeightedGraph V) (S T : Finset V) : Nat :=
  ∑ v ∈ S, ∑ u ∈ T, M v u

/-- The small-set edge-expansion inequality used by PK22. -/
def IsSmallSetEdgeExpanding
    (M : WeightedGraph V) (radius : Nat) (lambda : ℝ) : Prop :=
  ∀ S T : Finset V,
    S.card ≤ radius → T.card ≤ radius →
      (crossCount M S T : ℝ) ≤
        lambda * Real.sqrt ((S.card : ℝ) * T.card)

/-- Every vertex of `S` has at least `degree` outgoing edges into `T`. -/
def HasForwardDegreeAtLeast
    (M : WeightedGraph V) (S T : Finset V) (degree : Nat) : Prop :=
  ∀ v ∈ S, degree ≤ ∑ u ∈ T, M v u

/-- The length-two multigraph of a weighted graph. -/
def square [Fintype V] (M : WeightedGraph V) : WeightedGraph V :=
  fun v u => ∑ x, M v x * M x u

/-- The union of two weighted multigraphs on the same vertex type. -/
def add (M N : WeightedGraph V) : WeightedGraph V :=
  fun v u => M v u + N v u

/-- Relabel a weighted graph along a vertex equivalence. -/
def relabel {U : Type*} (e : V ≃ U) (M : WeightedGraph V) : WeightedGraph U :=
  fun u u' => M (e.symm u) (e.symm u')

/-- The disjoint union of a family of weighted graphs with a common vertex
type.  The first coordinate names the connected component. -/
def disjointUnion {I : Type*} [DecidableEq I]
    (M : I → WeightedGraph V) : WeightedGraph (I × V) :=
  fun iv ju => if iv.1 = ju.1 then M iv.1 iv.2 ju.2 else 0

/-- Count composable pairs by grouping them according to their intermediate
value.  This is the finite combinatorial identity behind multiplication of
weighted adjacency matrices. -/
theorem card_filter_product_eq_sum_card_fibers
    {A B X U : Type*} [Fintype A] [Fintype B] [Fintype X]
    [DecidableEq X] [DecidableEq U]
    (f : A → X) (g : X → B → U) (u : U) :
    (Finset.univ.filter fun p : A × B => g (f p.1) p.2 = u).card =
      ∑ x, (Finset.univ.filter fun a : A => f a = x).card *
        (Finset.univ.filter fun b : B => g x b = u).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ p ∈ (Finset.univ : Finset A) ×ˢ (Finset.univ : Finset B),
    if g (f p.1) p.2 = u then 1 else 0) = _
  rw [Finset.sum_product]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset A) f
    (fun a => ∑ b ∈ (Finset.univ : Finset B),
      if g (f a) b = u then 1 else 0)]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_filter]
  simp only [Finset.mem_filter] at ha
  simp [ha.2]

/-- Cross counts are additive under weighted-graph union. -/
theorem crossCount_add (M N : WeightedGraph V) (S T : Finset V) :
    crossCount (add M N) S T = crossCount M S T + crossCount N S T := by
  simp [crossCount, add, Finset.sum_add_distrib]

/-- A union on the same vertices has the sum of the two mixing constants. -/
theorem IsSmallSetEdgeExpanding.add
    {M N : WeightedGraph V} {radius : Nat} {lambda mu : ℝ}
    (hM : IsSmallSetEdgeExpanding M radius lambda)
    (hN : IsSmallSetEdgeExpanding N radius mu) :
    IsSmallSetEdgeExpanding (add M N) radius (lambda + mu) := by
  intro S T hS hT
  rw [crossCount_add, Nat.cast_add]
  calc
    (crossCount M S T : ℝ) + crossCount N S T ≤
        lambda * Real.sqrt ((S.card : ℝ) * T.card) +
          mu * Real.sqrt ((S.card : ℝ) * T.card) :=
      add_le_add (hM S T hS hT) (hN S T hS hT)
    _ = (lambda + mu) * Real.sqrt ((S.card : ℝ) * T.card) := by ring

/-- Relabelling preserves cross counts after transporting the two sets. -/
theorem crossCount_relabel
    {U : Type*} [DecidableEq V] [DecidableEq U]
    (e : V ≃ U) (M : WeightedGraph V) (S T : Finset U) :
    crossCount (relabel e M) S T =
      crossCount M (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding) := by
  classical
  simp [crossCount, relabel]

/-- Small-set expansion is invariant under a bijective relabelling of the
vertices. -/
theorem IsSmallSetEdgeExpanding.relabel
    {U : Type*} [DecidableEq V] [DecidableEq U]
    {M : WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hM : IsSmallSetEdgeExpanding M radius lambda) (e : V ≃ U) :
    IsSmallSetEdgeExpanding (relabel e M) radius lambda := by
  intro S T hS hT
  rw [crossCount_relabel]
  simpa using hM (S.map e.symm.toEmbedding) (T.map e.symm.toEmbedding)
    (by simpa using hS) (by simpa using hT)

/-- The vertices of a product finset lying over one first coordinate, with
that fixed coordinate removed. -/
def productFiber {I : Type*} [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) (i : I) : Finset V :=
  (S.filter fun iv => iv.1 = i).image Prod.snd

/-- A product finset is the disjoint union of its first-coordinate fibers. -/
theorem sum_card_productFiber
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) :
    ∑ i, (productFiber S i).card = S.card := by
  classical
  calc
    ∑ i, (productFiber S i).card =
        ∑ i, (S.filter fun iv => iv.1 = i).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [productFiber, Finset.card_image_iff.mpr]
      intro x hx y hy hxy
      exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
        (Finset.mem_filter.mp hy).2.symm) hxy
    _ = S.card := by
      have hMaps : Set.MapsTo (fun x : I × V => x.1) (↑S)
          (↑(Finset.univ : Finset I)) := by
        intro x _hx
        exact Finset.mem_univ x.1
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (s := S) (t := (Finset.univ : Finset I))
          (f := fun x : I × V => x.1)
          hMaps).symm

/-- Each first-coordinate fiber has at most as many elements as the whole
product finset. -/
theorem card_productFiber_le
    {I : Type*} [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) (i : I) :
    (productFiber S i).card ≤ S.card := by
  classical
  rw [productFiber, Finset.card_image_iff.mpr]
  · exact Finset.card_filter_le _ _
  · intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm) hxy

/-- Cross counts in a disjoint union split as the sum of the component cross
counts of the corresponding fibers. -/
theorem crossCount_disjointUnion
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (M : I → WeightedGraph V) (S T : Finset (I × V)) :
    crossCount (disjointUnion M) S T =
      ∑ i, crossCount (M i) (productFiber S i) (productFiber T i) := by
  classical
  simp only [crossCount, disjointUnion]
  rw [← Finset.sum_fiberwise S Prod.fst (fun iv =>
    ∑ ju ∈ T, if iv.1 = ju.1 then M iv.1 iv.2 ju.2 else 0)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [productFiber, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro iv hiv
    have hivFirst : iv.1 = i := (Finset.mem_filter.mp hiv).2
    calc
      (∑ ju ∈ T, if iv.1 = ju.1 then M iv.1 iv.2 ju.2 else 0) =
          ∑ ju ∈ T with ju.1 = i, M i iv.2 ju.2 := by
        simp only [hivFirst]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ju _hju
        by_cases hji : i = ju.1 <;> simp [hji, eq_comm]
      _ = ∑ u ∈ (T.filter fun ju => ju.1 = i).image Prod.snd,
          M i iv.2 u := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
          (Finset.mem_filter.mp hy).2.symm) hxy
  · intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm) hxy

/-- A disjoint union of small-set expanders has the same mixing constant.
The Cauchy--Schwarz step is essential: there is no loss by the number of
components. -/
theorem IsSmallSetEdgeExpanding.disjointUnion
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    {M : I → WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hM : ∀ i, IsSmallSetEdgeExpanding (M i) radius lambda) :
    IsSmallSetEdgeExpanding (disjointUnion M) radius lambda := by
  intro S T hS hT
  rw [crossCount_disjointUnion, Nat.cast_sum]
  have hFiberS (i : I) : (productFiber S i).card ≤ radius :=
    (card_productFiber_le S i).trans hS
  have hFiberT (i : I) : (productFiber T i).card ≤ radius :=
    (card_productFiber_le T i).trans hT
  calc
    ∑ i, (crossCount (M i) (productFiber S i) (productFiber T i) : ℝ) ≤
        ∑ i, lambda * Real.sqrt
          (((productFiber S i).card : ℝ) * (productFiber T i).card) :=
      Finset.sum_le_sum fun i _hi => hM i _ _ (hFiberS i) (hFiberT i)
    _ = lambda * ∑ i, Real.sqrt ((productFiber S i).card : ℝ) *
          Real.sqrt ((productFiber T i).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ ≤ lambda * (Real.sqrt (∑ i, ((productFiber S i).card : ℝ)) *
          Real.sqrt (∑ i, ((productFiber T i).card : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)) hLambda
    _ = lambda * Real.sqrt ((S.card : ℝ) * T.card) := by
      have hSumS : ∑ i, ((productFiber S i).card : ℝ) = S.card := by
        exact_mod_cast sum_card_productFiber S
      have hSumT : ∑ i, ((productFiber T i).card : ℝ) = T.card := by
        exact_mod_cast sum_card_productFiber T
      rw [hSumS, hSumT, Real.sqrt_mul (Nat.cast_nonneg S.card)]

/-- Pointwise domination of weighted graphs increases every cross count. -/
theorem crossCount_mono
    {M N : WeightedGraph V} (hMN : ∀ v u, M v u ≤ N v u)
    (S T : Finset V) :
    crossCount M S T ≤ crossCount N S T := by
  unfold crossCount
  exact Finset.sum_le_sum fun v _hv =>
    Finset.sum_le_sum fun u _hu => hMN v u

/-- A pointwise subgraph inherits the same small-set expansion bound. -/
theorem IsSmallSetEdgeExpanding.of_pointwise_le
    {M N : WeightedGraph V} {radius : Nat} {lambda : ℝ}
    (hN : IsSmallSetEdgeExpanding N radius lambda)
    (hMN : ∀ v u, M v u ≤ N v u) :
    IsSmallSetEdgeExpanding M radius lambda := by
  intro S T hS hT
  calc
    (crossCount M S T : ℝ) ≤ crossCount N S T := by
      exact_mod_cast crossCount_mono hMN S T
    _ ≤ lambda * Real.sqrt ((S.card : ℝ) * T.card) := hN S T hS hT

/-- Small-set expansion is monotone under shrinking the radius and enlarging
the mixing constant. -/
theorem IsSmallSetEdgeExpanding.mono
    {M : WeightedGraph V} {radius radius' : Nat} {lambda lambda' : ℝ}
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (hRadius : radius' ≤ radius) (hLambda : lambda ≤ lambda') :
    IsSmallSetEdgeExpanding M radius' lambda' := by
  intro S T hS hT
  calc
    (crossCount M S T : ℝ) ≤
        lambda * Real.sqrt ((S.card : ℝ) * T.card) :=
      hExpand S T (hS.trans hRadius) (hT.trans hRadius)
    _ ≤ lambda' * Real.sqrt ((S.card : ℝ) * T.card) :=
      mul_le_mul_of_nonneg_right hLambda (Real.sqrt_nonneg _)

/-- Pointwise lower bounds on degrees sum to a cross-edge lower bound. -/
theorem degree_mul_card_le_crossCount
    (M : WeightedGraph V) (S T : Finset V) (degree : Nat)
    (hDegree : HasForwardDegreeAtLeast M S T degree) :
    degree * S.card ≤ crossCount M S T := by
  unfold crossCount
  calc
    degree * S.card = ∑ _v ∈ S, degree := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, ∑ u ∈ T, M v u := by
      exact Finset.sum_le_sum fun v hv => hDegree v hv

/-- The counting core of PK22's labelled-edge lemma.  Let `A` be the active
edge set and `S ⊆ A` the active edges with no labelled endpoint.  Small-set
mixing bounds the neighbours of `S` that stay in `S`; a local-code distance
lower bound forces many neighbours in `A`; and the two unlabelled endpoints
allow strictly fewer than `2m` neighbours in `A \ S`.  If the distance beats
`2m + lambda`, the bad set `S` is empty. -/
theorem subset_eq_empty_of_internal_expansion_and_external_degree_lt
    [DecidableEq V]
    (M : WeightedGraph V) (radius : Nat) (lambda : ℝ)
    (A S : Finset V) (d m : Nat)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (hSA : S ⊆ A) (hARadius : A.card ≤ radius)
    (hDegree : HasForwardDegreeAtLeast M S A d)
    (hExternal : ∀ v ∈ S,
      (∑ u ∈ A \ S, M v u) < 2 * m)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    S = ∅ := by
  by_contra hS
  have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hSRadius : S.card ≤ radius :=
    (Finset.card_le_card hSA).trans hARadius
  have hInternal := hExpand S S hSRadius hSRadius
  have hRoot : Real.sqrt ((S.card : ℝ) * S.card) = S.card := by
    rw [show (S.card : ℝ) * S.card = (S.card : ℝ) ^ 2 by ring]
    exact Real.sqrt_sq (Nat.cast_nonneg S.card)
  rw [hRoot] at hInternal
  have hExternalSum :
      crossCount M S (A \ S) < 2 * m * S.card := by
    unfold crossCount
    calc
      (∑ v ∈ S, ∑ u ∈ A \ S, M v u) <
          ∑ _v ∈ S, 2 * m :=
        Finset.sum_lt_sum_of_nonempty hSNonempty hExternal
      _ = 2 * m * S.card := by simp [Nat.mul_comm]
  have hASplit : A = S ∪ (A \ S) := by
    ext u
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases huS : u ∈ S
      · exact Or.inl huS
      · exact Or.inr ⟨hu, huS⟩
    · rintro (huS | ⟨huA, _huS⟩)
      · exact hSA huS
      · exact huA
  have hDisjoint : Disjoint S (A \ S) := by
    exact Finset.disjoint_left.mpr fun u huS huDiff =>
      (Finset.mem_sdiff.mp huDiff).2 huS
  have hCrossSplit :
      crossCount M S A =
        crossCount M S S + crossCount M S (A \ S) := by
    have hInner : ∀ v,
        (∑ u ∈ A, M v u) =
          (∑ u ∈ S, M v u) + ∑ u ∈ A \ S, M v u := by
      intro v
      calc
        (∑ u ∈ A, M v u) = ∑ u ∈ S ∪ (A \ S), M v u := by
          exact Finset.sum_congr hASplit fun _u _hu => rfl
        _ = (∑ u ∈ S, M v u) + ∑ u ∈ A \ S, M v u :=
          Finset.sum_union hDisjoint
    unfold crossCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    exact hInner v
  have hDegreeSum := degree_mul_card_le_crossCount M S A d hDegree
  have hDegreeReal :
      (d : ℝ) * S.card ≤ (crossCount M S A : ℝ) := by
    exact_mod_cast hDegreeSum
  have hExternalReal :
      (crossCount M S (A \ S) : ℝ) <
        (2 * m : ℝ) * S.card := by
    exact_mod_cast hExternalSum
  rw [hCrossSplit, Nat.cast_add] at hDegreeReal
  have hSCardPos : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hSNonempty
  nlinarith

/-- Mixing plus a factor-two degree advantage forces an expanding subset to
occupy at most one quarter of the ambient labelled set. -/
theorem four_mul_card_le_of_degree_and_expansion
    (M : WeightedGraph V) (radius degree : Nat) (lambda : ℝ)
    (hLambda : 0 < lambda)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda)
    (S L : Finset V) (hSRadius : S.card ≤ radius)
    (hLRadius : L.card ≤ radius)
    (hDegree : HasForwardDegreeAtLeast M S L degree)
    (hThreshold : 2 * lambda ≤ degree) :
    4 * S.card ≤ L.card := by
  by_cases hS : S.card = 0
  · simp [hS]
  have hSPosNat : 0 < S.card := Nat.pos_of_ne_zero hS
  have hSPos : (0 : ℝ) < S.card := by exact_mod_cast hSPosNat
  have hCountNat := degree_mul_card_le_crossCount M S L degree hDegree
  have hCount : (degree : ℝ) * S.card ≤ (crossCount M S L : ℝ) := by
    exact_mod_cast hCountNat
  have hMix := hExpand S L hSRadius hLRadius
  have hThreshold' : 2 * lambda ≤ (degree : ℝ) := by
    simpa using hThreshold
  have hLambdaScaled : lambda * (2 * (S.card : ℝ)) ≤
      lambda * Real.sqrt ((S.card : ℝ) * L.card) := by
    calc
      lambda * (2 * (S.card : ℝ)) =
          (2 * lambda) * (S.card : ℝ) := by ring
      _ ≤ (degree : ℝ) * S.card :=
        mul_le_mul_of_nonneg_right hThreshold' (le_of_lt hSPos)
      _ ≤ (crossCount M S L : ℝ) := hCount
      _ ≤ lambda * Real.sqrt ((S.card : ℝ) * L.card) := hMix
  have hRoot : 2 * (S.card : ℝ) ≤
      Real.sqrt ((S.card : ℝ) * L.card) := by
    nlinarith
  have hProductNonnegative :
      0 ≤ (S.card : ℝ) * L.card := mul_nonneg (by positivity) (by positivity)
  have hRootSq :
      (Real.sqrt ((S.card : ℝ) * L.card)) ^ 2 =
        (S.card : ℝ) * L.card := Real.sq_sqrt hProductNonnegative
  have hFourReal : 4 * (S.card : ℝ) ≤ L.card := by
    have hRootNonnegative := Real.sqrt_nonneg ((S.card : ℝ) * L.card)
    nlinarith
  exact_mod_cast hFourReal

/-- PK22's labelled-set elimination step. If every labelled vertex expands
in at least one of two small-set expanding graphs, and the degree thresholds
beat the two mixing constants by a factor of two, then there are no labelled
vertices. -/
theorem labelledSet_eq_empty
    [DecidableEq V]
    (M₁ M₂ : WeightedGraph V)
    (radius₁ radius₂ degree₁ degree₂ : Nat)
    (lambda₁ lambda₂ : ℝ)
    (hLambda₁ : 0 < lambda₁) (hLambda₂ : 0 < lambda₂)
    (hExpand₁ : IsSmallSetEdgeExpanding M₁ radius₁ lambda₁)
    (hExpand₂ : IsSmallSetEdgeExpanding M₂ radius₂ lambda₂)
    (L L₁ L₂ : Finset V)
    (hCover : L ⊆ L₁ ∪ L₂)
    (hL₁ : L₁ ⊆ L) (hL₂ : L₂ ⊆ L)
    (hLRadius₁ : L.card ≤ radius₁)
    (hLRadius₂ : L.card ≤ radius₂)
    (hDegree₁ : HasForwardDegreeAtLeast M₁ L₁ L degree₁)
    (hDegree₂ : HasForwardDegreeAtLeast M₂ L₂ L degree₂)
    (hThreshold₁ : 2 * lambda₁ ≤ degree₁)
    (hThreshold₂ : 2 * lambda₂ ≤ degree₂) :
    L = ∅ := by
  have hL₁Radius : L₁.card ≤ radius₁ :=
    (Finset.card_le_card hL₁).trans hLRadius₁
  have hL₂Radius : L₂.card ≤ radius₂ :=
    (Finset.card_le_card hL₂).trans hLRadius₂
  have hQuarter₁ : 4 * L₁.card ≤ L.card :=
    four_mul_card_le_of_degree_and_expansion M₁ radius₁ degree₁ lambda₁
      hLambda₁ hExpand₁ L₁ L hL₁Radius hLRadius₁ hDegree₁ hThreshold₁
  have hQuarter₂ : 4 * L₂.card ≤ L.card :=
    four_mul_card_le_of_degree_and_expansion M₂ radius₂ degree₂ lambda₂
      hLambda₂ hExpand₂ L₂ L hL₂Radius hLRadius₂ hDegree₂ hThreshold₂
  have hCardCover : L.card ≤ L₁.card + L₂.card := by
    exact (Finset.card_le_card hCover).trans (Finset.card_union_le L₁ L₂)
  have : L.card = 0 := by omega
  exact Finset.card_eq_zero.mp this

end QEC.Coding.SmallSetExpansion

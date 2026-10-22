import QEC.Coding.ExpanderCodes.TannerLabelledEdges
import QEC.Coding.ExpanderCodes.SmallSetExpansionSquare

/-!
# Graph expansion inherited by the PK22 Tanner product

This module identifies the horizontal, vertical, and physical-edge graphs in
the Tanner lifted product as disjoint unions of the labelled Cayley double
cover.  It formalizes the graph-decomposition step of PK22's `lemma:expG'`
without losing a factor equal to the number of components.
-/

namespace QEC.Coding.TannerLiftedProduct

universe v

variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]

/-- Right-multiplication presentation of the labelled Cayley double cover. -/
def rightDoubleCoverNeighbor (label : W → G) (x : Fin 2 × G) (a : W) :
    Fin 2 × G :=
  (oppositeSide x.1,
    x.2 * (doubleCoverVoltage label x.1 a)⁻¹ *
      doubleCoverVoltage label (oppositeSide x.1) a)

/-- Left-multiplication presentation of the same labelled double cover. -/
def leftDoubleCoverNeighbor (label : W → G) (x : Fin 2 × G) (a : W) :
    Fin 2 × G :=
  (oppositeSide x.1,
    doubleCoverVoltage label (oppositeSide x.1) a *
      (doubleCoverVoltage label x.1 a)⁻¹ * x.2)

/-- The labelled Cayley double-cover multigraph, retaining parallel generator
directions. -/
def rightDoubleCoverGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (Fin 2 × G) :=
  fun x y =>
    (Finset.univ.filter fun a : W =>
      rightDoubleCoverNeighbor label x a = y).card

/-- The left-multiplication presentation of the double-cover multigraph. -/
def leftDoubleCoverGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (Fin 2 × G) :=
  fun x y =>
    (Finset.univ.filter fun a : W =>
      leftDoubleCoverNeighbor label x a = y).card

/-- The right-multiplication labelled Cayley multigraph before taking its
bipartite double cover.  Parallel generator directions are retained. -/
def rightCayleyGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph G :=
  fun g h =>
    (Finset.univ.filter fun a : W => g * label a = h).card

omit [Fintype G] [DecidableEq W] in
/-- Reindexing the generator directions by an equivalence does not change
the labelled Cayley multigraph, including its parallel-edge multiplicities. -/
theorem rightCayleyGraph_reindex
    {W' : Type v} [Fintype W'] [DecidableEq W']
    (label : W → G) (e : W' ≃ W) :
    rightCayleyGraph (fun a => label (e a)) = rightCayleyGraph label := by
  funext g h
  unfold rightCayleyGraph
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun a => ⟨e a.1, by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp a.2).2⟩⟩
      invFun := fun a => ⟨e.symm a.1, by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by
          simpa using (Finset.mem_filter.mp a.2).2⟩⟩
      left_inv := fun a => by apply Subtype.ext; exact e.symm_apply_apply a.1
      right_inv := fun a => by apply Subtype.ext; exact e.apply_symm_apply a.1 }

omit [DecidableEq W] in
/-- The labelled Cayley multigraph has one outgoing edge for every labelled
generator direction. -/
theorem rightCayleyGraph_isRegular (label : W → G) :
    SmallSetExpansion.IsRegular (rightCayleyGraph label)
      (Fintype.card W) := by
  intro g
  unfold rightCayleyGraph
  simpa using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) (Finset.univ : Finset G) (fun a => g * label a)

omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_zero_one
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (0, g) (1, h) =
      rightCayleyGraph label g h := by
  simp [rightDoubleCoverGraph, rightCayleyGraph,
    rightDoubleCoverNeighbor, doubleCoverVoltage, oppositeSide]

omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_one_zero
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (1, g) (0, h) =
      rightCayleyGraph label h g := by
  unfold rightDoubleCoverGraph rightCayleyGraph
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _ha
  simp [rightDoubleCoverNeighbor, doubleCoverVoltage, oppositeSide]
  constructor
  · intro hga
    calc
      h * label a = (g * (label a)⁻¹) * label a := by rw [hga]
      _ = g := by simp
  · intro hga
    calc
      g * (label a)⁻¹ = (h * label a) * (label a)⁻¹ := by rw [hga]
      _ = h := by simp

omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_zero_zero
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (0, g) (0, h) = 0 := by
  simp [rightDoubleCoverGraph, rightDoubleCoverNeighbor,
    doubleCoverVoltage, oppositeSide]

omit [Fintype G] [DecidableEq W] in
@[simp] theorem rightDoubleCoverGraph_one_one
    (label : W → G) (g h : G) :
    rightDoubleCoverGraph label (1, g) (1, h) = 0 := by
  simp [rightDoubleCoverGraph, rightDoubleCoverNeighbor,
    doubleCoverVoltage, oppositeSide]

/-- Inversion together with switching the bipartite side identifies the two
multiplication conventions. -/
def sideInverseEquiv : (Fin 2 × G) ≃ (Fin 2 × G) where
  toFun x := (oppositeSide x.1, x.2⁻¹)
  invFun x := (oppositeSide x.1, x.2⁻¹)
  left_inv x := by rcases x with ⟨side, g⟩; simp
  right_inv x := by rcases x with ⟨side, g⟩; simp

omit [Fintype G] [DecidableEq G] in
@[simp] theorem sideInverseEquiv_apply (x : Fin 2 × G) :
    sideInverseEquiv x = (oppositeSide x.1, x.2⁻¹) := rfl

omit [Fintype G] [DecidableEq G] in
@[simp] theorem sideInverseEquiv_symm_apply (x : Fin 2 × G) :
    sideInverseEquiv.symm x = (oppositeSide x.1, x.2⁻¹) := rfl

omit [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W] in
/-- Switching sides and inverting conjugates left multiplication to right
multiplication. -/
theorem sideInverseEquiv_leftDoubleCoverNeighbor
    (label : W → G) (x : Fin 2 × G) (a : W) :
    sideInverseEquiv (leftDoubleCoverNeighbor label x a) =
      rightDoubleCoverNeighbor label (sideInverseEquiv x) a := by
  rcases x with ⟨side, g⟩
  fin_cases side <;>
    simp [sideInverseEquiv, leftDoubleCoverNeighbor,
      rightDoubleCoverNeighbor, doubleCoverVoltage, oppositeSide]

omit [Fintype G] [DecidableEq W] in
/-- The left and right presentations are graph-isomorphic. -/
theorem leftDoubleCoverGraph_eq_relabel (label : W → G) :
    leftDoubleCoverGraph label =
      SmallSetExpansion.relabel sideInverseEquiv
        (rightDoubleCoverGraph label) := by
  funext x y
  unfold leftDoubleCoverGraph rightDoubleCoverGraph
  change (Finset.univ.filter fun a : W =>
      leftDoubleCoverNeighbor label x a = y).card =
    (Finset.univ.filter fun a : W =>
      rightDoubleCoverNeighbor label (sideInverseEquiv x) a =
        sideInverseEquiv y).card
  congr 1
  apply Finset.filter_congr
  intro a _ha
  constructor
  · intro hxy
    rw [← sideInverseEquiv_leftDoubleCoverNeighbor]
    exact congrArg sideInverseEquiv hxy
  · intro hxy
    apply sideInverseEquiv.injective
    rw [sideInverseEquiv_leftDoubleCoverNeighbor]
    exact hxy

/-- Horizontal-only adjacency on product vertices. -/
def horizontalGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun a : W => horizontalNeighbor label v a = u).card

/-- Vertical-only adjacency on product vertices. -/
def verticalGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun b : W => verticalNeighbor label v b = u).card

/-- Reassociate product vertices so the fixed vertical side indexes horizontal
double-cover components. -/
def horizontalFiberEquiv :
    (Fin 2 × (Fin 2 × G)) ≃ VertexIndex G where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun v := (v.2.1, v.1, v.2.2)
  left_inv x := by rcases x with ⟨i, j, g⟩; rfl
  right_inv v := by rcases v with ⟨i, j, g⟩; rfl

/-- Product vertices already have the right association for vertical
double-cover components. -/
def verticalFiberEquiv :
    (Fin 2 × (Fin 2 × G)) ≃ VertexIndex G := Equiv.refl _

/-- Physical vertical edges decompose by their local vertical direction. -/
def verticalEdgeFiberEquiv :
    (W × (Fin 2 × G)) ≃ VerticalEdgeIndex W G where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun e := (e.2.1, e.1, e.2.2)
  left_inv x := by rcases x with ⟨b, side, g⟩; rfl
  right_inv e := by rcases e with ⟨side, b, g⟩; rfl

omit [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W] in
/-- A fixed generator direction is an involution on the right double cover. -/
@[simp] theorem rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
    (label : W → G) (x : Fin 2 × G) (a : W) :
    rightDoubleCoverNeighbor label
      (rightDoubleCoverNeighbor label x a) a = x := by
  rcases x with ⟨side, g⟩
  fin_cases side <;>
    simp [rightDoubleCoverNeighbor, doubleCoverVoltage, oppositeSide,
      mul_assoc]

omit [Fintype G] [DecidableEq G] [Fintype W] [DecidableEq W] in
/-- A fixed horizontal direction is an involution on product vertices. -/
@[simp] theorem horizontalNeighbor_horizontalNeighbor
    (label : W → G) (v : VertexIndex G) (a : W) :
    horizontalNeighbor label (horizontalNeighbor label v a) a = v := by
  rcases v with ⟨side, sideV, g⟩
  fin_cases side <;>
    simp [horizontalNeighbor, doubleCoverVoltage, oppositeSide, mul_assoc]

/-- A neighbor multigraph generated by involutions is symmetric. -/
theorem neighborGraph_isSymmetric
    {X A : Type*} [Fintype A] [DecidableEq X]
    (neighbor : X → A → X)
    (hInvolution : ∀ x a, neighbor (neighbor x a) a = x) :
    SmallSetExpansion.IsSymmetric
      (fun x y => (Finset.univ.filter fun a => neighbor x a = y).card) := by
  intro x y
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _ha
  constructor
  · intro hxy
    rw [← hxy, hInvolution]
  · intro hyx
    rw [← hyx, hInvolution]

omit [Fintype G] [DecidableEq W] in
/-- The labelled right double cover is symmetric because every labelled
direction is an involution after switching sides. -/
theorem rightDoubleCoverGraph_isSymmetric (label : W → G) :
    SmallSetExpansion.IsSymmetric (rightDoubleCoverGraph label) :=
  neighborGraph_isSymmetric (rightDoubleCoverNeighbor label)
    (rightDoubleCoverNeighbor_rightDoubleCoverNeighbor label)

omit [DecidableEq W] in
/-- Every double-cover vertex has exactly one outgoing edge for each labelled
direction, with parallel labels counted separately. -/
theorem rightDoubleCoverGraph_isRegular (label : W → G) :
    SmallSetExpansion.IsRegular (rightDoubleCoverGraph label)
      (Fintype.card W) := by
  intro x
  unfold rightDoubleCoverGraph
  simpa using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) (Finset.univ : Finset (Fin 2 × G))
    (rightDoubleCoverNeighbor label x)

/-- Expander-mixing estimate normalized by the size of one bipartite part.
This is the correct spectral interface for a double cover: the side-sign
eigenvector is a second trivial mode, so a full mean-zero bound on
`Fin 2 × G` cannot have a subdegree constant. -/
def HasPartiteExpanderMixingBound
    (M : SmallSetExpansion.WeightedGraph (Fin 2 × G))
    (degree : Nat) (spectral : ℝ) : Prop :=
  ∀ S T : Finset (Fin 2 × G),
    (Fintype.card G : ℝ) * SmallSetExpansion.crossCount M S T ≤
      degree * (S.card : ℝ) * T.card +
        spectral * Fintype.card G *
          Real.sqrt ((S.card : ℝ) * T.card)

/-- Vertices of a double-cover subset lying over one fixed bipartite side. -/
def sideSlice (S : Finset (Fin 2 × G)) (side : Fin 2) : Finset G :=
  Finset.univ.filter fun g => (side, g) ∈ S

omit [Group G] in
theorem card_eq_card_sideSlice_add (S : Finset (Fin 2 × G)) :
    S.card = (sideSlice S 0).card + (sideSlice S 1).card := by
  classical
  calc
    S.card = ∑ x : Fin 2 × G, if x ∈ S then 1 else 0 := by simp
    _ = (∑ g : G, if (0, g) ∈ S then 1 else 0) +
        ∑ g : G, if (1, g) ∈ S then 1 else 0 := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    _ = (sideSlice S 0).card + (sideSlice S 1).card := by
      rw [Finset.sum_boole, Finset.sum_boole]
      rfl

omit [Group G] in
theorem sum_eq_sum_sideSlices (S : Finset (Fin 2 × G))
    (f : Fin 2 × G → Nat) :
    (∑ x ∈ S, f x) =
      (∑ g ∈ sideSlice S 0, f (0, g)) +
        ∑ g ∈ sideSlice S 1, f (1, g) := by
  classical
  calc
    (∑ x ∈ S, f x) =
        ∑ x : Fin 2 × G, if x ∈ S then f x else 0 := by simp
    _ = (∑ g : G, if (0, g) ∈ S then f (0, g) else 0) +
        ∑ g : G, if (1, g) ∈ S then f (1, g) else 0 := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    _ = (∑ g ∈ sideSlice S 0, f (0, g)) +
        ∑ g ∈ sideSlice S 1, f (1, g) := by
      rw [sideSlice, sideSlice, Finset.sum_filter, Finset.sum_filter]

omit [DecidableEq W] in
/-- Cross counts in a labelled double cover are the two opposite-side cross
counts of its underlying Cayley multigraph. -/
theorem crossCount_rightDoubleCoverGraph
    (label : W → G) (S T : Finset (Fin 2 × G)) :
    SmallSetExpansion.crossCount (rightDoubleCoverGraph label) S T =
      SmallSetExpansion.crossCount (rightCayleyGraph label)
          (sideSlice S 0) (sideSlice T 1) +
        SmallSetExpansion.crossCount (rightCayleyGraph label)
          (sideSlice T 0) (sideSlice S 1) := by
  classical
  unfold SmallSetExpansion.crossCount
  rw [sum_eq_sum_sideSlices]
  simp_rw [sum_eq_sum_sideSlices T]
  simp
  rw [Finset.sum_comm]

omit [DecidableEq W] in
/-- Expander mixing for the non-bipartite Cayley graph passes to the
bipartite double cover without changing the nontrivial spectral constant.
The two trivial double-cover modes are represented by the part-normalized
density term in `HasPartiteExpanderMixingBound`. -/
theorem rightDoubleCoverGraph_hasPartiteExpanderMixingBound
    (label : W → G) (degree : Nat) (spectral : ℝ)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : SmallSetExpansion.HasExpanderMixingBound
      (rightCayleyGraph label) degree spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) degree spectral := by
  intro S T
  let n : ℝ := Fintype.card G
  let s0 : ℝ := (sideSlice S 0).card
  let s1 : ℝ := (sideSlice S 1).card
  let t0 : ℝ := (sideSlice T 0).card
  let t1 : ℝ := (sideSlice T 1).card
  have hn : 0 ≤ n := by positivity
  have hs0 : 0 ≤ s0 := by positivity
  have hs1 : 0 ≤ s1 := by positivity
  have ht0 : 0 ≤ t0 := by positivity
  have ht1 : 0 ≤ t1 := by positivity
  have hS : (S.card : ℝ) = s0 + s1 := by
    dsimp [s0, s1]
    exact_mod_cast card_eq_card_sideSlice_add S
  have hT : (T.card : ℝ) = t0 + t1 := by
    dsimp [t0, t1]
    exact_mod_cast card_eq_card_sideSlice_add T
  have hCross :
      (SmallSetExpansion.crossCount (rightDoubleCoverGraph label) S T : ℝ) =
        (SmallSetExpansion.crossCount (rightCayleyGraph label)
            (sideSlice S 0) (sideSlice T 1) : ℝ) +
          SmallSetExpansion.crossCount (rightCayleyGraph label)
            (sideSlice T 0) (sideSlice S 1) := by
    exact_mod_cast crossCount_rightDoubleCoverGraph label S T
  have h01 := hMixing (sideSlice S 0) (sideSlice T 1)
  have h10 := hMixing (sideSlice T 0) (sideSlice S 1)
  change n *
      (SmallSetExpansion.crossCount (rightCayleyGraph label)
        (sideSlice S 0) (sideSlice T 1) : ℝ) ≤
      degree * s0 * t1 + spectral * n * Real.sqrt (s0 * t1) at h01
  change n *
      (SmallSetExpansion.crossCount (rightCayleyGraph label)
        (sideSlice T 0) (sideSlice S 1) : ℝ) ≤
      degree * t0 * s1 + spectral * n * Real.sqrt (t0 * s1) at h10
  have hrs0 : (Real.sqrt s0) ^ 2 = s0 := Real.sq_sqrt hs0
  have hrs1 : (Real.sqrt s1) ^ 2 = s1 := Real.sq_sqrt hs1
  have hrt0 : (Real.sqrt t0) ^ 2 = t0 := Real.sq_sqrt ht0
  have hrt1 : (Real.sqrt t1) ^ 2 = t1 := Real.sq_sqrt ht1
  have hCauchySq :
      (Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1)) ^ 2 ≤
        (s0 + s1) * (t0 + t1) := by
    rw [Real.sqrt_mul hs0, Real.sqrt_mul ht0]
    nlinarith [sq_nonneg
      (Real.sqrt s0 * Real.sqrt t0 - Real.sqrt s1 * Real.sqrt t1)]
  have hRootSum :
      Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1) ≤
        Real.sqrt ((s0 + s1) * (t0 + t1)) := by
    have hLeft :
        0 ≤ Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1) := by positivity
    have hProduct : 0 ≤ (s0 + s1) * (t0 + t1) := by positivity
    have hRightSq :
        (Real.sqrt ((s0 + s1) * (t0 + t1))) ^ 2 =
          (s0 + s1) * (t0 + t1) := Real.sq_sqrt hProduct
    have hRight :
        0 ≤ Real.sqrt ((s0 + s1) * (t0 + t1)) := Real.sqrt_nonneg _
    nlinarith
  have hDensity :
      (degree : ℝ) * s0 * t1 + degree * t0 * s1 ≤
        degree * (s0 + s1) * (t0 + t1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg degree) (mul_nonneg hs0 ht0),
      mul_nonneg (Nat.cast_nonneg degree) (mul_nonneg hs1 ht1)]
  have hSpectral :
      spectral * n *
          (Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1)) ≤
        spectral * n * Real.sqrt ((s0 + s1) * (t0 + t1)) :=
    mul_le_mul_of_nonneg_left hRootSum
      (mul_nonneg hSpectralNonnegative hn)
  rw [hCross, hS, hT]
  nlinarith

omit [DecidableEq W] in
/-- A two-sided nontrivial spectral bound on the non-bipartite Cayley graph
implies the source's part-normalized mixing estimate on its double cover. -/
theorem rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
    (label : W → G) (spectral : ℝ)
    (hSymmetric : SmallSetExpansion.IsSymmetric (rightCayleyGraph label))
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph label) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) (Fintype.card W) spectral :=
  rightDoubleCoverGraph_hasPartiteExpanderMixingBound
    label (Fintype.card W) spectral hSpectralNonnegative
    (SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
      hSymmetric (rightCayleyGraph_isRegular label)
      hSpectralNonnegative hSpectral)

omit [DecidableEq G] in
/-- A part-normalized bipartite mixing estimate gives the exact PK22
small-set bound.  The double cover's second trivial mode is absorbed by the
density contribution `degree * radius / |G|`. -/
theorem HasPartiteExpanderMixingBound.toSmallSetEdgeExpanding
    {M : SmallSetExpansion.WeightedGraph (Fin 2 × G)}
    {degree radius : Nat} {spectral density : ℝ}
    (hMixing : HasPartiteExpanderMixingBound M degree spectral)
    (hDensity : (degree : ℝ) * radius ≤ density * Fintype.card G) :
    SmallSetExpansion.IsSmallSetEdgeExpanding M radius (spectral + density) := by
  intro S T hS hT
  let n : ℝ := Fintype.card G
  let s : ℝ := S.card
  let t : ℝ := T.card
  let x : ℝ := Real.sqrt (s * t)
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hs : s ≤ radius := by
    dsimp [s]
    exact_mod_cast hS
  have ht : t ≤ radius := by
    dsimp [t]
    exact_mod_cast hT
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = s * t := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hxRadius : x ≤ radius := by nlinarith
  have hProduct : s * t ≤ (radius : ℝ) * x := by nlinarith
  have hUniform : (degree : ℝ) * s * t ≤ density * n * x := by
    calc
      (degree : ℝ) * s * t ≤
          (degree : ℝ) * ((radius : ℝ) * x) := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hProduct (Nat.cast_nonneg degree))
      _ = ((degree : ℝ) * radius) * x := by ring
      _ ≤ (density * n) * x := by
        exact mul_le_mul_of_nonneg_right (by simpa [n] using hDensity) hx0
      _ = density * n * x := by ring
  have hMix := hMixing S T
  change n * (SmallSetExpansion.crossCount M S T : ℝ) ≤
    (degree : ℝ) * s * t + spectral * n * x at hMix
  change (SmallSetExpansion.crossCount M S T : ℝ) ≤
    (spectral + density) * x
  nlinarith

omit [DecidableEq W] in
/-- Source-compatible bipartite mixing input for the labelled right double
cover. -/
theorem rightDoubleCoverGraph_expanding_of_partiteMixingBound
    (label : W → G) (radius : Nat) (spectral density : ℝ)
    (hMixing : HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) (Fintype.card W) spectral)
    (hDensity : (Fintype.card W : ℝ) * radius ≤
      density * Fintype.card G) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius (spectral + density) :=
  hMixing.toSmallSetEdgeExpanding hDensity

omit [DecidableEq W] in
/-- An abstract full mean-zero bilinear bound on the labelled double cover
implies small-set expansion, with the density term explicit. A nonempty
bipartite double cover has a trivial side-sign eigenmode, so a subdegree
full mean-zero bound cannot serve as PK22's spectral input; use the
part-normalized mixing bridge above for that application. -/
theorem rightDoubleCoverGraph_expanding_of_bilinearBound
    (label : W → G) (radius : Nat) (spectral density : ℝ)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightDoubleCoverGraph label) spectral)
    (hDensity : (Fintype.card W : ℝ) * radius ≤
      density * Fintype.card (Fin 2 × G)) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius (spectral + density) := by
  exact
    (SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
      (rightDoubleCoverGraph_isSymmetric label)
      (rightDoubleCoverGraph_isRegular label)
      hSpectralNonnegative hSpectral).toSmallSetEdgeExpanding hDensity

omit [DecidableEq W] in
/-- An induced-edge estimate for small vertex sets implies the two-set mixing
bound consumed by the PK22 Tanner proof.  For a `|W|`-regular double cover the
resulting constant is `sqrt (2 c |W|)`. -/
theorem rightDoubleCoverGraph_expanding_of_internal_count
    (label : W → G) (radius : Nat) (internalConstant : ℝ)
    (hInternalNonnegative : 0 ≤ internalConstant)
    (hInternal : ∀ U : Finset (Fin 2 × G), U.card ≤ 2 * radius →
      (SmallSetExpansion.crossCount
        (rightDoubleCoverGraph label) U U : ℝ) ≤
          internalConstant * U.card) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius
      (Real.sqrt (2 * internalConstant * Fintype.card W)) := by
  exact SmallSetExpansion.IsSmallSetEdgeExpanding.of_internal_count
    (rightDoubleCoverGraph label) radius (Fintype.card W) internalConstant
    (rightDoubleCoverGraph_isSymmetric label)
    (rightDoubleCoverGraph_isRegular label)
    hInternalNonnegative hInternal

omit [Fintype G] [DecidableEq W] in
/-- Horizontal product adjacency is a disjoint union of right double covers. -/
theorem horizontalGraph_eq_relabel_disjointUnion (label : W → G) :
    horizontalGraph label =
      SmallSetExpansion.relabel horizontalFiberEquiv
        (SmallSetExpansion.disjointUnion
          (fun _ : Fin 2 => rightDoubleCoverGraph label)) := by
  funext v u
  rcases v with ⟨side, sideV, g⟩
  rcases u with ⟨side', sideV', g'⟩
  by_cases hSide : sideV = sideV'
  · subst sideV'
    simp [horizontalGraph, SmallSetExpansion.relabel,
      SmallSetExpansion.disjointUnion, horizontalFiberEquiv,
      rightDoubleCoverGraph, rightDoubleCoverNeighbor, horizontalNeighbor]
  · have hEmpty : (Finset.univ.filter fun a : W =>
        horizontalNeighbor label (side, sideV, g) a =
          (side', sideV', g')).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro a _ha hEq
      exact hSide (congrArg (fun z : VertexIndex G => z.2.1) hEq)
    simp [horizontalGraph, SmallSetExpansion.relabel,
      SmallSetExpansion.disjointUnion, horizontalFiberEquiv, hSide, hEmpty]

omit [Fintype G] [DecidableEq W] in
/-- Vertical product adjacency is a disjoint union of left double covers. -/
theorem verticalGraph_eq_relabel_disjointUnion (label : W → G) :
    verticalGraph label =
      SmallSetExpansion.relabel verticalFiberEquiv
        (SmallSetExpansion.disjointUnion
          (fun _ : Fin 2 => leftDoubleCoverGraph label)) := by
  funext v u
  rcases v with ⟨side, sideV, g⟩
  rcases u with ⟨side', sideV', g'⟩
  by_cases hSide : side = side'
  · subst side'
    simp [verticalGraph, SmallSetExpansion.relabel,
      SmallSetExpansion.disjointUnion, verticalFiberEquiv,
      leftDoubleCoverGraph, leftDoubleCoverNeighbor, verticalNeighbor]
  · have hEmpty : (Finset.univ.filter fun b : W =>
        verticalNeighbor label (side, sideV, g) b =
          (side', sideV', g')).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro b _hb hEq
      exact hSide (congrArg (fun z : VertexIndex G => z.1) hEq)
    simp [verticalGraph, SmallSetExpansion.relabel,
      SmallSetExpansion.disjointUnion, verticalFiberEquiv, hSide, hEmpty]

omit [Fintype G] [DecidableEq W] in
/-- The concrete adjacency graph is the union of its horizontal and vertical
parts. -/
theorem adjacencyGraph_eq_add (label : W → G) :
    adjacencyGraph label =
      SmallSetExpansion.add (horizontalGraph label) (verticalGraph label) := by
  rfl

omit [Fintype G] [DecidableEq W] in
/-- The horizontal-plus-vertical Tanner adjacency multigraph is symmetric. -/
theorem adjacencyGraph_isSymmetric (label : W → G) :
    SmallSetExpansion.IsSymmetric (adjacencyGraph label) := by
  have hHorizontal : SmallSetExpansion.IsSymmetric (horizontalGraph label) :=
    neighborGraph_isSymmetric (horizontalNeighbor label)
      (horizontalNeighbor_horizontalNeighbor label)
  have hVertical : SmallSetExpansion.IsSymmetric (verticalGraph label) :=
    neighborGraph_isSymmetric (verticalNeighbor label)
      (verticalNeighbor_verticalNeighbor label)
  intro v u
  rw [adjacencyGraph_eq_add]
  unfold SmallSetExpansion.add
  rw [hHorizontal v u, hVertical v u]

omit [DecidableEq W] in
/-- Every product vertex has `2 * |W|` outgoing adjacency directions,
counted with multiplicity. -/
theorem adjacencyGraph_isRegular (label : W → G) :
    SmallSetExpansion.IsRegular (adjacencyGraph label)
      (2 * Fintype.card W) := by
  intro v
  unfold adjacencyGraph
  rw [Finset.sum_add_distrib]
  have hHorizontal := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) (Finset.univ : Finset (VertexIndex G))
    (horizontalNeighbor label v)
  have hVertical := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) (Finset.univ : Finset (VertexIndex G))
    (verticalNeighbor label v)
  have hHorizontal' :
      (∑ x, (Finset.univ.filter fun a : W =>
        horizontalNeighbor label v a = x).card) = Fintype.card W := by
    simpa using hHorizontal
  have hVertical' :
      (∑ x, (Finset.univ.filter fun b : W =>
        verticalNeighbor label v b = x).card) = Fintype.card W := by
    simpa using hVertical
  calc
    (∑ x, (Finset.univ.filter fun a : W =>
        horizontalNeighbor label v a = x).card) +
        ∑ x, (Finset.univ.filter fun b : W =>
          verticalNeighbor label v b = x).card =
      Fintype.card W + Fintype.card W :=
        congrArg₂ (· + ·) hHorizontal' hVertical'
    _ = 2 * Fintype.card W := by omega

omit [Fintype G] in
/-- The physical vertical-edge face graph is a disjoint union, indexed by the
vertical local direction, of right double covers. -/
theorem verticalFaceGraph_eq_relabel_disjointUnion (label : W → G) :
    verticalFaceGraph label =
      SmallSetExpansion.relabel verticalEdgeFiberEquiv
        (SmallSetExpansion.disjointUnion
          (fun _ : W => rightDoubleCoverGraph label)) := by
  funext e e'
  rcases e with ⟨side, b, g⟩
  rcases e' with ⟨side', b', g'⟩
  by_cases hb : b = b'
  · subst b'
    fin_cases side <;> fin_cases side' <;>
      simp [verticalFaceGraph, SmallSetExpansion.relabel,
        SmallSetExpansion.disjointUnion, verticalEdgeFiberEquiv,
        rightDoubleCoverGraph, rightDoubleCoverNeighbor,
        verticalFaceNeighbor, verticalEdgeEndpoint, verticalEdgeAtVertex,
        horizontalNeighbor, doubleCoverVoltage, oppositeSide]
  · have hEmpty : (Finset.univ.filter fun a : W =>
        verticalFaceNeighbor label (side, b, g) a =
          (side', b', g')).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro a _ha hEq
      exact hb (congrArg (fun z : VerticalEdgeIndex W G => z.2.1) hEq)
    simp [verticalFaceGraph, SmallSetExpansion.relabel,
      SmallSetExpansion.disjointUnion, verticalEdgeFiberEquiv, hb, hEmpty]

omit [Fintype G] [DecidableEq W] in
/-- The two multiplication presentations have identical small-set expansion. -/
theorem leftDoubleCoverGraph_expanding
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (leftDoubleCoverGraph label) radius lambda := by
  rw [leftDoubleCoverGraph_eq_relabel]
  exact hBase.relabel sideInverseEquiv

omit [Fintype G] [DecidableEq W] in
/-- PK22 `lemma:expG'`: the product adjacency graph inherits twice the base
mixing constant. -/
theorem adjacencyGraph_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radius (2 * lambda) := by
  have hHorizontal : SmallSetExpansion.IsSmallSetEdgeExpanding
      (horizontalGraph label) radius lambda := by
    rw [horizontalGraph_eq_relabel_disjointUnion]
    exact (SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
      hLambda (fun _ => hBase)).relabel horizontalFiberEquiv
  have hVertical : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalGraph label) radius lambda := by
    rw [verticalGraph_eq_relabel_disjointUnion]
    exact (SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
      hLambda (fun _ => leftDoubleCoverGraph_expanding label radius lambda hBase)).relabel
        verticalFiberEquiv
  rw [adjacencyGraph_eq_add, show (2 : ℝ) * lambda = lambda + lambda by ring]
  exact hHorizontal.add hVertical

omit [DecidableEq W] in
/-- PK22 `lemma:expG''`, in a dyadic form: the square of product adjacency
has radius divided by `2 * |W|` and mixing constant
`8 * lambda² * (log₂(2|W|) + 1)`. -/
theorem adjacencySquare_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (SmallSetExpansion.square (adjacencyGraph label))
      (radius / (2 * Fintype.card W))
      (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) := by
  have hProduct := adjacencyGraph_expanding_of_doubleCover
    label radius lambda hLambda hBase
  have hSquare :=
    SmallSetExpansion.IsSmallSetEdgeExpanding.square_of_symmetric_regular
      (M := adjacencyGraph label) (degree := 2 * Fintype.card W)
      (lambda := 2 * lambda) (by positivity)
      (adjacencyGraph_isSymmetric label)
      (adjacencyGraph_isRegular label) hProduct
  convert hSquare using 1
  ring

omit [Fintype G] in
/-- The physical vertical-edge graph inherits the base mixing constant with
no loss in the number of local vertical directions. -/
theorem verticalFaceGraph_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda := by
  rw [verticalFaceGraph_eq_relabel_disjointUnion]
  exact (SmallSetExpansion.IsSmallSetEdgeExpanding.disjointUnion
    hLambda (fun _ => hBase)).relabel verticalEdgeFiberEquiv

omit [DecidableEq W] in
/-- Horizontal-then-vertical local face paths are the corresponding product
of the two one-step adjacency matrices. -/
theorem faceSquareGraph_eq_horizontal_vertical (label : W → G)
    (v u : VertexIndex G) :
    faceSquareGraph label v u =
      ∑ x, horizontalGraph label v x * verticalGraph label x u := by
  unfold faceSquareGraph horizontalGraph verticalGraph
  exact SmallSetExpansion.card_filter_product_eq_sum_card_fibers
    (fun a : W => horizontalNeighbor label v a)
    (fun x : VertexIndex G => fun b : W => verticalNeighbor label x b) u

omit [DecidableEq W] in
/-- The local face-path graph is a pointwise subgraph of the full square of
the horizontal-plus-vertical adjacency graph. -/
theorem faceSquareGraph_le_adjacencyGraph_square (label : W → G)
    (v u : VertexIndex G) :
    faceSquareGraph label v u ≤
      SmallSetExpansion.square (adjacencyGraph label) v u := by
  rw [faceSquareGraph_eq_horizontal_vertical]
  unfold SmallSetExpansion.square
  apply Finset.sum_le_sum
  intro x _hx
  apply Nat.mul_le_mul
  · exact Nat.le_add_right
      (horizontalGraph label v x) (verticalGraph label v x)
  · exact Nat.le_add_left
      (verticalGraph label x u) (horizontalGraph label x u)

omit [DecidableEq W] in
/-- Any small-set expansion bound for the full square adjacency graph applies
to the concrete horizontal-then-vertical face graph used by PK22. -/
theorem faceSquareGraph_expanding_of_adjacencySquare
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hSquare : SmallSetExpansion.IsSmallSetEdgeExpanding
      (SmallSetExpansion.square (adjacencyGraph label)) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radius lambda :=
  hSquare.of_pointwise_le (faceSquareGraph_le_adjacencyGraph_square label)

omit [DecidableEq W] in
/-- The concrete face graph receives the square-graph expansion bound needed
by the global labelled-set argument. -/
theorem faceSquareGraph_expanding_of_doubleCover
    (label : W → G) (radius : Nat) (lambda : ℝ)
    (hLambda : 0 ≤ lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) (radius / (2 * Fintype.card W))
      (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) :=
  faceSquareGraph_expanding_of_adjacencySquare label _ _
    (adjacencySquare_expanding_of_doubleCover
      label radius lambda hLambda hBase)

section GlobalZero

universe u

variable {F : Type u} {R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

/-- Source-shaped one-orientation PK22 zero lemma whose graph hypotheses have
all been discharged from one small-set expansion bound on the labelled Cayley
double cover. -/
theorem cycle_eq_zero_of_doubleCoverExpansion
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hBlockRadiusVertical :
      Fintype.card W * blockWeight c ≤ radius)
    (hBlockRadiusEdge : blockWeight c ≤ radius)
    (hBlockRadiusFace :
      blockWeight c ≤ radius / (2 * Fintype.card W))
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    c = 0 := by
  exact cycle_eq_zero_of_globalExpansion_of_blockWeight
    label h hRank g' gInjective c hcCycle hcLocal d m s beta
    hProductExpand hDistance hLength hTwo hFour hDistanceScale
    hRectangleScale hBudget
    radius lambda
    (verticalFaceGraph_expanding_of_doubleCover
      label radius lambda hLambda.le hBase)
    hBlockRadiusVertical hVerticalThreshold
    radius (radius / (2 * Fintype.card W))
    (2 * lambda)
    (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2))
    (by positivity) (by positivity)
    (adjacencyGraph_expanding_of_doubleCover
      label radius lambda hLambda.le hBase)
    (faceSquareGraph_expanding_of_doubleCover
      label radius lambda hLambda.le hBase)
    hBlockRadiusEdge hBlockRadiusFace hEdgeThreshold hFaceThreshold

end GlobalZero

end QEC.Coding.TannerLiftedProduct

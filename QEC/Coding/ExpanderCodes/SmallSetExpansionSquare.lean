import QEC.Coding.ExpanderCodes.SmallSetExpansion
import Mathlib.Data.Nat.Log

/-!
# Squaring a small-set expanding regular graph

This module proves a dyadic variant of the logarithmic-loss counting step in
PK22's `lemma:exp2`.  The proof uses dyadic level sets rather than sorting the
intermediate vertices.  Its `2 * lambda² * (log₂ degree + 1)` coefficient is
generally weaker than the source's literal `2 * lambda² * (1 + ln degree)`;
the literal source statement remains open.
-/

namespace QEC.Coding.SmallSetExpansion

universe u

variable {V : Type u}

/-- A weighted graph is symmetric when reversing an oriented edge preserves
its multiplicity. -/
def IsSymmetric (M : WeightedGraph V) : Prop :=
  ∀ v u, M v u = M u v

/-- A weighted graph is regular when every outgoing multiplicity sum has the
same value. -/
def IsRegular [Fintype V] (M : WeightedGraph V) (degree : Nat) : Prop :=
  ∀ v, ∑ u, M v u = degree

/-- Division-free expander-mixing estimate for a finite weighted graph.
The first term is the uniform-density contribution and `spectral` controls
the nonconstant contribution. -/
def HasExpanderMixingBound [Fintype V]
    (M : WeightedGraph V) (degree : Nat) (spectral : ℝ) : Prop :=
  ∀ S T : Finset V,
    (Fintype.card V : ℝ) * crossCount M S T ≤
      degree * (S.card : ℝ) * T.card +
        spectral * Fintype.card V *
          Real.sqrt ((S.card : ℝ) * T.card)

/-- The bilinear form of the unnormalized weighted adjacency operator. -/
noncomputable def adjacencyPairing [Fintype V]
    (M : WeightedGraph V) (f g : V → ℝ) : ℝ :=
  ∑ v, f v * ∑ u, (M v u : ℝ) * g u

/-- Action of the unnormalized weighted adjacency operator. -/
noncomputable def weightedNeighborSum [Fintype V]
    (M : WeightedGraph V) (g : V → ℝ) (v : V) : ℝ :=
  ∑ u, (M v u : ℝ) * g u

/-- A two-sided spectral bound on the mean-zero subspace.  Unlike a
one-sided Rayleigh estimate, this controls two different vertex indicators
and therefore implies the sharp two-set expander-mixing inequality. -/
def HasMeanZeroBilinearBound [Fintype V]
    (M : WeightedGraph V) (spectral : ℝ) : Prop :=
  ∀ f g : V → ℝ,
    (∑ v, f v) = 0 →
    (∑ v, g v) = 0 →
      |adjacencyPairing M f g| ≤
        spectral * Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2)

/-- Real-valued indicator of a finite vertex set. -/
noncomputable def vertexIndicator [DecidableEq V]
    (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then 1 else 0

/-- Division-free centered indicator `|V| 1_S - |S| 1`. -/
noncomputable def centeredVertexIndicator [Fintype V] [DecidableEq V]
    (S : Finset V) (v : V) : ℝ :=
  Fintype.card V * vertexIndicator S v - S.card

theorem sum_vertexIndicator [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, vertexIndicator S v = S.card := by
  classical
  change (∑ v ∈ Finset.univ, if v ∈ S then (1 : ℝ) else 0) = S.card
  rw [Finset.sum_boole]
  simp

theorem sum_centeredVertexIndicator [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, centeredVertexIndicator S v = 0 := by
  classical
  unfold centeredVertexIndicator
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator]
  simp

/-- Squared norm of a division-free centered indicator. -/
theorem sum_sq_centeredVertexIndicator [Fintype V] [DecidableEq V]
    (S : Finset V) :
    ∑ v, (centeredVertexIndicator S v) ^ 2 =
      (Fintype.card V : ℝ) * S.card *
        (Fintype.card V - S.card) := by
  classical
  let n : ℝ := Fintype.card V
  let s : ℝ := S.card
  have hsq (v : V) : (vertexIndicator S v) ^ 2 = vertexIndicator S v := by
    by_cases hv : v ∈ S <;> simp [vertexIndicator, hv]
  change (∑ v, (n * vertexIndicator S v - s) ^ 2) = n * s * (n - s)
  have hcross :
      (∑ v, 2 * (n * vertexIndicator S v) * s) = 2 * n * s * s := by
    calc
      (∑ v, 2 * (n * vertexIndicator S v) * s) =
          (2 * n * s) * ∑ v, vertexIndicator S v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 2 * n * s * s := by rw [sum_vertexIndicator]
  simp_rw [sub_sq, mul_pow, hsq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator]
  rw [hcross]
  simp [n, s]
  ring

/-- Pairing a centered indicator with an arbitrary real function. -/
theorem sum_centeredVertexIndicator_mul
    [Fintype V] [DecidableEq V]
    (S : Finset V) (h : V → ℝ) :
    (∑ v, centeredVertexIndicator S v * h v) =
      Fintype.card V * (∑ v ∈ S, h v) -
        S.card * ∑ v, h v := by
  classical
  simp_rw [centeredVertexIndicator, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [vertexIndicator, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff]
  simp

/-- Centering a target indicator turns its neighbor sum into discrepancy. -/
theorem weightedNeighborSum_centeredVertexIndicator
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (T : Finset V) (v : V) :
    weightedNeighborSum M (centeredVertexIndicator T) v =
      Fintype.card V * (∑ u ∈ T, (M v u : ℝ)) -
        degree * T.card := by
  classical
  have hDegree : (∑ u, (M v u : ℝ)) = degree := by
    exact_mod_cast hRegular v
  unfold weightedNeighborSum centeredVertexIndicator
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · calc
      (∑ u, (M v u : ℝ) *
          ((Fintype.card V : ℝ) * vertexIndicator T u)) =
          (Fintype.card V : ℝ) *
            ∑ u, (M v u : ℝ) * vertexIndicator T u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _hu
        ring
      _ = (Fintype.card V : ℝ) * ∑ u ∈ T, (M v u : ℝ) := by
        congr 1
        simp [vertexIndicator]
  · calc
      (∑ u, (M v u : ℝ) * (T.card : ℝ)) =
          (∑ u, (M v u : ℝ)) * T.card := by rw [Finset.sum_mul]
      _ = degree * T.card := by rw [hDegree]

/-- For a symmetric regular graph, the centered neighbor discrepancy has
total zero. -/
theorem sum_weightedNeighborSum_centeredVertexIndicator
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (T : Finset V) :
    ∑ v, weightedNeighborSum M (centeredVertexIndicator T) v = 0 := by
  classical
  rw [show
      (∑ v, weightedNeighborSum M (centeredVertexIndicator T) v) =
        ∑ u, centeredVertexIndicator T u * ∑ v, (M u v : ℝ) by
    unfold weightedNeighborSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [hSymm]
    ring]
  have hDegree (u : V) : (∑ v, (M u v : ℝ)) = degree := by
    exact_mod_cast hRegular u
  simp_rw [hDegree, ← Finset.sum_mul]
  rw [sum_centeredVertexIndicator, zero_mul]

/-- Exact discrepancy identity for two division-free centered indicators. -/
theorem adjacencyPairing_centeredVertexIndicator
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (S T : Finset V) :
    adjacencyPairing M
        (centeredVertexIndicator S) (centeredVertexIndicator T) =
      (Fintype.card V : ℝ) *
        ((Fintype.card V : ℝ) * crossCount M S T -
          degree * (S.card : ℝ) * T.card) := by
  classical
  rw [adjacencyPairing]
  change (∑ v, centeredVertexIndicator S v *
      weightedNeighborSum M (centeredVertexIndicator T) v) = _
  rw [sum_centeredVertexIndicator_mul]
  rw [sum_weightedNeighborSum_centeredVertexIndicator
    M degree hSymm hRegular T, mul_zero, sub_zero]
  simp_rw [weightedNeighborSum_centeredVertexIndicator
    M degree hRegular T]
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hCross :
      (∑ v ∈ S, ∑ u ∈ T, (M v u : ℝ)) =
        crossCount M S T := by
    norm_cast
  rw [hCross]
  ring

/-- A two-sided mean-zero spectral bound implies the sharp division-free
expander-mixing inequality.  The proof uses centered indicators, so the
spectral constant is preserved rather than square-root interpolated. -/
theorem HasMeanZeroBilinearBound.toExpanderMixingBound
    [Fintype V] [DecidableEq V] [Nonempty V]
    {M : WeightedGraph V} {degree : Nat} {spectral : ℝ}
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : HasMeanZeroBilinearBound M spectral) :
    HasExpanderMixingBound M degree spectral := by
  intro S T
  let n : ℝ := Fintype.card V
  let s : ℝ := S.card
  let t : ℝ := T.card
  let x : ℝ := Real.sqrt (s * t)
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hsn : s ≤ n := by
    dsimp [s, n]
    exact_mod_cast Finset.card_le_univ S
  have htn : t ≤ n := by
    dsimp [t, n]
    exact_mod_cast Finset.card_le_univ T
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = s * t := by
    dsimp [x]
    rw [Real.sq_sqrt]
    positivity
  have hComplement : (n - s) * (n - t) ≤ n * n := by
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hNormS :
      (∑ v, (centeredVertexIndicator S v) ^ 2) = n * s * (n - s) := by
    simpa [n, s] using sum_sq_centeredVertexIndicator S
  have hNormT :
      (∑ v, (centeredVertexIndicator T v) ^ 2) = n * t * (n - t) := by
    simpa [n, t] using sum_sq_centeredVertexIndicator T
  have hSqrtNorm :
      Real.sqrt
          ((∑ v, (centeredVertexIndicator S v) ^ 2) *
            ∑ v, (centeredVertexIndicator T v) ^ 2) ≤
        n ^ 2 * x := by
    rw [hNormS, hNormT]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        (n * s * (n - s)) * (n * t * (n - t)) =
            (n ^ 2 * (s * t)) * ((n - s) * (n - t)) := by ring
        _ ≤ (n ^ 2 * (s * t)) * (n * n) :=
          mul_le_mul_of_nonneg_left hComplement (by positivity)
        _ = (n ^ 2 * x) ^ 2 := by rw [← hx2]; ring
  have hBound := hSpectral
    (centeredVertexIndicator S) (centeredVertexIndicator T)
    (sum_centeredVertexIndicator S) (sum_centeredVertexIndicator T)
  rw [adjacencyPairing_centeredVertexIndicator
    M degree hSymm hRegular S T] at hBound
  have hPairUpper :
      n * (n * (crossCount M S T : ℝ) -
          degree * s * t) ≤
        spectral *
          Real.sqrt
            ((∑ v, (centeredVertexIndicator S v) ^ 2) *
              ∑ v, (centeredVertexIndicator T v) ^ 2) := by
    exact (le_abs_self _).trans (by simpa [n, s, t] using hBound)
  have hSharp :
      n * (n * (crossCount M S T : ℝ) - degree * s * t) ≤
        spectral * (n ^ 2 * x) :=
    hPairUpper.trans
      (mul_le_mul_of_nonneg_left hSqrtNorm hSpectralNonnegative)
  change n * (crossCount M S T : ℝ) ≤
    (degree : ℝ) * s * t + spectral * n * x
  nlinarith

/-- An expander-mixing estimate gives the PK22 small-set bound.  If the
uniform-density term obeys `degree * radius / |V| ≤ density`, the resulting
mixing constant is `spectral + density`. -/
theorem HasExpanderMixingBound.toSmallSetEdgeExpanding
    [Fintype V] [Nonempty V]
    {M : WeightedGraph V} {degree radius : Nat} {spectral density : ℝ}
    (hMixing : HasExpanderMixingBound M degree spectral)
    (hDensity : (degree : ℝ) * radius ≤ density * Fintype.card V) :
    IsSmallSetEdgeExpanding M radius (spectral + density) := by
  intro S T hS hT
  let n : ℝ := Fintype.card V
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
      (degree : ℝ) * s * t ≤ (degree : ℝ) * ((radius : ℝ) * x) := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hProduct (Nat.cast_nonneg degree))
      _ = ((degree : ℝ) * radius) * x := by ring
      _ ≤ (density * n) * x := by
        exact mul_le_mul_of_nonneg_right (by simpa [n] using hDensity) hx0
      _ = density * n * x := by ring
  have hMix := hMixing S T
  change n * (crossCount M S T : ℝ) ≤
    (degree : ℝ) * s * t + spectral * n * x at hMix
  change (crossCount M S T : ℝ) ≤ (spectral + density) * x
  nlinarith

/-- Cross counts are monotone in both selected vertex sets. -/
theorem crossCount_mono_sets [DecidableEq V]
    (M : WeightedGraph V) {S S' T T' : Finset V}
    (hS : S ⊆ S') (hT : T ⊆ T') :
    crossCount M S T ≤ crossCount M S' T' := by
  unfold crossCount
  calc
    (∑ v ∈ S, ∑ u ∈ T, M v u) ≤
        ∑ v ∈ S, ∑ u ∈ T', M v u := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Finset.sum_le_sum_of_subset hT
    _ ≤ ∑ v ∈ S', ∑ u ∈ T', M v u :=
      Finset.sum_le_sum_of_subset hS

/-- A symmetric weighted graph has symmetric cross counts. -/
theorem crossCount_comm_of_symmetric [DecidableEq V]
    (M : WeightedGraph V) (hSymm : IsSymmetric M)
    (S T : Finset V) :
    crossCount M S T = crossCount M T S := by
  unfold crossCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro v _hv
  exact hSymm v u

/-- In a regular weighted graph, at most `degree |S|` oriented edges leave
`S`, even after restricting their endpoints to an arbitrary set `T`. -/
theorem crossCount_le_degree_mul_card_left [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (S T : Finset V) :
    crossCount M S T ≤ degree * S.card := by
  unfold crossCount
  calc
    (∑ v ∈ S, ∑ u ∈ T, M v u) ≤
        ∑ v ∈ S, ∑ u, M v u := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    _ = ∑ _v ∈ S, degree := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact hRegular v
    _ = degree * S.card := by simp [Nat.mul_comm]

/-- Internal-edge control plus regularity upgrades to a two-set small-set
mixing estimate.  This is the elementary square-root interpolation used to
turn an Alon--Chung bound for `U` into the PK22 cross-count bound for `S,T`.

The internal estimate is requested at radius `2 * radius`, because it is
applied to `S ∪ T`. -/
theorem IsSmallSetEdgeExpanding.of_internal_count
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (radius degree : Nat) (internalConstant : ℝ)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hInternalNonnegative : 0 ≤ internalConstant)
    (hInternal : ∀ U : Finset V, U.card ≤ 2 * radius →
      (crossCount M U U : ℝ) ≤ internalConstant * U.card) :
    IsSmallSetEdgeExpanding M radius
      (Real.sqrt (2 * internalConstant * degree)) := by
  intro S T hS hT
  have hFactorNonnegative : 0 ≤ 2 * internalConstant * (degree : ℝ) := by
    positivity
  have bound_when_card_le
      (A B : Finset V) (hA : A.card ≤ radius) (hB : B.card ≤ radius)
      (hAB : A.card ≤ B.card) :
      (crossCount M A B : ℝ) ≤
        Real.sqrt (2 * internalConstant * degree) *
          Real.sqrt ((A.card : ℝ) * B.card) := by
    have hDegreeNat := crossCount_le_degree_mul_card_left
      M degree hRegular A B
    have hDegree : (crossCount M A B : ℝ) ≤
        (degree : ℝ) * A.card := by
      exact_mod_cast hDegreeNat
    have hUnionAB : (A ∪ B).card ≤ 2 * radius := by
      calc
        (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
        _ ≤ radius + radius := Nat.add_le_add hA hB
        _ = 2 * radius := by omega
    have hABUnionNat :
        crossCount M A B ≤ crossCount M (A ∪ B) (A ∪ B) :=
      crossCount_mono_sets M Finset.subset_union_left Finset.subset_union_right
    have hABUnion : (crossCount M A B : ℝ) ≤
        internalConstant * (A ∪ B).card :=
      (Nat.cast_le.mpr hABUnionNat).trans (hInternal (A ∪ B) hUnionAB)
    have hUnionLe : ((A ∪ B).card : ℝ) ≤ 2 * B.card := by
      exact_mod_cast (Finset.card_union_le A B).trans (by omega)
    have hInternalB : (crossCount M A B : ℝ) ≤
        2 * internalConstant * B.card := by
      calc
        (crossCount M A B : ℝ) ≤
            internalConstant * (A ∪ B).card := hABUnion
        _ ≤ internalConstant * (2 * B.card) :=
          mul_le_mul_of_nonneg_left hUnionLe hInternalNonnegative
        _ = 2 * internalConstant * B.card := by ring
    have hSquare : (crossCount M A B : ℝ) ^ 2 ≤
        (2 * internalConstant * degree) *
          ((A.card : ℝ) * B.card) := by
      calc
        (crossCount M A B : ℝ) ^ 2 =
            (crossCount M A B : ℝ) * crossCount M A B := by ring
        _ ≤ ((degree : ℝ) * A.card) *
            (2 * internalConstant * B.card) :=
          mul_le_mul hDegree hInternalB (Nat.cast_nonneg _) (by positivity)
        _ = (2 * internalConstant * degree) *
            ((A.card : ℝ) * B.card) := by ring
    have hSqrt : (crossCount M A B : ℝ) ≤
        Real.sqrt ((2 * internalConstant * degree) *
          ((A.card : ℝ) * B.card)) :=
      Real.le_sqrt_of_sq_le hSquare
    rw [Real.sqrt_mul hFactorNonnegative] at hSqrt
    exact hSqrt
  by_cases hST : S.card ≤ T.card
  · exact bound_when_card_le S T hS hT hST
  · rw [crossCount_comm_of_symmetric M hSymm S T]
    have hTS : T.card ≤ S.card := Nat.le_of_not_ge hST
    simpa [mul_comm] using bound_when_card_le T S hT hS hTS

/-- Incoming multiplicity from a vertex set to one intermediate vertex. -/
def incomingCount (M : WeightedGraph V) (S : Finset V) (x : V) : Nat :=
  ∑ v ∈ S, M v x

/-- Outgoing multiplicity from one intermediate vertex to a vertex set. -/
def outgoingCount (M : WeightedGraph V) (T : Finset V) (x : V) : Nat :=
  ∑ u ∈ T, M x u

/-- Intermediate vertices reached with positive multiplicity from `S`. -/
def intermediateSupport [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter fun x => incomingCount M S x ≠ 0

/-- Cross counts in the square graph group length-two paths by their
intermediate vertex. -/
theorem crossCount_square [Fintype V]
    (M : WeightedGraph V) (S T : Finset V) :
    crossCount (square M) S T =
      ∑ x, incomingCount M S x * outgoingCount M T x := by
  simp only [crossCount, square, incomingCount, outgoingCount]
  calc
    (∑ v ∈ S, ∑ u ∈ T, ∑ x, M v x * M x u) =
        ∑ v ∈ S, ∑ x, ∑ u ∈ T, M v x * M x u := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact Finset.sum_comm
    _ = ∑ x, ∑ v ∈ S, ∑ u ∈ T, M v x * M x u :=
      Finset.sum_comm
    _ = ∑ x, (∑ v ∈ S, M v x) * ∑ u ∈ T, M x u := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]

/-- Incoming mass becomes an ordinary cross count when the graph is
symmetric. -/
theorem sum_incomingCount_eq_crossCount
    (M : WeightedGraph V) (hSymm : IsSymmetric M)
    (S A : Finset V) :
    (∑ x ∈ A, incomingCount M S x) = crossCount M A S := by
  simp only [incomingCount, crossCount]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro v _hv
  exact hSymm v x

/-- Outgoing mass over a set is its cross count. -/
theorem sum_outgoingCount_eq_crossCount
    (M : WeightedGraph V) (A T : Finset V) :
    (∑ x ∈ A, outgoingCount M T x) = crossCount M A T := by
  rfl

/-- In a symmetric regular graph, incoming multiplicity from any subset is
bounded by the degree. -/
theorem incomingCount_le_degree
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (S : Finset V) (x : V) :
    incomingCount M S x ≤ degree := by
  calc
    incomingCount M S x = ∑ v ∈ S, M x v := by
      unfold incomingCount
      apply Finset.sum_congr rfl
      intro v _hv
      exact hSymm v x
    _ ≤ ∑ v, M x v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun _ _ _ => Nat.zero_le _)
    _ = degree := hRegular x

/-- The number of intermediate vertices reached from `S` is at most degree
times `|S|`. -/
theorem card_intermediateSupport_le
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (degree : Nat) (hRegular : IsRegular M degree)
    (S : Finset V) :
    (intermediateSupport M S).card ≤ degree * S.card := by
  let U := intermediateSupport M S
  calc
    U.card = ∑ _x ∈ U, 1 := by simp
    _ ≤ ∑ x ∈ U, incomingCount M S x := by
      apply Finset.sum_le_sum
      intro x hx
      have hxNe : incomingCount M S x ≠ 0 := (Finset.mem_filter.mp hx).2
      omega
    _ ≤ ∑ x, incomingCount M S x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        (fun _ _ _ => Nat.zero_le _)
    _ = degree * S.card := by
      unfold incomingCount
      rw [Finset.sum_comm]
      calc
        (∑ v ∈ S, ∑ x, M v x) = ∑ _v ∈ S, degree := by
          apply Finset.sum_congr rfl
          intro v _hv
          exact hRegular v
        _ = degree * S.card := by simp [Nat.mul_comm]

/-- Terms outside the intermediate support vanish. -/
theorem sum_mul_over_intermediateSupport
    [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (S T : Finset V) :
    (∑ x, incomingCount M S x * outgoingCount M T x) =
      ∑ x ∈ intermediateSupport M S,
        incomingCount M S x * outgoingCount M T x := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _hxUniv hxSupport
  have hxZero : incomingCount M S x = 0 := by
    simpa [intermediateSupport] using hxSupport
  simp [hxZero]

/-- Dyadic form of the PK22 intermediate-vertex count.  If every subset of
`U` has both `p`- and `q`-mass bounded by the two mixing estimates, and
`1 ≤ p x ≤ degree` on `U`, then the sum of `p x * q x` loses only the number
of dyadic degree levels. -/
theorem sum_mul_le_of_dyadic_mixing
    [Fintype V] [DecidableEq V]
    (p q : V → Nat) (U : Finset V) (degree : Nat) (lambda : ℝ)
    (sCard tCard : Nat)
    (hLambda : 0 ≤ lambda)
    (hPPos : ∀ x ∈ U, 0 < p x)
    (hPBound : ∀ x ∈ U, p x ≤ degree)
    (hPMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (p x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * sCard))
    (hQMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (q x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * tCard)) :
    (∑ x ∈ U, ((p x * q x : Nat) : ℝ)) ≤
      ((Nat.log 2 degree + 1 : Nat) : ℝ) *
        (2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)) := by
  let level : V → Nat := fun x => Nat.log 2 (p x)
  let levels := Finset.range (Nat.log 2 degree + 1)
  have hLevel : ∀ x ∈ U, level x ∈ levels := by
    intro x hx
    simp only [level, levels, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hPBound x hx))
  rw [← Finset.sum_fiberwise_of_maps_to hLevel
    (fun x => ((p x * q x : Nat) : ℝ))]
  calc
    (∑ k ∈ levels, ∑ x ∈ U with level x = k,
        ((p x * q x : Nat) : ℝ)) ≤
        ∑ _k ∈ levels,
          2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard) := by
      apply Finset.sum_le_sum
      intro k hk
      let A := U.filter fun x => level x = k
      have hAU : A ⊆ U := Finset.filter_subset _ _
      have hLowerNat : 2 ^ k * A.card ≤ ∑ x ∈ A, p x := by
        calc
          2 ^ k * A.card = ∑ _x ∈ A, 2 ^ k := by
            simp [Nat.mul_comm]
          _ ≤ ∑ x ∈ A, p x := by
            apply Finset.sum_le_sum
            intro x hx
            have hxU := hAU hx
            have hxLevel : level x = k := (Finset.mem_filter.mp hx).2
            rw [← hxLevel]
            exact Nat.pow_log_le_self 2 (Nat.ne_of_gt (hPPos x hxU))
      have hUpperNat : ∑ x ∈ A, p x * q x ≤
          2 ^ (k + 1) * ∑ x ∈ A, q x := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        apply Nat.mul_le_mul_right
        have hxU := hAU hx
        have hxLevel : level x = k := (Finset.mem_filter.mp hx).2
        exact Nat.le_of_lt (by
          rw [← hxLevel]
          exact Nat.lt_pow_succ_log_self (by omega : 1 < 2) (p x))
      have hPMixA := hPMix A hAU
      have hQMixA := hQMix A hAU
      change (∑ x ∈ A, ((p x * q x : Nat) : ℝ)) ≤
        2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)
      by_cases hAEmpty : A = ∅
      · simp only [hAEmpty, Finset.sum_empty]
        positivity
      have hACardPosNat : 0 < A.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hAEmpty)
      have hACardPos : (0 : ℝ) < A.card := by exact_mod_cast hACardPosNat
      have hRootAPos : 0 < Real.sqrt (A.card : ℝ) :=
        Real.sqrt_pos.2 hACardPos
      have hLower : ((2 ^ k : Nat) : ℝ) * A.card ≤
          ∑ x ∈ A, (p x : ℝ) := by exact_mod_cast hLowerNat
      have hUpper : (∑ x ∈ A, ((p x * q x : Nat) : ℝ)) ≤
          ((2 ^ (k + 1) : Nat) : ℝ) * ∑ x ∈ A, (q x : ℝ) := by
        exact_mod_cast hUpperNat
      have hRootASq : Real.sqrt (A.card : ℝ) ^ 2 = A.card :=
        Real.sq_sqrt (Nat.cast_nonneg _)
      have hPAfterRoot : ((2 ^ k : Nat) : ℝ) * Real.sqrt A.card ≤
          lambda * Real.sqrt sCard := by
        have hCombined : ((2 ^ k : Nat) : ℝ) * A.card ≤
            lambda * (Real.sqrt A.card * Real.sqrt sCard) := by
          calc
            ((2 ^ k : Nat) : ℝ) * A.card ≤
                ∑ x ∈ A, (p x : ℝ) := hLower
            _ ≤ lambda * Real.sqrt ((A.card : ℝ) * sCard) := hPMixA
            _ = lambda * (Real.sqrt A.card * Real.sqrt sCard) := by
              rw [Real.sqrt_mul (Nat.cast_nonneg A.card)]
        apply (mul_le_mul_iff_of_pos_right hRootAPos).mp
        calc
          ((2 ^ k : Nat) : ℝ) * Real.sqrt A.card * Real.sqrt A.card =
              ((2 ^ k : Nat) : ℝ) * (Real.sqrt A.card) ^ 2 := by ring
          _ = ((2 ^ k : Nat) : ℝ) * A.card := by rw [hRootASq]
          _ ≤ lambda * (Real.sqrt A.card * Real.sqrt sCard) := hCombined
          _ = lambda * Real.sqrt sCard * Real.sqrt A.card := by ring
      calc
        (∑ x ∈ A, ((p x * q x : Nat) : ℝ)) ≤
            ((2 ^ (k + 1) : Nat) : ℝ) * ∑ x ∈ A, (q x : ℝ) := hUpper
        _ = (2 * ((2 ^ k : Nat) : ℝ)) * ∑ x ∈ A, (q x : ℝ) := by
          norm_num [Nat.pow_succ, mul_comm]
        _ ≤ (2 * ((2 ^ k : Nat) : ℝ)) *
            (lambda * Real.sqrt ((A.card : ℝ) * tCard)) :=
          mul_le_mul_of_nonneg_left hQMixA (by positivity)
        _ = (2 * lambda * Real.sqrt tCard) *
            (((2 ^ k : Nat) : ℝ) * Real.sqrt A.card) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg A.card)]
          ring
        _ ≤ (2 * lambda * Real.sqrt tCard) *
            (lambda * Real.sqrt sCard) := by
          exact mul_le_mul_of_nonneg_left hPAfterRoot
            (mul_nonneg (mul_nonneg (by positivity) hLambda)
              (Real.sqrt_nonneg _))
        _ = 2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg sCard)]
          ring
    _ = ((Nat.log 2 degree + 1 : Nat) : ℝ) *
        (2 * lambda ^ 2 * Real.sqrt ((sCard : ℝ) * tCard)) := by
      simp [levels]

/-- An internal dyadic variant of PK22's `lemma:exp2`.  Squaring a symmetric
regular small-set expander shrinks the radius by the degree and incurs a
`2 * lambda² * (log₂ degree + 1)` mixing constant.  This does not establish
the literal source coefficient `2 * lambda² * (1 + ln degree)`. -/
theorem IsSmallSetEdgeExpanding.square_of_symmetric_regular
    [Fintype V] [DecidableEq V]
    {M : WeightedGraph V} {radius degree : Nat} {lambda : ℝ}
    (hLambda : 0 ≤ lambda)
    (hSymm : IsSymmetric M) (hRegular : IsRegular M degree)
    (hExpand : IsSmallSetEdgeExpanding M radius lambda) :
    IsSmallSetEdgeExpanding (square M) (radius / degree)
      (((Nat.log 2 degree + 1 : Nat) : ℝ) * (2 * lambda ^ 2)) := by
  intro S T hS hT
  let p : V → Nat := incomingCount M S
  let q : V → Nat := outgoingCount M T
  let U : Finset V := intermediateSupport M S
  have hSRadius : S.card ≤ radius :=
    hS.trans (Nat.div_le_self radius degree)
  have hTRadius : T.card ≤ radius :=
    hT.trans (Nat.div_le_self radius degree)
  have hUCard : U.card ≤ radius := by
    calc
      U.card ≤ degree * S.card := card_intermediateSupport_le M degree hRegular S
      _ ≤ degree * (radius / degree) := Nat.mul_le_mul_left degree hS
      _ ≤ radius := Nat.mul_div_le radius degree
  have hPPos : ∀ x ∈ U, 0 < p x := by
    intro x hx
    have hxNe : incomingCount M S x ≠ 0 := (Finset.mem_filter.mp hx).2
    exact Nat.pos_of_ne_zero hxNe
  have hPBound : ∀ x ∈ U, p x ≤ degree := by
    intro x _hx
    exact incomingCount_le_degree M degree hSymm hRegular S x
  have hPMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (p x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * S.card) := by
    intro A hAU
    have hACard : A.card ≤ radius :=
      (Finset.card_le_card hAU).trans hUCard
    have hEq : (∑ x ∈ A, (p x : ℝ)) =
        (crossCount M A S : ℝ) := by
      exact_mod_cast sum_incomingCount_eq_crossCount M hSymm S A
    rw [hEq]
    exact hExpand A S hACard hSRadius
  have hQMix : ∀ A : Finset V, A ⊆ U →
      (∑ x ∈ A, (q x : ℝ)) ≤
        lambda * Real.sqrt ((A.card : ℝ) * T.card) := by
    intro A hAU
    have hACard : A.card ≤ radius :=
      (Finset.card_le_card hAU).trans hUCard
    have hEq : (∑ x ∈ A, (q x : ℝ)) =
        (crossCount M A T : ℝ) := by
      exact_mod_cast sum_outgoingCount_eq_crossCount M A T
    rw [hEq]
    exact hExpand A T hACard hTRadius
  have hDyadic := sum_mul_le_of_dyadic_mixing p q U degree lambda
    S.card T.card hLambda hPPos hPBound hPMix hQMix
  have hCross : (crossCount (square M) S T : ℝ) =
      ∑ x ∈ U, ((p x * q x : Nat) : ℝ) := by
    rw [crossCount_square, sum_mul_over_intermediateSupport, Nat.cast_sum]
  rw [hCross]
  calc
    (∑ x ∈ U, ((p x * q x : Nat) : ℝ)) ≤
        ((Nat.log 2 degree + 1 : Nat) : ℝ) *
          (2 * lambda ^ 2 * Real.sqrt ((S.card : ℝ) * T.card)) := hDyadic
    _ = (((Nat.log 2 degree + 1 : Nat) : ℝ) * (2 * lambda ^ 2)) *
        Real.sqrt ((S.card : ℝ) * T.card) := by ring

end QEC.Coding.SmallSetExpansion

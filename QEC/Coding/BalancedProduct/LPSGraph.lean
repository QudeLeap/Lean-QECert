import QEC.Coding.BalancedProduct.LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic

/-!
# The concrete BE20 LPS Cayley graph

The paper uses edges `g -- s g` and lets the upper-unipotent subgroup act on
the right.  We keep that orientation explicitly, rather than silently swapping
to Mathlib's right-generator convention.
-/

open scoped MatrixGroups

namespace QEC.Coding.BalancedProduct.LPSGraph

open Matrix
open LPSArithmetic LPSGenerators

/-- The concrete LPS vertex type is finite for every prime modulus. -/
noncomputable instance pglFintype401 (q : ℕ) [Fact q.Prime] :
    Fintype (PGL(2, ZMod q)) := by
  classical
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI : Fintype (GL (Fin 2) (ZMod q)) :=
    Fintype.ofInjective Units.val Units.val_injective
  exact Fintype.ofSurjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective

/-- The source-oriented LPS graph: a directed presentation `w = s g` is
symmetrized by `SimpleGraph.fromRel`. -/
noncomputable def lpsCayleyGraph401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    SimpleGraph PGL(2, ZMod q) :=
  SimpleGraph.fromRel fun g w =>
    ∃ s ∈ lpsGenerators401 q hq, s * g = w

theorem one_not_mem_lpsGenerators401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    (1 : PGL(2, ZMod q)) ∉ lpsGenerators401 q hq := by
  intro hone
  have hnonsquare :=
    not_projectiveDetIsSquare_of_mem_lpsGenerators401 q hq hone
  apply hnonsquare
  simpa using
    (projectiveDetIsSquare_upperUnipotent (R := ZMod q) (0 : ZMod q))

theorem lpsCayleyGraph401_adj_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g w : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).Adj g w ↔
      ∃ s ∈ lpsGenerators401 q hq, s * g = w := by
  rw [lpsCayleyGraph401, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨s, hs, hsg⟩ | ⟨s, hs, hsw⟩⟩
    · exact ⟨s, hs, hsg⟩
    · refine ⟨s⁻¹, inv_mem_lpsGenerators401_of_mem q hq hs, ?_⟩
      rw [← hsw]
      simp
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, Or.inl ⟨s, hs, rfl⟩⟩
    intro heq
    have hsone : s = 1 := by
      apply mul_right_cancel (b := g)
      simpa using heq
    exact one_not_mem_lpsGenerators401 q hq (hsone ▸ hs)

/-- The explicit neighbor finset at `g`. -/
noncomputable def lpsNeighbors401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) : Finset PGL(2, ZMod q) := by
  classical
  exact (lpsGenerators401 q hq).image fun s => s * g

theorem mem_lpsNeighbors401_iff_adj
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g w : PGL(2, ZMod q)) :
    w ∈ lpsNeighbors401 q hq g ↔
      (lpsCayleyGraph401 q hq).Adj g w := by
  classical
  rw [lpsCayleyGraph401_adj_iff]
  constructor
  · intro hw
    change w ∈ (lpsGenerators401 q hq).image (fun s => s * g) at hw
    rcases Finset.mem_image.mp hw with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    change s * g ∈ (lpsGenerators401 q hq).image (fun a => a * g)
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩

theorem card_lpsNeighbors401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsNeighbors401 q hq g).card = 402 := by
  classical
  rw [lpsNeighbors401, Finset.card_image_of_injective]
  · exact card_lpsGenerators401 q hq40 hq
  · intro s t h
    exact mul_right_cancel h

/-- Right multiplication commutes with every source-oriented LPS edge. -/
theorem lpsCayleyGraph401_adj_mul_right_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g w h : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).Adj (g * h) (w * h) ↔
      (lpsCayleyGraph401 q hq).Adj g w := by
  simp only [lpsCayleyGraph401_adj_iff]
  constructor
  · rintro ⟨s, hs, hsw⟩
    refine ⟨s, hs, ?_⟩
    apply mul_right_cancel (b := h)
    simpa [mul_assoc] using hsw
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, by simp [mul_assoc]⟩

/-- The graph automorphism induced by right multiplication. -/
noncomputable def lpsRightIso401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (h : PGL(2, ZMod q)) :
    lpsCayleyGraph401 q hq ≃g lpsCayleyGraph401 q hq where
  toEquiv := Equiv.mulRight h
  map_rel_iff' := by
    intro g w
    exact lpsCayleyGraph401_adj_mul_right_iff q hq g w h

/-- The upper-unipotent right action is free on genuine unoriented LPS edges.
The endpoint-preserving branch reduces to vertex freeness.  The endpoint-swap
branch would put an LPS generator in a conjugate of the upper-unipotent
subgroup, contradicting the proved determinant square class. -/
theorem upperUnipotent_edge_fixed_iff_one
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {g w : PGL(2, ZMod q)}
    (hgw : (lpsCayleyGraph401 q hq).Adj g w)
    (h : upperUnipotentSubgroup (R := ZMod q)) :
    s(g * (h : PGL(2, ZMod q)), w * (h : PGL(2, ZMod q))) = s(g, w) ↔
      h = 1 := by
  constructor
  · intro hedge
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨hg, _⟩ | ⟨hgwSwap, _⟩
    · exact (right_mul_eq_self_iff g h).mp hg
    · rcases (lpsCayleyGraph401_adj_iff q hq g w).mp hgw with
        ⟨s, hs, hsg⟩
      rcases (mem_upperUnipotentSubgroup_iff
        (R := ZMod q) (h : PGL(2, ZMod q))).mp h.property with ⟨x, hx⟩
      have hconj : s = g * upperUnipotentPGL x * g⁻¹ := by
        rw [hx]
        apply mul_right_cancel (b := g)
        calc
          s * g = w := hsg
          _ = g * (h : PGL(2, ZMod q)) := hgwSwap.symm
          _ = (g * (h : PGL(2, ZMod q)) * g⁻¹) * g := by simp [mul_assoc]
      exact (lpsGenerators401_ne_conj_upperUnipotent q hq hs g x hconj).elim
  · rintro rfl
    simp

/-! ## Approved external LPS boundary -/

/-- The adjacency Rayleigh quadratic form of the actual source-oriented LPS
graph.  It is deliberately defined from the proved neighbor finsets, so the
external boundary receives neither an adjacency matrix nor any extra graph
data. -/
noncomputable def adjacencyRayleigh401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (f : PGL(2, ZMod q) → ℝ) : ℝ :=
  ∑ v, f v * ∑ w ∈ lpsNeighbors401 q hq v, f w

/-- The sole approved external premise for the conditional BE20 endpoint.

This is the connectedness conclusion and the one-sided rationalized spectral
bound `lambda₂ ≤ 401 / 10` for the concrete graph `X_{401,q}`.  The one-sided
Rayleigh form correctly permits the bipartite trivial eigenvalue `-402`.
Every Tanner, distance, locality, and asymptotic consequence must be derived
from this graph-only proposition in Lean. -/
def LPS401RayleighBound
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) : Prop :=
  (lpsCayleyGraph401 q hq).Connected ∧
    ∀ f : PGL(2, ZMod q) → ℝ,
      (∑ v, f v) = 0 →
      10 * adjacencyRayleigh401 q hq f ≤
        401 * ∑ v, (f v) ^ 2

/-! ## Spectral-to-combinatorial interface -/

/-- Real-valued indicator of a finite vertex set. -/
noncomputable def vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) : ℝ := by
  classical
  exact if v ∈ S then 1 else 0

theorem vertexIndicator401_of_mem
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    {v : PGL(2, ZMod q)} (hv : v ∈ S) :
    vertexIndicator401 q S v = 1 := by
  classical
  change (if v ∈ S then (1 : ℝ) else 0) = 1
  rw [if_pos hv]

theorem vertexIndicator401_of_not_mem
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    {v : PGL(2, ZMod q)} (hv : v ∉ S) :
    vertexIndicator401 q S v = 0 := by
  classical
  change (if v ∈ S then (1 : ℝ) else 0) = 0
  rw [if_neg hv]

/-- The mean-zero, division-free centering of a vertex-set indicator:
`|V| 1_S - |S| 1`. -/
noncomputable def centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) : ℝ :=
  Fintype.card (PGL(2, ZMod q)) * vertexIndicator401 q S v - S.card

/-- Directed adjacency incidences with both endpoints in `S`.  Every genuine
undirected induced edge contributes twice. -/
noncomputable def lpsNeighborsIn401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) : Finset (PGL(2, ZMod q)) := by
  classical
  exact (lpsNeighbors401 q hq v).filter (· ∈ S)

/-- Directed adjacency incidences with both endpoints in `S`.  Every genuine
undirected induced edge contributes twice. -/
noncomputable def insideAdjacencyCount401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) : ℕ := by
  classical
  exact ∑ v ∈ S, (lpsNeighborsIn401 q hq S v).card

theorem sum_vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, vertexIndicator401 q S v = S.card := by
  classical
  change (∑ v ∈ Finset.univ, if v ∈ S then (1 : ℝ) else 0) = S.card
  rw [Finset.sum_boole]
  simp

theorem sum_centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, centeredVertexIndicator401 q S v = 0 := by
  classical
  unfold centeredVertexIndicator401
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator401]
  simp

theorem sum_neighbor_vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) :
    ∑ w ∈ lpsNeighbors401 q hq v, vertexIndicator401 q S w =
      (lpsNeighborsIn401 q hq S v).card := by
  classical
  unfold lpsNeighborsIn401
  change
    (∑ w ∈ lpsNeighbors401 q hq v,
      if w ∈ S then (1 : ℝ) else 0) =
        ((lpsNeighbors401 q hq v).filter (· ∈ S)).card
  rw [Finset.sum_boole]

theorem adjacencyRayleigh_vertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    adjacencyRayleigh401 q hq (vertexIndicator401 q S) =
      insideAdjacencyCount401 q hq S := by
  classical
  rw [adjacencyRayleigh401, insideAdjacencyCount401]
  simp_rw [sum_neighbor_vertexIndicator401]
  push_cast
  calc
    (∑ v,
        vertexIndicator401 q S v *
          ((lpsNeighborsIn401 q hq S v).card : ℝ)) =
        ∑ v ∈ S,
          vertexIndicator401 q S v *
            ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v _hvUniv hvS
      rw [vertexIndicator401_of_not_mem q S hvS, zero_mul]
    _ = ∑ v ∈ S, ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hvS
      rw [vertexIndicator401_of_mem q S hvS, one_mul]

/-- Squared norm of the division-free centered indicator. -/
theorem sum_sq_centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, (centeredVertexIndicator401 q S v) ^ 2 =
      (Fintype.card (PGL(2, ZMod q)) : ℝ) * S.card *
        (Fintype.card (PGL(2, ZMod q)) - S.card) := by
  classical
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  have hsq (v : PGL(2, ZMod q)) :
      (vertexIndicator401 q S v) ^ 2 = vertexIndicator401 q S v := by
    by_cases hv : v ∈ S
    · rw [vertexIndicator401_of_mem q S hv]
      norm_num
    · rw [vertexIndicator401_of_not_mem q S hv]
      norm_num
  change (∑ v, (n * vertexIndicator401 q S v - m) ^ 2) =
    n * m * (n - m)
  have hcross :
      (∑ v, 2 * (n * vertexIndicator401 q S v) * m) = 2 * n * m * m := by
    calc
      (∑ v, 2 * (n * vertexIndicator401 q S v) * m) =
          (2 * n * m) * ∑ v, vertexIndicator401 q S v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 2 * n * m * m := by
        rw [sum_vertexIndicator401]
  simp_rw [sub_sq, mul_pow, hsq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [sum_vertexIndicator401]
  rw [hcross]
  simp [n, m]
  ring

/-- Summing over the explicit neighbor image is the same as summing over the
402 generators. -/
theorem sum_lpsNeighbors401_eq_sum_generators
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (v : PGL(2, ZMod q))
    (f : PGL(2, ZMod q) → ℝ) :
    ∑ w ∈ lpsNeighbors401 q hq v, f w =
      ∑ s ∈ lpsGenerators401 q hq, f (s * v) := by
  classical
  unfold lpsNeighbors401
  rw [Finset.sum_image]
  intro s _hs t _ht hst
  exact mul_right_cancel hst

/-- Total incidence into `S`: regularity and symmetry make it `402 |S|`. -/
theorem sum_neighbor_vertexIndicator401_over_vertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, ∑ w ∈ lpsNeighbors401 q hq v, vertexIndicator401 q S w =
      402 * S.card := by
  classical
  calc
    (∑ v, ∑ w ∈ lpsNeighbors401 q hq v,
        vertexIndicator401 q S w) =
        ∑ v, ∑ s ∈ lpsGenerators401 q hq,
          vertexIndicator401 q S (s * v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact sum_lpsNeighbors401_eq_sum_generators q hq v
        (vertexIndicator401 q S)
    _ = ∑ s ∈ lpsGenerators401 q hq,
          ∑ v, vertexIndicator401 q S (s * v) := by
      rw [Finset.sum_comm]
    _ = ∑ s ∈ lpsGenerators401 q hq,
          ∑ v, vertexIndicator401 q S v := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact Equiv.sum_comp (Equiv.mulLeft s) (vertexIndicator401 q S)
    _ = 402 * S.card := by
      rw [sum_vertexIndicator401]
      simp [card_lpsGenerators401 q hq40 hq]

/-- Exact quadratic-form identity for the division-free centered indicator.
This is the algebraic bridge from the graph-only Rayleigh premise to induced
edge counting. -/
theorem adjacencyRayleigh_centeredVertexIndicator401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q))) :
    adjacencyRayleigh401 q hq (centeredVertexIndicator401 q S) =
      (Fintype.card (PGL(2, ZMod q)) : ℝ) ^ 2 *
          insideAdjacencyCount401 q hq S -
        402 * Fintype.card (PGL(2, ZMod q)) * S.card ^ 2 := by
  classical
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  have hinner (v : PGL(2, ZMod q)) :
      (∑ w ∈ lpsNeighbors401 q hq v,
          centeredVertexIndicator401 q S w) =
        n * (lpsNeighborsIn401 q hq S v).card - 402 * m := by
    unfold centeredVertexIndicator401
    rw [Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    rw [sum_neighbor_vertexIndicator401]
    rw [Finset.sum_const, card_lpsNeighbors401 q hq40 hq]
    simp only [nsmul_eq_mul]
    dsimp [n, m]
  have hinside :
      (∑ v, vertexIndicator401 q S v *
          ((lpsNeighborsIn401 q hq S v).card : ℝ)) =
        insideAdjacencyCount401 q hq S := by
    rw [← adjacencyRayleigh_vertexIndicator401 q hq S]
    unfold adjacencyRayleigh401
    simp_rw [sum_neighbor_vertexIndicator401]
  have hcount :
      (∑ v, ((lpsNeighborsIn401 q hq S v).card : ℝ)) = 402 * m := by
    have h := sum_neighbor_vertexIndicator401_over_vertices q hq40 hq S
    simp_rw [sum_neighbor_vertexIndicator401] at h
    simpa only [m] using h
  have hA :
      (∑ v, n * vertexIndicator401 q S v *
          (n * (lpsNeighborsIn401 q hq S v).card)) =
        n ^ 2 * insideAdjacencyCount401 q hq S := by
    calc
      _ = n ^ 2 * ∑ v, vertexIndicator401 q S v *
          ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = n ^ 2 * insideAdjacencyCount401 q hq S := by rw [hinside]
  have hB :
      (∑ v, n * vertexIndicator401 q S v * (402 * m)) =
        402 * n * m ^ 2 := by
    calc
      _ = (402 * n * m) * ∑ v, vertexIndicator401 q S v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 402 * n * m ^ 2 := by
        rw [sum_vertexIndicator401]
        change 402 * n * m * m = 402 * n * m ^ 2
        ring
  have hC :
      (∑ v, m * (n * (lpsNeighborsIn401 q hq S v).card)) =
        402 * n * m ^ 2 := by
    calc
      _ = (m * n) * ∑ v,
          ((lpsNeighborsIn401 q hq S v).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = 402 * n * m ^ 2 := by rw [hcount]; ring
  have hD :
      (∑ _v : PGL(2, ZMod q), m * (402 * m)) = 402 * n * m ^ 2 := by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    dsimp [n]
    ring
  rw [adjacencyRayleigh401]
  simp_rw [hinner]
  unfold centeredVertexIndicator401
  change (∑ v,
      (n * vertexIndicator401 q S v - m) *
        (n * (lpsNeighborsIn401 q hq S v).card - 402 * m)) =
    n ^ 2 * insideAdjacencyCount401 q hq S - 402 * n * m ^ 2
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [hA, hB, hC, hD]
  ring

/-- Rational Alon--Chung bound obtained from the sole graph-only external
premise.  `insideAdjacencyCount401` is directed, so no hidden factor of two is
introduced here. -/
theorem alonChung_insideAdjacency401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (S : Finset (PGL(2, ZMod q))) :
    10 * (Fintype.card (PGL(2, ZMod q)) : ℝ) *
        (insideAdjacencyCount401 q hq S : ℝ) ≤
      401 * (S.card : ℝ) *
          ((Fintype.card (PGL(2, ZMod q)) : ℝ) - S.card) +
        4020 * (S.card : ℝ) ^ 2 := by
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  let d : ℝ := insideAdjacencyCount401 q hq S
  have hspectral := hLPS.2 (centeredVertexIndicator401 q S)
    (sum_centeredVertexIndicator401 q S)
  rw [adjacencyRayleigh_centeredVertexIndicator401 q hq40 hq S,
    sum_sq_centeredVertexIndicator401 q S] at hspectral
  have hn : 0 < n := by
    dsimp [n]
    positivity
  change 10 * n * d ≤ 401 * m * (n - m) + 4020 * m ^ 2
  change
    10 * (n ^ 2 * d - 402 * n * m ^ 2) ≤
      401 * (n * m * (n - m)) at hspectral
  nlinarith

/-- At the corrected BE20 primal graph radius, the induced directed adjacency
count is strictly below `41 |S|`.  The rational constant `1003/25 = 40.12`
leaves visible slack above the LPS contribution `40.1`; no decimal arithmetic
or source normalization identity is hidden in the proof. -/
theorem smallSet_insideAdjacency401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (S : Finset (PGL(2, ZMod q)))
    (hsmall : 10000000 * S.card ≤
      402 * Fintype.card (PGL(2, ZMod q))) :
    25 * insideAdjacencyCount401 q hq S ≤ 1003 * S.card := by
  have halon := alonChung_insideAdjacency401 q hq40 hq hLPS S
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  let d : ℝ := insideAdjacencyCount401 q hq S
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hm : 0 ≤ m := by positivity
  have hsmallR : 10000000 * m ≤ 402 * n := by
    dsimp [m, n]
    exact_mod_cast hsmall
  change 10 * n * d ≤ 401 * m * (n - m) + 4020 * m ^ 2 at halon
  have hreal : 25 * d ≤ 1003 * m := by
    nlinarith
  dsimp [d, m] at hreal
  exact_mod_cast hreal

end QEC.Coding.BalancedProduct.LPSGraph

import QEC.Coding.ExpanderCodes.SmallSetExpansion
import QEC.Coding.ExpanderCodes.TannerBlockWeight

/-!
# Global expansion for the PK22 Tanner lifted product

This module connects the concrete horizontal and vertical neighbours of the
Tanner lifted product to the weighted-graph counting interface used in the
global small-set expansion argument.
-/

namespace QEC.Coding.TannerLiftedProduct

universe u v

variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

/-- The horizontal-plus-vertical adjacency multigraph on product vertices.
Parallel local directions are retained as edge multiplicities. -/
def adjacencyGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun a : W => horizontalNeighbor label v a = u).card +
      (Finset.univ.filter fun b : W => verticalNeighbor label v b = u).card

/-- The horizontal-then-vertical length-two paths associated to local faces.
This is the concrete subgraph of the square graph used by the active-face
argument. -/
def faceSquareGraph (label : W → G) :
    SmallSetExpansion.WeightedGraph (VertexIndex G) :=
  fun v u =>
    (Finset.univ.filter fun p : W × W =>
      verticalNeighbor label (horizontalNeighbor label v p.1) p.2 = u).card

/-- Horizontal local directions whose opposite endpoint lies in `L`. -/
noncomputable def horizontalDirectionsInto (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun a => horizontalNeighbor label v a ∈ L

/-- Vertical local directions whose opposite endpoint lies in `L`. -/
noncomputable def verticalDirectionsInto (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun b => verticalNeighbor label v b ∈ L

/-- Horizontal directions whose opposite endpoint is outside `L`. -/
noncomputable def horizontalDirectionsOutside (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun a => horizontalNeighbor label v a ∉ L

/-- Vertical directions whose opposite endpoint is outside `L`. -/
noncomputable def verticalDirectionsOutside (label : W → G)
    (L : Finset (VertexIndex G)) (v : VertexIndex G) : Finset W := by
  classical
  exact Finset.univ.filter fun b => verticalNeighbor label v b ∉ L

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Outgoing adjacency multiplicity into a vertex set is exactly the number
of horizontal and vertical local directions entering it. -/
theorem sum_adjacencyGraph_eq_card_directionsInto
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    ∑ u ∈ L, adjacencyGraph label v u =
      (horizontalDirectionsInto label L v).card +
        (verticalDirectionsInto label L v).card := by
  classical
  have hHorizontal := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) L (horizontalNeighbor label v)
  have hVertical := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset W) L (verticalNeighbor label v)
  simpa [adjacencyGraph, horizontalDirectionsInto, verticalDirectionsInto,
    Finset.sum_add_distrib] using congrArg₂ (· + ·) hHorizontal hVertical

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- The incoming and outside horizontal directions partition all directions. -/
theorem card_horizontalDirectionsInto_add_outside
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    (horizontalDirectionsInto label L v).card +
        (horizontalDirectionsOutside label L v).card = Fintype.card W := by
  classical
  simpa [horizontalDirectionsInto, horizontalDirectionsOutside] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W))
      (fun a => horizontalNeighbor label v a ∈ L))

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- The incoming and outside vertical directions partition all directions. -/
theorem card_verticalDirectionsInto_add_outside
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    (verticalDirectionsInto label L v).card +
        (verticalDirectionsOutside label L v).card = Fintype.card W := by
  classical
  simpa [verticalDirectionsInto, verticalDirectionsOutside] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W))
      (fun b => verticalNeighbor label v b ∈ L))

omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Outgoing face-square multiplicity into a vertex set counts the local
direction pairs whose opposite face vertex lies in that set. -/
theorem sum_faceSquareGraph_eq_card_filter
    (label : W → G) (L : Finset (VertexIndex G)) (v : VertexIndex G) :
    ∑ u ∈ L, faceSquareGraph label v u =
      (Finset.univ.filter fun p : W × W =>
        verticalNeighbor label (horizontalNeighbor label v p.1) p.2 ∈ L).card := by
  classical
  have hFiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (W × W)) L
    (fun p => verticalNeighbor label (horizontalNeighbor label v p.1) p.2)
  simpa [faceSquareGraph] using hFiber

/-- Active face-direction pairs in a selected local rectangle. The first
coordinate is horizontal and the second is vertical. -/
noncomputable def activeFaceDirectionPairs (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W) : Finset (W × W) := by
  classical
  exact (A ×ˢ B).filter fun p => localFaceMatrix label c v p.2 p.1 ≠ 0

omit [Fintype F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- Rectangle weight is the cardinality of its active face-direction pairs. -/
theorem card_activeFaceDirectionPairs
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W) :
    (activeFaceDirectionPairs label c v A B).card =
      ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A := by
  classical
  unfold activeFaceDirectionPairs ProductExpansion.restrictedWeight
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases _hzero : localFaceMatrix label c v b a = 0 <;> simp

omit [Fintype F] [Fintype G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- If every active face in a selected rectangle has its opposite vertex in
`L`, its rectangle weight is bounded by outgoing face-square multiplicity
into `L`. -/
theorem restrictedWeight_le_sum_faceSquareGraph
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W)
    (L : Finset (VertexIndex G))
    (hOpposite : ∀ a ∈ A, ∀ b ∈ B,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L) :
    ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A ≤
      ∑ u ∈ L, faceSquareGraph label v u := by
  rw [← card_activeFaceDirectionPairs label c v A B,
    sum_faceSquareGraph_eq_card_filter]
  apply Finset.card_le_card
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpAB := Finset.mem_product.mp hpData.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ p,
    hOpposite p.1 hpAB.1 p.2 hpAB.2 hpData.2⟩

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- Directions outside a set containing every active vertex are inactive in
the coefficient sense required by the local-star proof. -/
theorem verticalDirectionsOutside_subset_inactive
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L) (v : VertexIndex G) :
    verticalDirectionsOutside label L v ⊆
      verticalInactiveDirections label c v := by
  intro b hb
  have hbOutside : verticalNeighbor label v b ∉ L := by
    simpa [verticalDirectionsOutside] using hb
  have hbZero : localVertexMatrix c (verticalNeighbor label v b) = 0 := by
    by_contra hbNonzero
    exact hbOutside (hActive
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero
        c (verticalNeighbor label v b)).2 hbNonzero))
  simpa [verticalInactiveDirections] using hbZero

/-- The active-vertex local-star estimate on caller-selected large direction
sets. The vertical set only needs to consist of inactive opposite endpoints;
this form is what the global labelled-set argument consumes. -/
theorem localStar_restrictedWeight_ge_on
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (v : VertexIndex G) (hv : localVertexMatrix c v ≠ 0)
    (A B : Finset W)
    (hBInactive : B ⊆ verticalInactiveDirections label c v)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hHorizontalLarge : Fintype.card W - m < A.card)
    (hVerticalLarge : Fintype.card W - m < B.card)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    s ≤ ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A := by
  let J₂ := localHeavyDifferenceDirections label h hRank g' c v ∩ B
  let J₃ := localAgreementDirections label h hRank g' c v ∩ B
  apply ProductExpansion.localStar_restrictedWeight_ge
    h (ProductExpansion.generatorImageParityCheck g')
    (localFaceMatrix label c v)
    (localVertexCosetLeaderMatrix h hRank g' c v)
    A B J₂ J₃ d m s beta hExpand
  · exact localVertexCosetLeaderMatrix_productKernel h hRank g' c v
  · exact localVertexCosetLeaderMatrix_ne_zero
      h hRank g' gInjective c v hv
  · intro hJ₃
    apply ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
      h (ProductExpansion.generatorImageParityCheck g')
      (localFaceMatrix label c v)
      (localVertexCosetLeaderMatrix h hRank g' c v)
      J₃ m beta hJ₃
    · intro i hi j
      exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
        label h hRank g' c v i (Finset.mem_inter.mp hi).1 j
    · intro i codeword hcodeword
      exact (ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
        h hRank (verticalVertexSyndrome g' c v) i).weight_le_add_codeword
          codeword hcodeword
    · intro j codeword hcodeword
      exact_mod_cast
        faceColumn_weight_le_add_codeword_of_fiberLocallyMinimal
          label h g' c hcLocal v j codeword hcodeword
    · exact hBudget
  · exact hHorizontalLarge
  · exact hVerticalLarge
  · intro b hb
    have hbInactive := hBInactive hb
    rw [verticalInactiveDirections_eq_heavy_union_agreement
      label h hRank g' c v] at hbInactive
    rcases Finset.mem_union.mp hbInactive with hbHeavy | hbAgree
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hbHeavy, hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hbAgree, hb⟩)
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_right
  · intro b hb
    exact localFaceMatrix_row_heavy_of_mem_heavyDifference
      label h hRank g' c hcCycle d hDistance v b
        (Finset.mem_inter.mp hb).1
  · exact hDistanceScale
  · exact hRectangleScale
  · intro b hb a _ha
    exact localFaceMatrix_eq_localVertexCosetLeaderMatrix_of_mem_agreement
      label h hRank g' c v b (Finset.mem_inter.mp hb).1 a

/-- A concrete active vertex either has at least `m` labelled neighbours in
the product graph or at least `s` active-face paths to labelled vertices in
the face-square graph. -/
theorem activeVertex_edge_or_face_expanding
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (hOpposite : ∀ v ∈ vertexBlockSupport c,
      ∀ a ∈ horizontalDirectionsOutside label L v,
      ∀ b ∈ verticalDirectionsOutside label L v,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L)
    (v : VertexIndex G) (hv : v ∈ vertexBlockSupport c)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
      s ≤ ∑ u ∈ L, faceSquareGraph label v u := by
  by_cases hEdge : m ≤ ∑ u ∈ L, adjacencyGraph label v u
  · exact Or.inl hEdge
  · right
    have hAdjacency := sum_adjacencyGraph_eq_card_directionsInto
      label L v
    have hHorizontalSmall :
        (horizontalDirectionsInto label L v).card < m := by
      omega
    have hVerticalSmall :
        (verticalDirectionsInto label L v).card < m := by
      omega
    have hHorizontalPartition := card_horizontalDirectionsInto_add_outside
      label L v
    have hVerticalPartition := card_verticalDirectionsInto_add_outside
      label L v
    have hHorizontalLarge : Fintype.card W - m <
        (horizontalDirectionsOutside label L v).card := by
      omega
    have hVerticalLarge : Fintype.card W - m <
        (verticalDirectionsOutside label L v).card := by
      omega
    have hLocal := localStar_restrictedWeight_ge_on
      label h hRank g' gInjective c hcCycle hcLocal v
      ((mem_vertexBlockSupport_iff_localVertexMatrix_ne_zero c v).1 hv)
      (horizontalDirectionsOutside label L v)
      (verticalDirectionsOutside label L v)
      (verticalDirectionsOutside_subset_inactive label c L hActive v)
      d m s beta hExpand hDistance hHorizontalLarge hVerticalLarge
      hDistanceScale hRectangleScale hBudget
    exact hLocal.trans (restrictedWeight_le_sum_faceSquareGraph
      label c v
      (horizontalDirectionsOutside label L v)
      (verticalDirectionsOutside label L v) L
      (hOpposite v hv))

/-- The vertices of `L` satisfying the first global expansion alternative. -/
noncomputable def edgeExpandingVertices (label : W → G)
    (L : Finset (VertexIndex G)) (m : Nat) : Finset (VertexIndex G) := by
  classical
  exact L.filter fun v => m ≤ ∑ u ∈ L, adjacencyGraph label v u

/-- The vertices of `L` satisfying the active-face expansion alternative. -/
noncomputable def faceExpandingVertices (label : W → G)
    (L : Finset (VertexIndex G)) (s : Nat) : Finset (VertexIndex G) := by
  classical
  exact L.filter fun v => s ≤ ∑ u ∈ L, faceSquareGraph label v u

omit [Fintype G] [DecidableEq W] in
/-- A pointwise edge-or-face degree dichotomy and the two small-set mixing
bounds force the entire labelled set to be empty. -/
theorem labelledSet_eq_empty_of_degree_dichotomy
    (label : W → G) (L : Finset (VertexIndex G))
    (radiusEdge radiusFace m s : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : L.card ≤ radiusEdge)
    (hLRadiusFace : L.card ≤ radiusFace)
    (hDichotomy : ∀ v ∈ L,
      m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
        s ≤ ∑ u ∈ L, faceSquareGraph label v u)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    L = ∅ := by
  let LEdge := edgeExpandingVertices label L m
  let LFace := faceExpandingVertices label L s
  apply SmallSetExpansion.labelledSet_eq_empty
    (adjacencyGraph label) (faceSquareGraph label)
    radiusEdge radiusFace m s lambdaEdge lambdaFace
    hLambdaEdge hLambdaFace hExpandEdge hExpandFace L LEdge LFace
  · intro v hv
    rcases hDichotomy v hv with hEdge | hFace
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv, hEdge⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv, hFace⟩)
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _
  · exact hLRadiusEdge
  · exact hLRadiusFace
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · exact hThresholdEdge
  · exact hThresholdFace

/-- A vertical edge carries an active face when at least one incident face has
a nonzero coefficient. This inclusive predicate is used for face-incidence
geometry; PK22's narrower `IsFaceActiveVerticalEdgeAt` is defined below. -/
def CarriesActiveFaceVerticalEdgeAt (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) : Prop :=
  ∃ a, localFaceMatrix label c v b a ≠ 0

/-- PK22's face-active vertical edge: it carries an active face and neither
endpoint carries an active vertex block. -/
def IsFaceActiveVerticalEdgeAt (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (b : W) : Prop :=
  CarriesActiveFaceVerticalEdgeAt label c v b ∧
    v ∉ vertexBlockSupport c ∧
      verticalNeighbor label v b ∉ vertexBlockSupport c

/-- A vertex is incident to a face-active vertical edge when one of its
vertical directions contains a nonzero face coefficient. -/
def IsIncidentToFaceActiveVerticalEdge (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) : Prop :=
  ∃ b, IsFaceActiveVerticalEdgeAt label c v b

/-- The closure condition in PK22's definition of labelled vertices: active
vertices are labelled, and an endpoint of a face-active vertical edge becomes
labelled once it has at least `m` labelled neighbours. -/
def IsClosedLabelledSet (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (L : Finset (VertexIndex G)) : Prop :=
  vertexBlockSupport c ⊆ L ∧
    ∀ v, IsIncidentToFaceActiveVerticalEdge label c v →
      m ≤ ∑ u ∈ L, adjacencyGraph label v u → v ∈ L

/-- The canonical PK22 labelled set, defined as the intersection of all
finite sets satisfying the monotone closure rule. -/
noncomputable def labelledVertices (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) : Finset (VertexIndex G) := by
  classical
  exact Finset.univ.filter fun v =>
    ∀ L, IsClosedLabelledSet label c m L → v ∈ L

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
theorem mem_labelledVertices_iff (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (v : VertexIndex G) :
    v ∈ labelledVertices label c m ↔
      ∀ L, IsClosedLabelledSet label c m L → v ∈ L := by
  classical
  simp [labelledVertices]

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- The canonical labelled set is contained in every closed labelled set. -/
theorem labelledVertices_subset (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (L : Finset (VertexIndex G))
    (hL : IsClosedLabelledSet label c m L) :
    labelledVertices label c m ⊆ L := by
  intro v hv
  exact (mem_labelledVertices_iff label c m v).mp hv L hL

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- The intersection construction is itself closed. -/
theorem labelledVertices_isClosed (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) :
    IsClosedLabelledSet label c m (labelledVertices label c m) := by
  constructor
  · intro v hv
    rw [mem_labelledVertices_iff]
    intro L hL
    exact hL.1 hv
  · intro v hvIncident hvDegree
    rw [mem_labelledVertices_iff]
    intro L hL
    apply hL.2 v hvIncident
    exact hvDegree.trans (Finset.sum_le_sum_of_subset
      (labelledVertices_subset label c m L hL))

omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R'] in
/-- Every non-active vertex in the minimal labelled closure entered through
the degree rule, hence has at least `m` labelled neighbours. -/
theorem labelledVertices_nonactive_degree (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (v : VertexIndex G)
    (hv : v ∈ labelledVertices label c m)
    (hvInactive : v ∉ vertexBlockSupport c) :
    m ≤ ∑ u ∈ labelledVertices label c m, adjacencyGraph label v u := by
  by_contra hDegree
  let L := labelledVertices label c m
  have hClosed := labelledVertices_isClosed label c m
  have hEraseClosed : IsClosedLabelledSet label c m (L.erase v) := by
    constructor
    · intro u hu
      exact Finset.mem_erase.mpr ⟨by
        intro huv
        subst u
        exact hvInactive hu, hClosed.1 hu⟩
    · intro u huIncident huDegree
      have huDegreeL : m ≤ ∑ x ∈ L, adjacencyGraph label u x :=
        huDegree.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset v L))
      have huL : u ∈ L := hClosed.2 u huIncident huDegreeL
      have huv : u ≠ v := by
        intro huv
        subst u
        have hEraseLe :
            (∑ x ∈ L.erase v, adjacencyGraph label v x) ≤
              ∑ x ∈ L, adjacencyGraph label v x :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset v L)
        have hDegreeL :
            (∑ x ∈ L, adjacencyGraph label v x) < m := by
          simpa [L] using Nat.lt_of_not_ge hDegree
        exact (not_lt_of_ge (huDegree.trans hEraseLe)) hDegreeL
      exact Finset.mem_erase.mpr ⟨huv, huL⟩
  have hvErase : v ∈ L.erase v :=
    (mem_labelledVertices_iff label c m v).mp hv (L.erase v) hEraseClosed
  simp at hvErase

omit [Fintype F] [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] in
/-- If every vertical edge carrying an active face has a labelled endpoint,
then every
active face belongs to the star of a labelled vertex. -/
theorem faceSupport_has_labelled_incidentVertex_of_carriesActiveFace
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hEdgeLabel : ∀ v b, CarriesActiveFaceVerticalEdgeAt label c v b →
      v ∈ L ∨ verticalNeighbor label v b ∈ L) :
    ∀ p ∈ faceSupport c, ∃ v ∈ L, p ∈ faceStar label v := by
  rintro ⟨a, b, g⟩ hp
  let v : VertexIndex G := (0, 0, g)
  have hface : faceAtVertex label v a b = (a, b, g) := by
    simp [v, faceAtVertex, doubleCoverVoltage]
  have hnonzero : localFaceMatrix label c v b a ≠ 0 := by
    simpa [localFaceMatrix, hface, faceSupport] using hp
  rcases hEdgeLabel v b ⟨a, hnonzero⟩ with hv | hv
  · exact ⟨v, hv, (mem_faceStar_iff label v _).2 ⟨a, b, hface⟩⟩
  · refine ⟨verticalNeighbor label v b, hv,
      (mem_faceStar_iff label (verticalNeighbor label v b) _).2 ?_⟩
    exact ⟨a, b, by simpa using hface⟩

omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] in
/-- In an active-face rectangle whose horizontal neighbour is unlabelled, the
labelled endpoint of the opposite vertical edge is the diagonal vertex. -/
theorem oppositeVertex_mem_of_carriesActiveFace
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hEdgeLabel : ∀ v b, CarriesActiveFaceVerticalEdgeAt label c v b →
      v ∈ L ∨ verticalNeighbor label v b ∈ L)
    (v : VertexIndex G) (a b : W)
    (ha : horizontalNeighbor label v a ∉ L)
    (hface : localFaceMatrix label c v b a ≠ 0) :
    verticalNeighbor label (horizontalNeighbor label v a) b ∈ L := by
  have hactive : CarriesActiveFaceVerticalEdgeAt label c
      (horizontalNeighbor label v a) b := by
    refine ⟨a, ?_⟩
    simpa [localFaceMatrix] using hface
  rcases hEdgeLabel (horizontalNeighbor label v a) b hactive with h | h
  · exact (ha h).elim
  · exact h

/-- PK22's global zero lemma for one Tanner orientation. Once a labelled set
contains every active vertex and every active face has a labelled incident
witness, the local product-expansion dichotomy and the two graph mixing
bounds rule out every nonzero fibre-locally-minimal cycle. -/
theorem cycle_eq_zero_of_globalExpansion
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (hFaceLabel : ∀ p ∈ faceSupport c,
      ∃ v ∈ L, p ∈ faceStar label v)
    (d m s : Nat) (beta : ℝ)
    (hNonactiveEdge : ∀ v ∈ L, v ∉ vertexBlockSupport c →
      m ≤ ∑ u ∈ L, adjacencyGraph label v u)
    (hOpposite : ∀ v ∈ vertexBlockSupport c,
      ∀ a ∈ horizontalDirectionsOutside label L v,
      ∀ b ∈ verticalDirectionsOutside label L v,
      localFaceMatrix label c v b a ≠ 0 →
        verticalNeighbor label (horizontalNeighbor label v a) b ∈ L)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : L.card ≤ radiusEdge)
    (hLRadiusFace : L.card ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  have hDichotomy : ∀ v ∈ L,
      m ≤ ∑ u ∈ L, adjacencyGraph label v u ∨
        s ≤ ∑ u ∈ L, faceSquareGraph label v u := by
    intro v hv
    by_cases hvActive : v ∈ vertexBlockSupport c
    · exact activeVertex_edge_or_face_expanding
        label h hRank g' gInjective c hcCycle hcLocal L hActive
        hOpposite v hvActive d m s beta hExpand hDistance hLength
        hDistanceScale hRectangleScale hBudget
    · exact Or.inl (hNonactiveEdge v hv hvActive)
  have hLEmpty := labelledSet_eq_empty_of_degree_dichotomy label L
    radiusEdge radiusFace m s lambdaEdge lambdaFace
    hLambdaEdge hLambdaFace hExpandEdge hExpandFace
    hLRadiusEdge hLRadiusFace hDichotomy hThresholdEdge hThresholdFace
  have hVertexEmpty : vertexBlockSupport c = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have : v ∈ L := hActive hv
    simp [hLEmpty] at this
  have hFaceEmpty : faceSupport c = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨v, hv, _hpv⟩ := hFaceLabel p hp
    simp [hLEmpty] at hv
  apply (blockWeight_eq_zero_iff c).mp
  simp [blockWeight, hVertexEmpty, hFaceEmpty]

/-- Inclusive edge-incidence form of the global zero lemma. The two face
conditions follow when every vertical edge carrying an active face has a
labelled endpoint. -/
theorem cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled
    (label : W → G) (h : Matrix R W F)
    (hRank : h.rank = Fintype.card R) (g' : Matrix R' W F)
    (gInjective : Function.Injective
      (fun u : Word F R' => g'.transpose.mulVec u))
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (hcLocal : LocallyMinimalDistance.IsLocallyMinimal blockWeight
      (horizontalFiberBoundaryMoves label h g') c)
    (L : Finset (VertexIndex G))
    (hActive : vertexBlockSupport c ⊆ L)
    (hEdgeLabel : ∀ v b, CarriesActiveFaceVerticalEdgeAt label c v b →
      v ∈ L ∨ verticalNeighbor label v b ∈ L)
    (d m s : Nat) (beta : ℝ)
    (hNonactiveEdge : ∀ v ∈ L, v ∉ vertexBlockSupport c →
      m ≤ ∑ u ∈ L, adjacencyGraph label v u)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : L.card ≤ radiusEdge)
    (hLRadiusFace : L.card ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  apply cycle_eq_zero_of_globalExpansion label h hRank g' gInjective c
    hcCycle hcLocal L hActive
    (faceSupport_has_labelled_incidentVertex_of_carriesActiveFace
      label c L hEdgeLabel)
    d m s beta hNonactiveEdge
  · intro v _hv a ha b _hb hface
    exact oppositeVertex_mem_of_carriesActiveFace
      label c L hEdgeLabel v a b
      (by simpa [horizontalDirectionsOutside] using ha) hface
  · exact hExpand
  · exact hDistance
  · exact hLength
  · exact hDistanceScale
  · exact hRectangleScale
  · exact hBudget
  · exact hLambdaEdge
  · exact hLambdaFace
  · exact hExpandEdge
  · exact hExpandFace
  · exact hLRadiusEdge
  · exact hLRadiusFace
  · exact hThresholdEdge
  · exact hThresholdFace

/-- Radius-conditional labelled-closure form of PK22's global zero argument.
Active vertices and the non-active degree alternative follow from the least
closed labelled set. The labelled-edge hypothesis and the two labelled-set
radius bounds remain explicit; the source derives them in separate incidence
counting and `lbl-edge` arguments. -/
theorem cycle_eq_zero_of_globalExpansion_of_labelledVertices
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
    (hEdgeLabel : ∀ v b, IsFaceActiveVerticalEdgeAt label c v b →
      v ∈ labelledVertices label c m ∨
        verticalNeighbor label v b ∈ labelledVertices label c m)
    (hExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck g') s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (radiusEdge radiusFace : Nat) (lambdaEdge lambdaFace : ℝ)
    (hLambdaEdge : 0 < lambdaEdge) (hLambdaFace : 0 < lambdaFace)
    (hExpandEdge : SmallSetExpansion.IsSmallSetEdgeExpanding
      (adjacencyGraph label) radiusEdge lambdaEdge)
    (hExpandFace : SmallSetExpansion.IsSmallSetEdgeExpanding
      (faceSquareGraph label) radiusFace lambdaFace)
    (hLRadiusEdge : (labelledVertices label c m).card ≤ radiusEdge)
    (hLRadiusFace : (labelledVertices label c m).card ≤ radiusFace)
    (hThresholdEdge : 2 * lambdaEdge ≤ m)
    (hThresholdFace : 2 * lambdaFace ≤ s) :
    c = 0 := by
  have hClosed := labelledVertices_isClosed label c m
  have hCarriesLabel : ∀ v b,
      CarriesActiveFaceVerticalEdgeAt label c v b →
        v ∈ labelledVertices label c m ∨
          verticalNeighbor label v b ∈ labelledVertices label c m := by
    intro v b hCarries
    by_cases hv : v ∈ vertexBlockSupport c
    · exact Or.inl (hClosed.1 hv)
    by_cases hNeighbor : verticalNeighbor label v b ∈ vertexBlockSupport c
    · exact Or.inr (hClosed.1 hNeighbor)
    · exact hEdgeLabel v b ⟨hCarries, hv, hNeighbor⟩
  apply cycle_eq_zero_of_globalExpansion_of_carriesActiveFaceLabelled
    label h hRank g' gInjective c hcCycle hcLocal
    (labelledVertices label c m)
    hClosed.1 hCarriesLabel
    d m s beta
    (fun v hv hvInactive =>
      labelledVertices_nonactive_degree label c m v hv hvInactive)
    hExpand hDistance hLength hDistanceScale hRectangleScale hBudget
    radiusEdge radiusFace lambdaEdge lambdaFace hLambdaEdge hLambdaFace
    hExpandEdge hExpandFace hLRadiusEdge hLRadiusFace
    hThresholdEdge hThresholdFace

end QEC.Coding.TannerLiftedProduct

import Mathlib

/-!
# Finite connectivity graphs

This module contains the finite graph vocabulary shared by the fixed-generator
connectivity interface.  Separator measurements are defined by finite
enumeration in `QEC.Locality.SeparatorProfile`.
-/

namespace QEC.Locality

universe u

/-- A finite simple graph on code coordinates. -/
structure ConnectivityGraph (ι : Type u) [Fintype ι] where
  adjacent : ι → ι → Prop
  symmetric : ∀ ⦃i j : ι⦄, adjacent i j → adjacent j i
  loopless : ∀ i : ι, ¬ adjacent i i

/-- The graph induced by the explicitly listed vertex set. -/
def inducedSubgraph {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ConnectivityGraph {i : ι // i ∈ vertices} where
  adjacent x y := G.adjacent x.1 y.1
  symmetric := by
    intro x y hxy
    exact G.symmetric hxy
  loopless := by
    intro x hxx
    exact G.loopless x.1 hxx

/-- Induced adjacency is exactly the original graph relation restricted to listed vertices. -/
theorem inducedSubgraph_adj_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (x y : {i : ι // i ∈ vertices}) :
    (inducedSubgraph G vertices).adjacent x y ↔ G.adjacent x.1 y.1 :=
  Iff.rfl

/-- There is no graph edge from a vertex in `left` to a vertex in `right`. -/
def NoEdgeBetween {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (left right : Finset ι) : Prop :=
  ∀ ⦃x : ι⦄, x ∈ left → ∀ ⦃y : ι⦄, y ∈ right → ¬ G.adjacent x y

/--
The fixed `2/3` balance convention after deleting a vertex separator.

`left` and `right` partition exactly the induced vertex set after deleting
`separator`; neither side may contain more than two thirds of the original
induced vertex set, and no edge may cross the partition.
-/
def TwoThirdsBalancedPartitionAfterDeleting {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices left separator right : Finset ι) : Prop :=
  separator ⊆ vertices ∧
    left ∪ right = vertices \ separator ∧
    Disjoint left right ∧
    3 * left.card ≤ 2 * vertices.card ∧
    3 * right.card ≤ 2 * vertices.card ∧
    NoEdgeBetween G left right

/-- A separator has the fixed `2/3` balance convention when such a partition exists. -/
def IsTwoThirdsBalancedVertexSeparator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices separator : Finset ι) : Prop :=
  ∃ left right : Finset ι,
    TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right

/-- Deleting every vertex is always a `2/3`-balanced separator. -/
theorem self_isTwoThirdsBalancedVertexSeparator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    IsTwoThirdsBalancedVertexSeparator G vertices vertices := by
  refine ⟨∅, ∅, ?_⟩
  simp [TwoThirdsBalancedPartitionAfterDeleting, NoEdgeBetween]

end QEC.Locality

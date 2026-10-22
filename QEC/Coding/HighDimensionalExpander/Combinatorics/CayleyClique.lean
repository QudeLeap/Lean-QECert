import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cayley and Schreier clique complexes

This module constructs abstract simplicial complexes directly from graphs: the
faces are exactly the nonempty finite cliques.  It then specializes the
construction to Cayley graphs and to Schreier graphs computed from a genuine
group action.  No face table, locality certificate, or expansion property is
accepted as data.
-/

namespace QEC.Coding.HighDimensionalExpander.CayleyClique

open Finset

universe u v

variable {V : Type u} {W : Type v}

/-- The abstract simplicial complex whose faces are the nonempty finite
cliques of `G`. -/
def cliqueComplex (G : SimpleGraph V) : AbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ G.IsClique (s : Set V)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, hs.2.subset ?_⟩
    simpa using hts
  singleton_mem x := by
    simp

@[simp]
theorem mem_cliqueComplex_iff (G : SimpleGraph V) (s : Finset V) :
    s ∈ cliqueComplex G ↔ s.Nonempty ∧ G.IsClique (s : Set V) :=
  Iff.rfl

/-- Three pairwise adjacent vertices form an actual triangular face of the
clique complex. -/
theorem triple_mem_cliqueComplex
    [DecidableEq V] (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    {a, b, c} ∈ cliqueComplex G := by
  rw [mem_cliqueComplex_iff]
  refine ⟨by simp, ?_⟩
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact (hxy rfl).elim
  · exact hab
  · exact hac
  · exact G.adj_symm hab
  · exact (hxy rfl).elim
  · exact hbc
  · exact G.adj_symm hac
  · exact G.adj_symm hbc
  · exact (hxy rfl).elim

/-- Four pairwise adjacent vertices form an actual tetrahedral face of the
clique complex. -/
theorem quadruple_mem_cliqueComplex
    [DecidableEq V] (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : G.Adj c d) :
    {a, b, c, d} ∈ cliqueComplex G := by
  rw [mem_cliqueComplex_iff]
  refine ⟨by simp, ?_⟩
  have habc : G.IsClique ({a, b, c} : Set V) := by
    have hmem := triple_mem_cliqueComplex G hab hac hbc
    have hfin := (mem_cliqueComplex_iff G {a, b, c}).mp hmem |>.2
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hfin
  have hins : G.IsClique (insert d ({a, b, c} : Set V)) :=
    habc.insert (by
      intro x hx _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact G.adj_symm had
      · exact G.adj_symm hbd
      · exact G.adj_symm hcd)
  have hset :
      (({a, b, c, d} : Finset V) : Set V) =
        insert d ({a, b, c} : Set V) := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact hins

/-- A graph isomorphism maps every face of the clique complex to a face, and
reflects face membership. -/
theorem map_mem_cliqueComplex_iff
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (s : Finset V) :
    s.map e.toEquiv.toEmbedding ∈ cliqueComplex H ↔ s ∈ cliqueComplex G := by
  simp only [mem_cliqueComplex_iff, Finset.map_nonempty]
  constructor
  · rintro ⟨hsne, hs⟩
    refine ⟨hsne, ?_⟩
    intro x hx y hy hxy
    apply e.map_adj_iff.mp
    exact hs (by simpa using hx) (by simpa using hy) (by simpa using hxy)
  · rintro ⟨hsne, hs⟩
    refine ⟨hsne, ?_⟩
    intro x hx y hy hxy
    have hxFinset : x ∈ s.map e.toEquiv.toEmbedding := hx
    have hyFinset : y ∈ s.map e.toEquiv.toEmbedding := hy
    obtain ⟨x', hx', hxeq⟩ := Finset.mem_map.mp hxFinset
    obtain ⟨y', hy', hyeq⟩ := Finset.mem_map.mp hyFinset
    have hxmem : e.symm x ∈ s := by
      simpa [← hxeq] using hx'
    have hymem : e.symm y ∈ s := by
      simpa [← hyeq] using hy'
    have hadj : H.Adj (e (e.symm x)) (e (e.symm y)) := by
      apply e.map_adj_iff.mpr
      apply hs hxmem hymem
      intro heq
      exact hxy (e.symm.injective heq)
    simpa using hadj

section Finite

variable [Fintype V] [DecidableEq V]

/-- Vertices which extend `s` to a face by adjoining one new vertex. -/
noncomputable def extensionVertices
    (K : AbstractSimplicialComplex V) (s : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun x => x ∉ s ∧ insert x s ∈ K

@[simp]
theorem mem_extensionVertices_iff
    (K : AbstractSimplicialComplex V) (s : Finset V) (x : V) :
    x ∈ extensionVertices K s ↔ x ∉ s ∧ insert x s ∈ K := by
  classical
  simp [extensionVertices]

theorem card_extensionVertices_le_card
    (K : AbstractSimplicialComplex V) (s : Finset V) :
    (extensionVertices K s).card ≤ Fintype.card V := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (extensionVertices K s))

/-- The finite set of vertices adjacent to `x`, without requiring a global
decidable-adjacency instance for `G`. -/
noncomputable def neighborVertices (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter fun y => G.Adj x y

omit [DecidableEq V] in
@[simp]
theorem mem_neighborVertices_iff (G : SimpleGraph V) (x y : V) :
    y ∈ neighborVertices G x ↔ G.Adj x y := by
  classical
  simp [neighborVertices]

theorem extensionVertices_subset_neighborVertices
    (G : SimpleGraph V) (s : Finset V) {x : V} (hx : x ∈ s) :
    extensionVertices (cliqueComplex G) s ⊆ neighborVertices G x := by
  intro y hy
  rw [mem_extensionVertices_iff] at hy
  rw [mem_neighborVertices_iff]
  exact hy.2.2 (by exact Finset.mem_insert_of_mem hx) (by simp) (by
    intro hxy
    subst y
    exact hy.1 hx)

/-- Once a face has a vertex, the number of one-vertex cofaces is bounded by
the degree of that vertex. -/
theorem card_extensionVertices_le_neighbors
    (G : SimpleGraph V) (s : Finset V) {x : V} (hx : x ∈ s) :
    (extensionVertices (cliqueComplex G) s).card ≤ (neighborVertices G x).card := by
  exact Finset.card_le_card (extensionVertices_subset_neighborVertices G s hx)

end Finite

section Cayley

variable {Γ : Type u} [Group Γ]

/-- The clique complex of the undirected Cayley graph generated by `S`. -/
def cayleyCliqueComplex (S : Set Γ) : AbstractSimplicialComplex Γ :=
  cliqueComplex (SimpleGraph.mulCayley S)

@[simp]
theorem mem_cayleyCliqueComplex_iff (S : Set Γ) (s : Finset Γ) :
    s ∈ cayleyCliqueComplex S ↔
      s.Nonempty ∧ (SimpleGraph.mulCayley S).IsClique (s : Set Γ) :=
  Iff.rfl

/-- Left multiplication is an automorphism of an undirected Cayley graph. -/
def cayleyLeftIso (S : Set Γ) (a : Γ) :
    SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley S where
  toEquiv := Equiv.mulLeft a
  map_rel_iff' := by
    intro x y
    exact SimpleGraph.mulCayley_adj_mul_iff_right

@[simp]
theorem leftMul_mem_cayleyCliqueComplex_iff
    (S : Set Γ) (a : Γ) (s : Finset Γ) :
    s.map (Equiv.mulLeft a).toEmbedding ∈ cayleyCliqueComplex S ↔
      s ∈ cayleyCliqueComplex S :=
  map_mem_cliqueComplex_iff (cayleyLeftIso S a) s

section Finite

variable [Fintype Γ] [DecidableEq Γ]

/-- The two images of the generator set which contain every neighbor of `x`
in the undirected Cayley graph. -/
def cayleyNeighborCandidates (S : Finset Γ) (x : Γ) : Finset Γ :=
  (S.image fun g => x * g) ∪ (S.image fun g => x * g⁻¹)

theorem neighborVertices_cayley_subset_candidates (S : Finset Γ) (x : Γ) :
    neighborVertices (SimpleGraph.mulCayley (S : Set Γ)) x ⊆
      cayleyNeighborCandidates S x := by
  intro y hy
  rw [mem_neighborVertices_iff, SimpleGraph.mulCayley_adj] at hy
  rcases hy.2 with h | h
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨x⁻¹ * y, h, by simp⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨y⁻¹ * x, h, by simp⟩

omit [Fintype Γ] in
theorem card_cayleyNeighborCandidates_le (S : Finset Γ) (x : Γ) :
    (cayleyNeighborCandidates S x).card ≤ 2 * S.card := by
  calc
    (cayleyNeighborCandidates S x).card ≤
        (S.image fun g => x * g).card + (S.image fun g => x * g⁻¹).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card := by omega

theorem card_neighborVertices_cayley_le (S : Finset Γ) (x : Γ) :
    (neighborVertices (SimpleGraph.mulCayley (S : Set Γ)) x).card ≤ 2 * S.card :=
  (Finset.card_le_card (neighborVertices_cayley_subset_candidates S x)).trans
    (card_cayleyNeighborCandidates_le S x)

/-- The number of one-vertex cofaces of a nonempty Cayley-clique face is
bounded directly by twice the number of supplied generators. -/
theorem card_cayley_extensionVertices_le
    (S : Finset Γ) (s : Finset Γ) {x : Γ} (hx : x ∈ s) :
    (extensionVertices (cayleyCliqueComplex (S : Set Γ)) s).card ≤ 2 * S.card :=
  (card_extensionVertices_le_neighbors
    (SimpleGraph.mulCayley (S : Set Γ)) s hx).trans
      (card_neighborVertices_cayley_le S x)

end Finite

end Cayley

section Schreier

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- The undirected Schreier graph computed from the action of the generators
`S` on `X`. -/
def schreierGraph (S : Set Γ) : SimpleGraph X :=
  SimpleGraph.fromRel fun x y => ∃ g ∈ S, g • x = y

@[simp]
theorem schreierGraph_adj (S : Set Γ) (x y : X) :
    (schreierGraph S).Adj x y ↔
      x ≠ y ∧ (∃ g ∈ S, g • x = y) ∨ x ≠ y ∧ (∃ g ∈ S, g • y = x) := by
  simp only [schreierGraph, SimpleGraph.fromRel_adj]
  aesop

/-- The clique complex of a Schreier graph. -/
def schreierCliqueComplex (S : Set Γ) : AbstractSimplicialComplex X :=
  cliqueComplex (schreierGraph S)

@[simp]
theorem mem_schreierCliqueComplex_iff (S : Set Γ) (s : Finset X) :
    s ∈ schreierCliqueComplex S ↔ s.Nonempty ∧ (schreierGraph S).IsClique (s : Set X) :=
  Iff.rfl

/-- A permutation commuting with every selected generator is a Schreier-graph
automorphism. -/
def schreierIsoOfCommutes
    (S : Set Γ) (e : X ≃ X) (h : ∀ g ∈ S, ∀ x, e (g • x) = g • e x) :
    schreierGraph (X := X) S ≃g schreierGraph (X := X) S where
  toEquiv := e
  map_rel_iff' := by
    intro x y
    simp only [schreierGraph_adj]
    constructor
    · rintro (⟨hne, g, hg, hxy⟩ | ⟨hne, g, hg, hyx⟩)
      · left
        refine ⟨fun hxy' => hne (congrArg e hxy'), g, hg, ?_⟩
        apply e.injective
        simpa [h g hg x] using hxy
      · right
        refine ⟨fun hxy' => hne (congrArg e hxy'), g, hg, ?_⟩
        apply e.injective
        simpa [h g hg y] using hyx
    · rintro (⟨hne, g, hg, hxy⟩ | ⟨hne, g, hg, hyx⟩)
      · left
        refine ⟨e.injective.ne hne, g, hg, ?_⟩
        simpa [h g hg x] using congrArg e hxy
      · right
        refine ⟨e.injective.ne hne, g, hg, ?_⟩
        simpa [h g hg y] using congrArg e hyx

@[simp]
theorem map_mem_schreierCliqueComplex_iff
    (S : Set Γ) (e : X ≃ X) (h : ∀ g ∈ S, ∀ x, e (g • x) = g • e x)
    (s : Finset X) :
    s.map e.toEmbedding ∈ schreierCliqueComplex S ↔ s ∈ schreierCliqueComplex S :=
  map_mem_cliqueComplex_iff (schreierIsoOfCommutes S e h) s

section Finite

variable [Fintype X] [DecidableEq X] [DecidableEq Γ]

/-- Explicit images of a finite generator set which contain all neighbors of
`x` in the undirected Schreier graph. -/
def schreierNeighborCandidates (S : Finset Γ) (x : X) : Finset X :=
  (S.image fun g => g • x) ∪ (S.image fun g => g⁻¹ • x)

omit [DecidableEq Γ] in
theorem neighborVertices_schreier_subset_candidates (S : Finset Γ) (x : X) :
    neighborVertices (schreierGraph (X := X) (S : Set Γ)) x ⊆
      schreierNeighborCandidates S x := by
  intro y hy
  rw [mem_neighborVertices_iff, schreierGraph_adj] at hy
  rcases hy with ⟨_, g, hg, hgy⟩ | ⟨_, g, hg, hgy⟩
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨g, hg, hgy⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    calc
      g⁻¹ • x = g⁻¹ • (g • y) := by rw [hgy]
      _ = y := by simp

omit [Fintype X] [DecidableEq Γ] in
theorem card_schreierNeighborCandidates_le (S : Finset Γ) (x : X) :
    (schreierNeighborCandidates S x).card ≤ 2 * S.card := by
  calc
    (schreierNeighborCandidates S x).card ≤
        (S.image fun g => g • x).card + (S.image fun g => g⁻¹ • x).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + S.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * S.card := by omega

omit [DecidableEq Γ] in
theorem card_neighborVertices_schreier_le (S : Finset Γ) (x : X) :
    (neighborVertices (schreierGraph (X := X) (S : Set Γ)) x).card ≤ 2 * S.card :=
  (Finset.card_le_card (neighborVertices_schreier_subset_candidates S x)).trans
    (card_schreierNeighborCandidates_le S x)

omit [DecidableEq Γ] in
/-- The number of one-vertex cofaces of a nonempty Schreier-clique face is
bounded directly by twice the number of selected generators. -/
theorem card_schreier_extensionVertices_le
    (S : Finset Γ) (s : Finset X) {x : X} (hx : x ∈ s) :
    (extensionVertices (schreierCliqueComplex (X := X) (S : Set Γ)) s).card ≤
      2 * S.card :=
  (card_extensionVertices_le_neighbors
    (schreierGraph (X := X) (S : Set Γ)) s hx).trans
      (card_neighborVertices_schreier_le S x)

end Finite

end Schreier

end QEC.Coding.HighDimensionalExpander.CayleyClique

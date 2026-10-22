import QEC.Coding.Stabilizer.FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Dai--Li planar embeddings and fixed-generator interactions

This module supplies the finite object language used by the Dai--Li locality
branch.  A planar embedding stores actual coordinates and a proof of unit
Euclidean separation.  Interactions are the unordered edges induced by one
fixed binary stabilizer presentation, so repeated support by several selected
generators never introduces multiplicity.

The thresholded count is the cardinality of a filtered finite edge set.  The
per-qubit Dai--Li counter is the degree in the corresponding threshold graph;
its total is therefore twice the number of distinct unordered long edges.
No generator-invariance claim is made.
-/

noncomputable section
open scoped Classical

namespace QEC
namespace Locality

/-- Euclidean distance on explicit real coordinate pairs. -/
def euclideanDistance2D (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

/-- Euclidean distance on coordinate pairs is symmetric. -/
theorem euclideanDistance2D_comm (x y : ℝ × ℝ) :
    euclideanDistance2D x y = euclideanDistance2D y x := by
  simp only [euclideanDistance2D]
  congr 1
  ring

/-- Euclidean distance on coordinate pairs is nonnegative. -/
theorem euclideanDistance2D_nonneg (x y : ℝ × ℝ) :
    0 ≤ euclideanDistance2D x y :=
  Real.sqrt_nonneg _

/-- A faithful two-dimensional embedding of finite qubits with unit separation. -/
structure UnitSeparatedEmbedding2D (ι : Type*) where
  point : ι → ℝ × ℝ
  unitSeparated : ∀ ⦃p q : ι⦄, p ≠ q → 1 ≤ euclideanDistance2D (point p) (point q)

namespace UnitSeparatedEmbedding2D

variable {ι : Type*}

/-- The distance between two embedded qubits. -/
def distance (embedding : UnitSeparatedEmbedding2D ι) (p q : ι) : ℝ :=
  euclideanDistance2D (embedding.point p) (embedding.point q)

/-- Embedded-qubit distance is symmetric. -/
theorem distance_comm (embedding : UnitSeparatedEmbedding2D ι) (p q : ι) :
    embedding.distance p q = embedding.distance q p :=
  euclideanDistance2D_comm _ _

/-- The stored unit-separation condition exposes the source convention directly. -/
theorem one_le_distance_of_ne (embedding : UnitSeparatedEmbedding2D ι)
    {p q : ι} (hpq : p ≠ q) :
    1 ≤ embedding.distance p q :=
  embedding.unitSeparated hpq

/-- Distance is nonnegative for every pair of embedded qubits. -/
theorem distance_nonneg (embedding : UnitSeparatedEmbedding2D ι) (p q : ι) :
    0 ≤ embedding.distance p q :=
  euclideanDistance2D_nonneg _ _

end UnitSeparatedEmbedding2D
end Locality

namespace Coding
namespace StabilizerCode
namespace BinaryStabilizerPresentation

open PauliSymplectic

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The Mathlib simple graph carried by the fixed-generator interaction relation. -/
def fixedGeneratorInteractionSimpleGraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : SimpleGraph ι where
  Adj := P.fixedGeneratorInteraction
  symm := by
    constructor
    intro p q hpq
    exact P.fixedGeneratorInteractionGraph_symmetric hpq
  loopless := ⟨fun p => P.fixedGeneratorInteractionGraph_loopless p⟩

/-- The finite set of distinct unordered interactions for the selected generators. -/
def fixedGeneratorInteractions
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) : Finset (Sym2 ι) := by
  classical
  exact P.fixedGeneratorInteractionSimpleGraph.edgeFinset

/-- An unordered pair is present exactly when one selected generator supports both endpoints. -/
@[simp]
theorem sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    s(p, q) ∈ P.fixedGeneratorInteractions ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by
  classical
  rw [fixedGeneratorInteractions, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  exact P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q

/-- The unordered interaction representation is invariant under swapping endpoints. -/
theorem sym2_mk_mem_fixedGeneratorInteractions_comm
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    s(p, q) ∈ P.fixedGeneratorInteractions ↔ s(q, p) ∈ P.fixedGeneratorInteractions := by
  rw [Sym2.eq_swap]

/-- Fixed-generator interactions contain no loops. -/
@[simp]
theorem sym2_diag_not_mem_fixedGeneratorInteractions
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p : ι) :
    s(p, p) ∉ P.fixedGeneratorInteractions := by
  simp

/-- Euclidean length of an unordered interaction in a fixed planar embedding. -/
def interactionLength (embedding : Locality.UnitSeparatedEmbedding2D ι) : Sym2 ι → ℝ :=
  Sym2.lift ⟨embedding.distance, embedding.distance_comm⟩

/-- Interaction length on an explicit pair is ordinary Euclidean distance. -/
@[simp]
theorem interactionLength_sym2_mk
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (p q : ι) :
    interactionLength embedding s(p, q) = embedding.distance p q :=
  rfl

/-- Every actual interaction has length at least one in a unit-separated embedding. -/
theorem one_le_interactionLength_of_mem
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {edge : Sym2 ι} (hedge : edge ∈ P.fixedGeneratorInteractions) :
    1 ≤ interactionLength embedding edge := by
  induction edge using Sym2.ind with
  | _ p q =>
      have hpq : p ≠ q :=
        (P.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support p q).1 hedge |>.1
      exact embedding.one_le_distance_of_ne hpq

/-- The finite unordered interactions whose Euclidean length meets a threshold. -/
def interactionsAtLengthAtLeast
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) : Finset (Sym2 ι) := by
  classical
  exact P.fixedGeneratorInteractions.filter
    (fun edge => threshold ≤ interactionLength embedding edge)

/-- Membership in the thresholded set is edge membership plus the length inequality. -/
@[simp]
theorem mem_interactionsAtLengthAtLeast_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (edge : Sym2 ι) :
    edge ∈ P.interactionsAtLengthAtLeast embedding threshold ↔
      edge ∈ P.fixedGeneratorInteractions ∧
        threshold ≤ interactionLength embedding edge := by
  classical
  simp [interactionsAtLengthAtLeast]

/-- Endpoint-level specification of thresholded fixed-generator interactions. -/
@[simp]
theorem sym2_mk_mem_interactionsAtLengthAtLeast_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (p q : ι) :
    s(p, q) ∈ P.interactionsAtLengthAtLeast embedding threshold ↔
      p ≠ q ∧
        (∃ j : κ, p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) ∧
        threshold ≤ embedding.distance p q := by
  simp [and_assoc]

/-- The long-interaction count is derived from the finite unordered-edge set. -/
def longInteractionCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) : Nat :=
  (P.interactionsAtLengthAtLeast embedding threshold).card

/-- The count is definitionally the finite cardinality, never supplied data. -/
theorem longInteractionCount_eq_card
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    P.longInteractionCount embedding threshold =
      (P.interactionsAtLengthAtLeast embedding threshold).card :=
  rfl

/-- Raising the length threshold can only remove unordered interactions. -/
theorem interactionsAtLengthAtLeast_anti_mono
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {low high : ℝ} (hlowhigh : low ≤ high) :
    P.interactionsAtLengthAtLeast embedding high ⊆
      P.interactionsAtLengthAtLeast embedding low := by
  intro edge hedge
  rw [P.mem_interactionsAtLengthAtLeast_iff] at hedge ⊢
  exact ⟨hedge.1, hlowhigh.trans hedge.2⟩

/-- Raising the length threshold cannot increase the unordered-edge count. -/
theorem longInteractionCount_anti_mono
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι)
    {low high : ℝ} (hlowhigh : low ≤ high) :
    P.longInteractionCount embedding high ≤ P.longInteractionCount embedding low :=
  Finset.card_le_card (P.interactionsAtLengthAtLeast_anti_mono embedding hlowhigh)

/-- The simple graph consisting exactly of thresholded fixed-generator interactions. -/
def longInteractionGraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) : SimpleGraph ι where
  Adj p q := P.fixedGeneratorInteraction p q ∧ threshold ≤ embedding.distance p q
  symm := by
    constructor
    rintro p q ⟨hpq, hlength⟩
    exact ⟨P.fixedGeneratorInteractionGraph_symmetric hpq,
      embedding.distance_comm p q ▸ hlength⟩
  loopless := ⟨fun p hp => P.fixedGeneratorInteractionGraph_loopless p hp.1⟩

/-- The long-interaction graph has exactly the filtered unordered edge set. -/
theorem longInteractionGraph_edgeFinset_eq
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (P.longInteractionGraph embedding threshold).edgeFinset =
      P.interactionsAtLengthAtLeast embedding threshold := by
  classical
  ext edge
  induction edge using Sym2.ind with
  | _ p q =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        P.mem_interactionsAtLengthAtLeast_iff, fixedGeneratorInteractions,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, interactionLength_sym2_mk]
      rfl

/-- The Dai--Li counter `f_{>=threshold}(q)` counts incident long interactions. -/
def daiLiInteractionCounter
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (q : ι) : Nat := by
  classical
  exact (P.longInteractionGraph embedding threshold).degree q

/-- Counter membership specification using actual generator support and Euclidean length. -/
theorem daiLiInteractionCounter_eq_neighborFinset_card
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) (q : ι) :
    P.daiLiInteractionCounter embedding threshold q =
      ((Finset.univ.filter fun r : ι =>
        q ≠ r ∧
          (∃ j : κ, q ∈ P.generatorSupport j ∧ r ∈ P.generatorSupport j) ∧
          threshold ≤ embedding.distance q r).card) := by
  classical
  rw [daiLiInteractionCounter, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  congr 1
  ext r
  simp [longInteractionGraph, fixedGeneratorInteraction, and_assoc]

/-- The total Dai--Li incidence counter is twice the distinct unordered long-edge count. -/
theorem sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : Locality.UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) =
      2 * P.longInteractionCount embedding threshold := by
  classical
  letI : DecidableRel (P.longInteractionGraph embedding threshold).Adj :=
    Classical.decRel _
  letI : Fintype (P.longInteractionGraph embedding threshold).edgeSet :=
    (P.longInteractionGraph embedding threshold).fintypeEdgeSet
  rw [show (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) =
      ∑ q : ι, (P.longInteractionGraph embedding threshold).degree q by rfl]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  change 2 * (P.longInteractionGraph embedding threshold).edgeFinset.card =
    2 * (P.interactionsAtLengthAtLeast embedding threshold).card
  congr 1
  apply congrArg Finset.card
  ext edge
  induction edge using Sym2.ind with
  | _ p q =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        P.mem_interactionsAtLengthAtLeast_iff, fixedGeneratorInteractions,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, interactionLength_sym2_mk]
      rfl

end BinaryStabilizerPresentation
end StabilizerCode
end Coding
end QEC

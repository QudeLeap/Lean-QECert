import QEC.Coding.Stabilizer.Parameters
import QEC.Locality.Graph.Core
/-!
# Fixed-generator interaction graphs

This module constructs the physical-qubit interaction graph determined by one
fixed binary stabilizer generator presentation.  Its adjacency and boundary
APIs reduce to the actual Pauli support of the selected generators; no
generator-invariance claim is made here.

Downstream internal users should import
`QEC.Coding.FixedGeneratorInteraction` directly.
-/

namespace QEC
namespace Coding
namespace StabilizerCode

open PauliSymplectic

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/--
Distinct qubits interact when one member of a fixed finite binary Pauli family
acts nontrivially on both. This family-level definition also supports
redundant Hamiltonian term presentations.
-/
def fixedGeneratorInteractionOf (generators : κ → Binary ι) (p q : ι) : Prop :=
  p ≠ q ∧ ∃ j : κ, p ∈ support (generators j) ∧ q ∈ support (generators j)

/-- The physical-qubit graph induced by a fixed finite binary Pauli family. -/
def fixedGeneratorInteractionGraphOf (generators : κ → Binary ι) :
    Locality.ConnectivityGraph ι where
  adjacent := fixedGeneratorInteractionOf generators
  symmetric := by
    intro p q h
    rcases h with ⟨hpq, j, hp, hq⟩
    exact ⟨hpq.symm, j, hq, hp⟩
  loopless := by
    intro p h
    exact h.1 rfl

omit [Fintype κ] in
/-- Family-level adjacency is exactly common actual Pauli support. -/
theorem fixedGeneratorInteractionGraphOf_adj_iff
    (generators : κ → Binary ι) (p q : ι) :
    (fixedGeneratorInteractionGraphOf generators).adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (generators j) ∧ q ∈ support (generators j) :=
  Iff.rfl

namespace BinaryStabilizerPresentation

/-- Distinct qubits interact when one fixed generator acts nontrivially on both. -/
def fixedGeneratorInteraction (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (p q : ι) : Prop :=
  p ≠ q ∧ ∃ j : κ, p ∈ P.generatorSupport j ∧ q ∈ P.generatorSupport j

/-- The physical-qubit graph induced by the selected fixed generator family. -/
def fixedGeneratorInteractionGraph
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Locality.ConnectivityGraph ι where
  adjacent := P.fixedGeneratorInteraction
  symmetric := by
    intro p q h
    rcases h with ⟨hpq, j, hp, hq⟩
    exact ⟨Ne.symm hpq, j, hq, hp⟩
  loopless := by
    intro p h
    exact h.1 rfl

/-- Adjacency is exactly common support in one selected generator. -/
theorem fixedGeneratorInteractionGraph_adj_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    P.fixedGeneratorInteractionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ, p ∈ P.generatorSupport j ∧ q ∈ P.generatorSupport j :=
  Iff.rfl

/-- Adjacency is exactly common actual Pauli support in one selected generator. -/
theorem fixedGeneratorInteractionGraph_adj_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    P.fixedGeneratorInteractionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) :=
  Iff.rfl

/-- The fixed-generator interaction graph is symmetric. -/
theorem fixedGeneratorInteractionGraph_symmetric
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) {p q : ι}
    (h : P.fixedGeneratorInteractionGraph.adjacent p q) :
    P.fixedGeneratorInteractionGraph.adjacent q p :=
  P.fixedGeneratorInteractionGraph.symmetric h

/-- The fixed-generator interaction graph has no loops. -/
theorem fixedGeneratorInteractionGraph_loopless
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p : ι) :
    ¬ P.fixedGeneratorInteractionGraph.adjacent p p :=
  P.fixedGeneratorInteractionGraph.loopless p

/-- Vertices outside `A` that interact with a vertex of `A` in the fixed graph. -/
def fixedGeneratorOuterBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) : Set ι :=
  {q | q ∉ A ∧ ∃ p : ι, p ∈ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q}

/-- Vertices of `A` that interact with a vertex outside `A` in the fixed graph. -/
def fixedGeneratorInnerBoundary
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) : Set ι :=
  {p | p ∈ A ∧ ∃ q : ι, q ∉ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q}

/-- Graph-level characterization of fixed-generator outer-boundary membership. -/
theorem mem_fixedGeneratorOuterBoundary_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (q : ι) :
    q ∈ P.fixedGeneratorOuterBoundary A ↔
      q ∉ A ∧ ∃ p : ι, p ∈ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q :=
  Iff.rfl

/-- Outer-boundary membership is witnessed by actual support of one fixed generator. -/
theorem mem_fixedGeneratorOuterBoundary_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (q : ι) :
    q ∈ P.fixedGeneratorOuterBoundary A ↔
      q ∉ A ∧ ∃ p : ι, p ∈ A ∧ p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by
  constructor
  · rintro ⟨hqA, p, hpA, hpq⟩
    rcases (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hpq with
      ⟨hpq, j, hpj, hqj⟩
    exact ⟨hqA, p, hpA, hpq, j, hpj, hqj⟩
  · rintro ⟨hqA, p, hpA, hpq, j, hpj, hqj⟩
    exact ⟨hqA, p, hpA,
      (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hpj, hqj⟩⟩

/-- Graph-level characterization of fixed-generator inner-boundary membership. -/
theorem mem_fixedGeneratorInnerBoundary_iff
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (p : ι) :
    p ∈ P.fixedGeneratorInnerBoundary A ↔
      p ∈ A ∧ ∃ q : ι, q ∉ A ∧ P.fixedGeneratorInteractionGraph.adjacent p q :=
  Iff.rfl

/-- Inner-boundary membership is witnessed by actual support of one fixed generator. -/
theorem mem_fixedGeneratorInnerBoundary_iff_actual_support
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A : Set ι) (p : ι) :
    p ∈ P.fixedGeneratorInnerBoundary A ↔
      p ∈ A ∧ ∃ q : ι, q ∉ A ∧ p ≠ q ∧ ∃ j : κ,
        p ∈ support (P.generators j) ∧ q ∈ support (P.generators j) := by
  constructor
  · rintro ⟨hpA, q, hqA, hpq⟩
    rcases (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hpq with
      ⟨hpq, j, hpj, hqj⟩
    exact ⟨hpA, q, hqA, hpq, j, hpj, hqj⟩
  · rintro ⟨hpA, q, hqA, hpq, j, hpj, hqj⟩
    exact ⟨hpA, q, hqA,
      (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hpj, hqj⟩⟩

/-- The fixed interaction graph has no edge between the two regions. -/
def fixedGeneratorNoCrossEdge
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) : Prop :=
  ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B →
    ¬ P.fixedGeneratorInteractionGraph.adjacent p q

/--
The fixed interaction graph has no cross-edge exactly when no selected generator
has actual Pauli support on distinct vertices across the two regions.
-/
theorem fixedGeneratorNoCrossEdge_iff_no_cross_interaction
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) :
    P.fixedGeneratorNoCrossEdge A B ↔
      ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B → p ≠ q →
        ∀ j : κ,
          ¬ (p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · intro h p hp q hq hpq j hsupport
    exact h hp hq
      ((P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).2
        ⟨hpq, j, hsupport.1, hsupport.2⟩)
  · intro h p hp q hq hpq
    rcases (P.fixedGeneratorInteractionGraph_adj_iff_actual_support p q).1 hpq with
      ⟨hpq, j, hpj, hqj⟩
    exact h hp hq hpq j ⟨hpj, hqj⟩

/--
Source-level fixed-generator decoupling requires disjoint regions and no
interaction-graph edge between them.
-/
def fixedGeneratorDecoupled
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) : Prop :=
  Disjoint A B ∧ P.fixedGeneratorNoCrossEdge A B

/--
Fixed-generator decoupling holds exactly when the regions are disjoint and no
selected generator has actual Pauli support in both regions.
-/
theorem fixedGeneratorDecoupled_iff_disjoint_no_cross_interaction
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (A B : Set ι) :
    P.fixedGeneratorDecoupled A B ↔
      Disjoint A B ∧ ∀ ⦃p : ι⦄, p ∈ A → ∀ ⦃q : ι⦄, q ∈ B →
        ∀ j : κ,
          ¬ (p ∈ support (P.generators j) ∧ q ∈ support (P.generators j)) := by
  constructor
  · rintro ⟨hdisjoint, hnoedge⟩
    refine ⟨hdisjoint, ?_⟩
    have hsupport :=
      (P.fixedGeneratorNoCrossEdge_iff_no_cross_interaction A B).1 hnoedge
    intro p hp q hq j hpq
    have hne : p ≠ q := by
      intro hpq
      subst q
      exact (Set.disjoint_left.1 hdisjoint) hp hq
    exact hsupport hp hq hne j hpq
  · rintro ⟨hdisjoint, hsupport⟩
    refine ⟨hdisjoint, ?_⟩
    refine (P.fixedGeneratorNoCrossEdge_iff_no_cross_interaction A B).2 ?_
    intro p hp q hq _hne j hpq
    exact hsupport hp hq j hpq

/-- A region cannot be source-level decoupled from itself when it contains a vertex. -/
theorem not_fixedGeneratorDecoupled_singleton_self
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (x : ι) :
    ¬ P.fixedGeneratorDecoupled ({x} : Set ι) {x} := by
  intro hdecoupled
  have hx : x ∈ ({x} : Set ι) := by simp
  exact (Set.disjoint_left.1 hdecoupled.1) hx hx

end BinaryStabilizerPresentation
end StabilizerCode
end Coding
end QEC

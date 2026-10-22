import QEC.Coding.Stabilizer.FixedGeneratorInteraction
import QEC.Locality.Core.Definitions
/-!
# Selected local stabilizer Hamiltonians

This module records a finite, possibly redundant family of selected binary
Pauli stabilizer terms. The family generates an existing source-valid
stabilizer code, has actual geometrically local support, and uses the fixed
unit-coefficient normalization.

Energy barriers and thermal dynamics are deliberately not fields of this
interface.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode

open PauliSymplectic
open scoped BigOperators

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/--
A source-valid binary stabilizer code together with its actual selected local
Hamiltonian terms.

The selected family may be redundant. This is essential for standard local
Hamiltonians whose full check family has global relations.
-/
structure LocalStabilizerHamiltonian where
  code : SourceValidBinary ι
  generators : κ → Binary ι
  generated_eq : generatedStabilizerSet generators = code.1.generatedGroup
  generator_self_adjoint : ∀ j,
    LinearMap.adjoint (toQubitOperator (generators j)) =
      toQubitOperator (generators j)
  geometry : Locality.LatticeGeometry ι
  interactionRange : Nat
  interactionRange_positive : 0 < interactionRange
  local_support : ∀ j,
    Locality.BoundedDiameter geometry (support (generators j) : Set ι)
      interactionRange
  participationBound : Nat
  participationBound_positive : 0 < participationBound
  participation_le : ∀ i,
    (Finset.univ.filter fun j => i ∈ support (generators j)).card ≤
      participationBound

namespace LocalStabilizerHamiltonian

/-- The actual finite support of one selected Hamiltonian term. -/
def generatorSupport (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (j : κ) : Finset ι :=
  support (H.generators j)

@[simp]
theorem generatorSupport_eq_support
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    H.generatorSupport j = support (H.generators j) :=
  rfl

/-- One selected generator belongs to the existing code's generated group. -/
theorem generator_mem_generatedGroup
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    H.generators j ∈ H.code.1.generatedGroup := by
  rw [← H.generated_eq]
  exact GeneratedStabilizer.generator j

/-- The selected binary generators commute because they lie in the same stabilizer. -/
theorem generators_commute
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commutes (H.generators j) (H.generators k) :=
  H.code.1.generatedGroup_pairwise_commutes
    (H.generator_mem_generatedGroup j) (H.generator_mem_generatedGroup k)

/-- The fixed interaction graph uses the shared actual-support construction. -/
def interactionGraph
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    Locality.ConnectivityGraph ι :=
  fixedGeneratorInteractionGraphOf H.generators

/-- Interaction-graph adjacency is common support in one selected term. -/
theorem interactionGraph_adj_iff
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (p q : ι) :
    H.interactionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ H.generatorSupport j ∧ q ∈ H.generatorSupport j :=
  Iff.rfl

/-- The recorded locality bound applies to the actual selected-term support. -/
theorem generatorSupport_boundedDiameter
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    Locality.BoundedDiameter H.geometry (H.generatorSupport j : Set ι)
      H.interactionRange :=
  H.local_support j

/-- The checks incident on one physical qubit. -/
def incidentGenerators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (i : ι) : Finset κ :=
  Finset.univ.filter fun j => i ∈ H.generatorSupport j

/-- The number of selected terms incident on a qubit obeys the recorded bound. -/
theorem incidentGenerators_card_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (i : ι) :
    (H.incidentGenerators i).card ≤ H.participationBound :=
  H.participation_le i

/-- The represented self-adjoint stabilizer operator of one selected check. -/
noncomputable def generatorOperator
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  toQubitOperator (H.generators j)

/-- The unit-coefficient Hamiltonian term associated with one selected check. -/
noncomputable def term
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  -(H.generatorOperator j)

/-- The selected unit-coefficient commuting stabilizer Hamiltonian. -/
noncomputable def operator
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  ∑ j, H.term j

@[simp]
theorem generatorOperator_adjoint_eq_self
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    LinearMap.adjoint (H.generatorOperator j) = H.generatorOperator j :=
  H.generator_self_adjoint j

@[simp]
theorem term_adjoint_eq_self
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    LinearMap.adjoint (H.term j) = H.term j := by
  simp [term]

/-- Selected concrete generator operators commute. -/
theorem generatorOperator_commute
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commute (H.generatorOperator j) (H.generatorOperator k) := by
  exact toQubitOperator_commute_of_commutes
      (H.generators j) (H.generators k) (H.generators_commute j k)

/-- Unit-coefficient Hamiltonian terms commute. -/
theorem term_commute
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commute (H.term j) (H.term k) := by
  simpa [term] using (H.generatorOperator_commute j k).neg_left.neg_right

/-- The finite unit-coefficient Hamiltonian is self-adjoint. -/
theorem operator_adjoint_eq_self
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    LinearMap.adjoint H.operator = H.operator := by
  simp [operator]

end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC

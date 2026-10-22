import QEC.Semantics.Instruments.Sequential.Composition
/-!
# Dependent finite sequential instrument composition

This module constructs sequential finite instruments whose second raw Kraus
index and observed outcome types depend on the first observed outcome. The
composite raw index is the actual dependent sigma type over first raw branches.
-/

universe u v w x y

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

namespace FiniteInstrument

variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

/--
Sequentially bind a finite instrument to a family of second instruments whose
raw and observed types are selected by the first observed outcome.

The first component of each composite raw index records the actual first
Kraus branch, so the dependent second raw-index fibre is selected by its
observation rather than by a fixed surrogate type.
-/
noncomputable def bindDependent (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L) :
    FiniteInstrument (Sigma fun firstIndex : κ => κ₂ (I.observe firstIndex)) (Sigma Ξ) H L where
  kraus :=
    { operator index :=
      ((J (I.observe index.1)).kraus.operator index.2).comp
        (I.kraus.operator index.1) }
  observe := fun index =>
    ⟨I.observe index.1, (J (I.observe index.1)).observe index.2⟩

/-- A dependent composite raw branch is the selected second branch after its first branch. -/
theorem bindDependent_kraus_operator (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ₂ (I.observe firstIndex)) :
    (I.bindDependent J).kraus.operator ⟨firstIndex, secondIndex⟩ =
      ((J (I.observe firstIndex)).kraus.operator secondIndex).comp
        (I.kraus.operator firstIndex) :=
  rfl

/-- A dependent composite observation records both actual stage observations. -/
theorem bindDependent_observe (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (firstIndex : κ) (secondIndex : κ₂ (I.observe firstIndex)) :
    (I.bindDependent J).observe ⟨firstIndex, secondIndex⟩ =
      ⟨I.observe firstIndex, (J (I.observe firstIndex)).observe secondIndex⟩ :=
  rfl

/-- The induced map decomposes over the actual dependent raw-index fibres. -/
theorem bindDependent_inducedMap_apply (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (A : Operator H) :
    (I.bindDependent J).kraus.inducedMap A =
      ∑ firstIndex : κ,
        (J (I.observe firstIndex)).kraus.inducedMap
          ((I.kraus.operator firstIndex).comp
            (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by
  ext x
  simp only [FiniteKrausFamily.inducedMap_apply, bindDependent,
    LinearMap.adjoint_comp, LinearMap.comp_apply, LinearMap.sum_apply,
    Fintype.sum_sigma]

/-- Completeness is preserved by dependent finite sequential binding. -/
theorem bindDependent_complete (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) :
    (I.bindDependent J).kraus.Complete := by
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [I.bindDependent_inducedMap_apply J A, map_sum]
  calc
    (∑ firstIndex : κ,
        LinearMap.trace Complex L
          ((J (I.observe firstIndex)).kraus.inducedMap
            ((I.kraus.operator firstIndex).comp
              (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))))) =
        ∑ firstIndex : κ,
          LinearMap.trace Complex K
            ((I.kraus.operator firstIndex).comp
              (A.comp (LinearMap.adjoint (I.kraus.operator firstIndex)))) := by
          apply Finset.sum_congr rfl
          intro firstIndex _
          exact
            (J (I.observe firstIndex)).kraus.inducedMap_trace_preserving
              (hJ (I.observe firstIndex)) _
    _ = LinearMap.trace Complex K (I.kraus.inducedMap A) := by
          rw [FiniteKrausFamily.inducedMap_apply, map_sum]
    _ = LinearMap.trace Complex H A :=
          I.kraus.inducedMap_trace_preserving hI A

/-- Complete dependent sequential binding has normalized total observable Born mass. -/
theorem bindDependent_sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome, (I.bindDependent J).bornWeight outcome rho = 1 :=
  (I.bindDependent J).sum_bornWeight_eq_one (I.bindDependent_complete J hI hJ) rho

end FiniteInstrument

end
end Semantics
end QEC

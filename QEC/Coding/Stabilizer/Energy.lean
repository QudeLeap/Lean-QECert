import QEC.Coding.Stabilizer.ErrorPath

/-!
# Selected-generator stabilizer excitation energy

This module identifies violated selected stabilizer generators with the support
of the existing M3 generator-indexed syndrome. It then fixes the BT09 excess
energy normalization and proves how each unit Hamiltonian term acts on a Pauli
error applied to a codeword.

All counts depend on the selected generator family. The unit-defect count is
not identified here with any geometric loop length; that specialization belongs
to the later four-dimensional toric-code route.
-/

noncomputable section

namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian

open PauliSymplectic
open scoped Classical

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

/-- The selected Hamiltonian terms violated by a binary Pauli error. -/
def violatedGenerators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Finset κ :=
  Finset.univ.filter fun j => ¬ Commutes E (H.generators j)

/-- The support of the existing M3 syndrome for the selected generator family. -/
def syndromeSupport
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Finset κ :=
  Finset.univ.filter fun j =>
    stabilizerSyndrome H.generators E j = 1

/-- The Hamming weight of the selected generator-indexed syndrome. -/
def syndromeWeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Nat :=
  (H.syndromeSupport E).card

/--
Energy with one unit assigned to each violated selected term.

For the later 4D route, a separate geometric theorem must identify this count
with the length of the appropriate defect loop.
-/
def unitDefectEnergy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Nat :=
  (H.violatedGenerators E).card

/--
The BT09 excess energy for the fixed unit-coefficient Hamiltonian convention.

Each violated term changes its eigenvalue from `-1` to `+1`, hence contributes
two units above the common ground sector.
-/
def btExcessEnergy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) : Nat :=
  2 * H.unitDefectEnergy E

@[simp]
theorem mem_violatedGenerators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (j : κ) :
    j ∈ H.violatedGenerators E ↔ ¬ Commutes E (H.generators j) := by
  simp [violatedGenerators]

@[simp]
theorem mem_syndromeSupport
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (j : κ) :
    j ∈ H.syndromeSupport E ↔
      stabilizerSyndrome H.generators E j = 1 := by
  simp only [syndromeSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Violated selected terms are exactly the nonzero selected syndrome bits. -/
theorem violatedGenerators_eq_syndromeSupport
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators E = H.syndromeSupport E := by
  ext j
  simp [stabilizerSyndromeBit_eq_one_iff_not_commutes]

/-- Unit-defect energy is exactly the selected syndrome weight. -/
theorem unitDefectEnergy_eq_syndromeWeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.unitDefectEnergy E = H.syndromeWeight E := by
  rw [unitDefectEnergy, syndromeWeight, violatedGenerators_eq_syndromeSupport]

/-- BT09 excess energy is twice the selected syndrome weight. -/
theorem btExcessEnergy_eq_two_mul_syndromeWeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy E = 2 * H.syndromeWeight E := by
  rw [btExcessEnergy, unitDefectEnergy_eq_syndromeWeight]

/--
The fixed normalization bridge from one-unit defect energy to BT09 excess
energy. A later 4D theorem supplies the geometric loop-length identification.
-/
theorem btExcessEnergy_eq_two_mul_unitDefectEnergy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy E = 2 * H.unitDefectEnergy E :=
  rfl

@[simp]
theorem syndromeSupport_binaryOne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.syndromeSupport binaryOne = ∅ := by
  ext j
  simp [syndromeSupport, stabilizerSyndrome, stabilizerSyndromeBit,
    binaryOne, symplecticForm]

@[simp]
theorem violatedGenerators_binaryOne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.violatedGenerators binaryOne = ∅ := by
  rw [violatedGenerators_eq_syndromeSupport, syndromeSupport_binaryOne]

@[simp]
theorem syndromeWeight_binaryOne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.syndromeWeight binaryOne = 0 := by
  simp [syndromeWeight]

@[simp]
theorem unitDefectEnergy_binaryOne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.unitDefectEnergy binaryOne = 0 := by
  simp [unitDefectEnergy]

@[simp]
theorem btExcessEnergy_binaryOne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.btExcessEnergy binaryOne = 0 := by
  simp [btExcessEnergy]

/--
The selected generator operator fixes every vector in the existing source-valid
code. This derives fixedness from generated-group membership rather than adding
it as a Hamiltonian field.
-/
theorem generatorOperator_apply_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.generatorOperator j ψ = ψ := by
  exact
    (H.code.2.2 ψ).1 hψ (H.generators j)
      (H.generator_mem_generatedGroup j)

/--
On a Pauli-error codeword, one selected generator has eigenvalue `+1` when it
commutes with the error and `-1` when it anticommutes.
-/
theorem generatorOperator_apply_error_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.generatorOperator j (toQubitOperator E ψ) =
      if Commutes E (H.generators j) then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by
  let S := H.generators j
  have hfix : toQubitOperator S ψ = ψ := by
    exact H.generatorOperator_apply_codeword ψ hψ j
  change toQubitOperator S (toQubitOperator E ψ) =
    if Commutes E S then
      toQubitOperator E ψ
    else
      -(toQubitOperator E ψ)
  by_cases hcommutes : Commutes E S
  · simp only [hcommutes, if_true]
    change (toQubitOperator S * toQubitOperator E) ψ =
      toQubitOperator E ψ
    rw [← toQubitOperator_commute_of_commutes E S hcommutes]
    simp [Module.End.mul_apply, hfix]
  · simp only [hcommutes, if_false]
    have hreverse : ¬ Commutes S E := by
      intro hSE
      exact hcommutes ((commutes_comm E S).2 hSE)
    change (toQubitOperator S * toQubitOperator E) ψ =
      -(toQubitOperator E ψ)
    rw [toQubitOperator_anticommute_of_not_commutes S E hreverse]
    simp [Module.End.mul_apply, hfix]

/--
For the unit Hamiltonian term `-S_j`, a violated term contributes the excited
`+1` branch and an unviolated term contributes the ground `-1` branch.
-/
theorem term_apply_error_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) (j : κ) :
    H.term j (toQubitOperator E ψ) =
      if j ∈ H.violatedGenerators E then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by
  change -(H.generatorOperator j (toQubitOperator E ψ)) =
    if j ∈ H.violatedGenerators E then
      toQubitOperator E ψ
    else
      -(toQubitOperator E ψ)
  rw [H.generatorOperator_apply_error_codeword E ψ hψ j]
  by_cases hcommutes : Commutes E (H.generators j)
  · simp [hcommutes]
  · simp [hcommutes]

/-- The full Hamiltonian is the sum of its selected excited/ground branches. -/
theorem operator_apply_error_codeword
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (ψ : Semantics.Qubit.QubitRegister ι)
    (hψ : ψ ∈ H.code.1.code.carrier) :
    H.operator (toQubitOperator E ψ) =
      ∑ j, if j ∈ H.violatedGenerators E then
        toQubitOperator E ψ
      else
        -(toQubitOperator E ψ) := by
  rw [operator, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  exact H.term_apply_error_codeword E ψ hψ j

/--
The combinatorial energy depends only on the literal selected generator family,
not on the remaining locality metadata of its Hamiltonian presentation.
-/
theorem btExcessEnergy_congr_generators
    (H K : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (hgenerators : H.generators = K.generators) (E : Binary ι) :
    H.btExcessEnergy E = K.btExcessEnergy E := by
  simp [btExcessEnergy, unitDefectEnergy, violatedGenerators, hgenerators]

end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC

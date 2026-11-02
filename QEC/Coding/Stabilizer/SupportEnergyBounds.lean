import QEC.Coding.Stabilizer.PathEnergy

/-!
# Support and participation bounds for Pauli-error energy
-/

noncomputable section

namespace QEC
namespace Coding

open PauliSymplectic
open scoped Classical

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

namespace StabilizerCode.LocalStabilizerHamiltonian

variable {κ : Type*} [Fintype κ]

/-- Selected generators incident on at least one site of a finite region. -/
def incidentGeneratorUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Finset κ :=
  R.biUnion H.incidentGenerators

theorem card_incidentGeneratorUnion_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    (H.incidentGeneratorUnion R).card ≤
      R.card * H.participationBound := by
  exact
    Finset.card_biUnion_le_card_mul R H.incidentGenerators
      H.participationBound fun i _hi => H.incidentGenerators_card_le i

theorem mem_incidentGeneratorUnion_of_mem_generatorSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (i : ι) (j : κ)
    (hiR : i ∈ R) (hij : i ∈ support (H.generators j)) :
    j ∈ H.incidentGeneratorUnion R := by
  rw [incidentGeneratorUnion, Finset.mem_biUnion]
  refine ⟨i, hiR, ?_⟩
  simpa [incidentGenerators, generatorSupport] using hij

end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC

namespace QEC
namespace Coding
namespace StabilizerCode
namespace LocalStabilizerHamiltonian

open PauliSymplectic
open scoped Classical

universe u

variable {κ : Type u} [Fintype κ]

/-- Every violated selected generator is incident on the error support. -/
theorem violatedGenerators_subset_incidentGeneratorUnion_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators E ⊆ H.incidentGeneratorUnion (support E) := by
  intro j hj
  rw [mem_violatedGenerators] at hj
  have hnotDisjoint :
      ¬ Disjoint (support E) (support (H.generators j)) := by
    intro hdisjoint
    exact hj
      (QEC.Locality.commutes_of_disjoint_support
        E (H.generators j) hdisjoint)
  obtain ⟨i, hiE, hiGenerator⟩ :=
    Finset.not_disjoint_iff.mp hnotDisjoint
  exact
    H.mem_incidentGeneratorUnion_of_mem_generatorSupport
      (support E) i j hiE hiGenerator

/-- A finite-support error has energy bounded by support size times participation. -/
theorem btExcessEnergy_le_two_mul_support_card_mul_participationBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy E ≤
      2 * (support E).card * H.participationBound := by
  have hsubset :=
    H.violatedGenerators_subset_incidentGeneratorUnion_support E
  have hincident :=
    H.card_incidentGeneratorUnion_le (support E)
  unfold btExcessEnergy unitDefectEnergy
  calc
    2 * (H.violatedGenerators E).card
        ≤ 2 * (H.incidentGeneratorUnion (support E)).card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)
    _ ≤ 2 * (support E).card * H.participationBound := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hincident

end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC

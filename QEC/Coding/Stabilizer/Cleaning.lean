import QEC.Coding.Stabilizer.LocalHamiltonian
import QEC.Locality.CorrectableRegions.CorrectableRegionClosure
/-!
# Stabilizer cleaning dichotomy

This module proves the source-faithful stabilizer cleaning dichotomy for an
arbitrary finite qubit region. The cleaning operator is generated only by the
selected Hamiltonian terms whose literal supports meet the region.

The theorem assumes neither erasure correctability nor generator independence,
and it contains no geometric strip conclusion.
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

/-- A selected generator meets a physical region when their supports intersect. -/
def GeneratorMeets
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (j : κ) : Prop :=
  ¬ Disjoint (H.generatorSupport j) R

/-- The selected-generator indices whose literal supports meet a region. -/
def MeetingIndex
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :=
  {j : κ // H.GeneratorMeets R j}

instance instFiniteMeetingIndex
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Finite (H.MeetingIndex R) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance instFintypeMeetingIndex
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) : Fintype (H.MeetingIndex R) :=
  Fintype.ofFinite _

/-- Actual Pauli products generated only by selected terms meeting the region. -/
def GeneratedByMeeting
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (S : Binary ι) : Prop :=
  GeneratedStabilizer
    (fun j : H.MeetingIndex R => H.generators j.1) S

/-- The vector span of selected generators whose supports meet the region. -/
def meetingGeneratorSubspace
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι) :=
  Submodule.span (ZMod 2)
    (Set.range fun j : H.MeetingIndex R => (H.generators j.1).vector)

/-- The existing generated stabilizer subspace is spanned by the selected family. -/
theorem generatedVectorSubspace_eq_span_generators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.code.1.generatedVectorSubspace =
      Submodule.span (ZMod 2)
        (Set.range fun j => (H.generators j).vector) := by
  apply le_antisymm
  · rintro vector ⟨S, hS, rfl⟩
    rw [← H.generated_eq] at hS
    induction hS with
    | one =>
        change (0 : SymplecticVector (ZMod 2) ι) ∈ _
        exact Submodule.zero_mem _
    | generator j =>
        exact Submodule.subset_span ⟨j, rfl⟩
    | mul _ _ ihS ihT =>
        exact Submodule.add_mem _ ihS ihT
    | dagger _ ihS =>
        simpa [binaryDagger] using ihS
  · apply Submodule.span_le.2
    rintro vector ⟨j, rfl⟩
    exact ⟨H.generators j, H.generator_mem_generatedGroup j, rfl⟩

/-- A product of meeting generators is an element of the full stabilizer group. -/
theorem generatedByMeeting_mem_generatedGroup
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (S : Binary ι)
    (hS : H.GeneratedByMeeting R S) :
    S ∈ H.code.1.generatedGroup := by
  rw [← H.generated_eq]
  change GeneratedStabilizer H.generators S
  induction hS with
  | one => exact .one
  | generator j => exact .generator j.1
  | mul _ _ ihS ihT => exact .mul ihS ihT
  | dagger _ ihS => exact .dagger ihS

/-- Meeting-generator span membership has an actual Pauli-product witness. -/
theorem mem_meetingGeneratorSubspace_iff_exists_generatedByMeeting
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (vector : SymplecticVector (ZMod 2) ι) :
    vector ∈ H.meetingGeneratorSubspace R ↔
      ∃ S : Binary ι, H.GeneratedByMeeting R S ∧ S.vector = vector := by
  constructor
  · intro hvector
    unfold meetingGeneratorSubspace at hvector
    induction hvector using Submodule.span_induction with
    | mem vector hmem =>
        rcases hmem with ⟨j, rfl⟩
        exact ⟨H.generators j.1, .generator j, rfl⟩
    | zero =>
        exact ⟨binaryOne, .one, rfl⟩
    | add x y _ _ ihx ihy =>
        rcases ihx with ⟨S, hS, hSv⟩
        rcases ihy with ⟨T, hT, hTv⟩
        refine ⟨binaryMul S T, .mul hS hT, ?_⟩
        rw [← hSv, ← hTv]
        rfl
    | smul c x _ ihx =>
        rcases ihx with ⟨S, hS, hSv⟩
        by_cases hc : c = 0
        · subst c
          refine ⟨binaryOne, .one, ?_⟩
          apply (SymplecticVector.toProdEquiv
            (F := ZMod 2) (ι := ι)).injective
          simp [binaryOne, SymplecticVector.toProdEquiv]
        · have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero hc
          subst c
          exact ⟨S, hS, by simpa using hSv⟩
  · rintro ⟨S, hS, rfl⟩
    induction hS with
    | one =>
        change (0 : SymplecticVector (ZMod 2) ι) ∈ _
        exact Submodule.zero_mem _
    | generator j =>
        exact Submodule.subset_span ⟨j, rfl⟩
    | mul _ _ ihS ihT =>
        exact Submodule.add_mem (H.meetingGeneratorSubspace R) ihS ihT
    | dagger _ ihS =>
        simpa [binaryDagger] using ihS

/-- A Pauli supported in a region has its vector in that coordinate subspace. -/
theorem vector_mem_coordinateSubspace_of_support_subset
    (R : Finset ι) (E : Binary ι) (hE : support E ⊆ R) :
    E.vector ∈ Locality.coordinateSubspace R := by
  let localVector : SymplecticVector (ZMod 2) {i : ι // i ∈ R} :=
    { xPart := fun i => E.vector.xPart i.1
      zPart := fun i => E.vector.zPart i.1 }
  refine ⟨localVector, ?_⟩
  apply (SymplecticVector.toProdEquiv (F := ZMod 2) (ι := ι)).injective
  apply Prod.ext <;> funext i
  · by_cases hi : i ∈ R
    · simp [Locality.embedCoordinateVector, localVector, hi,
        SymplecticVector.toProdEquiv]
    · have hiSupport : i ∉ support E := fun hiE => hi (hE hiE)
      have hxi : E.vector.xPart i = 0 := by
        by_contra hx
        exact hiSupport ((mem_support E i).2
          (Or.inl ((mem_binarySupport _ i).2 hx)))
      simp [Locality.embedCoordinateVector, localVector, hi, hxi,
        SymplecticVector.toProdEquiv]
  · by_cases hi : i ∈ R
    · simp [Locality.embedCoordinateVector, localVector, hi,
        SymplecticVector.toProdEquiv]
    · have hiSupport : i ∉ support E := fun hiE => hi (hE hiE)
      have hzi : E.vector.zPart i = 0 := by
        by_contra hz
        exact hiSupport ((mem_support E i).2
          (Or.inr ((mem_binarySupport _ i).2 hz)))
      simp [Locality.embedCoordinateVector, localVector, hi, hzi,
        SymplecticVector.toProdEquiv]

/--
BT09 Cleaning Lemma: either the region supports a nontrivial logical Pauli, or
every normalizer representative can be cleaned from the region using only
selected generators that meet it.
-/
theorem stabilizerCleaningDichotomy
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) :
    (∃ P : Binary ι,
      H.code.1.InBinaryNormalizer P ∧
      ¬ H.code.1.InGeneratedGroupUpToSign P ∧
      support P ⊆ R) ∨
    (∀ P : Binary ι, H.code.1.InBinaryNormalizer P →
      ∃ S : Binary ι,
        H.GeneratedByMeeting R S ∧
        S ∈ H.code.1.generatedGroup ∧
        H.code.1.InBinaryNormalizer (binaryMul P S) ∧
        support (binaryMul P S) ⊆ Rᶜ) := by
  classical
  by_cases hlocal :
      ∃ P : Binary ι,
        H.code.1.InBinaryNormalizer P ∧
        ¬ H.code.1.InGeneratedGroupUpToSign P ∧
        support P ⊆ R
  · exact Or.inl hlocal
  · right
    let L := H.code.1.generatedVectorSubspace
    let N := FiniteSymplectic.form.orthogonal L
    let W := Locality.coordinateSubspace R
    let A := H.meetingGeneratorSubspace R
    have hNoLocal : N ⊓ W ≤ L := by
      rintro vector ⟨hN, hW⟩
      let E : Binary ι := { phase := 0, vector := vector }
      have hNormalizer : H.code.1.InBinaryNormalizer E := by
        apply (H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer E).1
        simpa [N, L, E] using hN
      have hSupport : support E ⊆ R :=
        Locality.support_subset_of_vector_mem_coordinateSubspace R E
          (by simpa [W, E] using hW)
      by_contra hnotL
      apply hlocal
      refine ⟨E, hNormalizer, ?_, hSupport⟩
      intro hGenerated
      exact hnotL ((H.code.1.vector_mem_generatedVectorSubspace_iff E).2
        hGenerated)
    have hOrthogonalSubset :
        FiniteSymplectic.form.orthogonal
            (A ⊔ FiniteSymplectic.form.orthogonal W) ≤ L := by
      rw [Locality.symplectic_orthogonal_sup_eq_inf,
        LinearMap.BilinForm.orthogonal_orthogonal
          FiniteSymplectic.form_nondegenerate
          FiniteSymplectic.form_isAlt.isRefl]
      rintro vector ⟨hAOrthogonal, hW⟩
      apply hNoLocal
      refine ⟨?_, hW⟩
      change vector ∈
        FiniteSymplectic.form.orthogonal
          H.code.1.generatedVectorSubspace
      rw [H.generatedVectorSubspace_eq_span_generators]
      intro stabilizerVector hStabilizer
      induction hStabilizer using Submodule.span_induction with
      | mem generatorVector hGenerator =>
          rcases hGenerator with ⟨j, rfl⟩
          by_cases hj : H.GeneratorMeets R j
          · exact hAOrthogonal (H.generators j).vector
              (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
          · have hdisjoint : Disjoint (H.generatorSupport j) R := by
              simpa [GeneratorMeets] using hj
            have hsupport : support (H.generators j) ⊆ Rᶜ := by
              intro i hi
              exact Finset.mem_compl.mpr fun hiR =>
                (Finset.disjoint_left.mp hdisjoint hi hiR)
            have hgeneratorWOrthogonal :
                (H.generators j).vector ∈
                  FiniteSymplectic.form.orthogonal W := by
              change (H.generators j).vector ∈
                FiniteSymplectic.form.orthogonal
                  (Locality.coordinateSubspace R)
              rw [Locality.orthogonal_coordinateSubspace]
              exact vector_mem_coordinateSubspace_of_support_subset
                Rᶜ (H.generators j) hsupport
            exact
              FiniteSymplectic.form_isAlt.isRefl.eq_iff.mp
                (hgeneratorWOrthogonal vector hW)
      | zero =>
          change symplecticForm 0 vector = 0
          simp [symplecticForm]
      | add x y _ _ ihx ihy =>
          change symplecticForm (x + y) vector = 0
          change symplecticForm x vector = 0 at ihx
          change symplecticForm y vector = 0 at ihy
          rw [Locality.symplecticForm_add_left, ihx, ihy, add_zero]
      | smul c x _ ihx =>
          change symplecticForm x vector = 0 at ihx
          change symplecticForm (c • x) vector = 0
          by_cases hc : c = 0
          · subst c
            rw [zero_smul]
            change (FiniteSymplectic.form 0) vector = 0
            rw [map_zero]
            rfl
          · have hc1 : c = 1 := zmod_two_eq_one_of_ne_zero hc
            subst c
            simpa using ihx
    have hClean : N ≤ A ⊔ FiniteSymplectic.form.orthogonal W := by
      have hReverse :=
        LinearMap.BilinForm.orthogonal_le
          (B := FiniteSymplectic.form) hOrthogonalSubset
      rw [LinearMap.BilinForm.orthogonal_orthogonal
          FiniteSymplectic.form_nondegenerate
          FiniteSymplectic.form_isAlt.isRefl] at hReverse
      simpa [N, L] using hReverse
    intro P hP
    have hPVector : P.vector ∈ N := by
      simpa [N, L] using
        (H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer P).2 hP
    rcases Submodule.mem_sup.mp (hClean hPVector) with
      ⟨meetingVector, hMeeting, outsideVector, hOutside, hsum⟩
    obtain ⟨S, hSMeeting, hSVector⟩ :=
      (H.mem_meetingGeneratorSubspace_iff_exists_generatedByMeeting
        R meetingVector).1 hMeeting
    have hSGlobal := H.generatedByMeeting_mem_generatedGroup R S hSMeeting
    have hCleanVector :
        (binaryMul P S).vector = outsideVector := by
      change P.vector + S.vector = outsideVector
      rw [hSVector, ← hsum]
      have haddSelf (vector : SymplecticVector (ZMod 2) ι) :
          vector + vector = 0 := by
        calc
          vector + vector = (2 : ZMod 2) • vector := by
            rw [two_smul]
          _ = 0 := by
            have htwo : (2 : ZMod 2) = 0 := by decide
            rw [htwo, zero_smul]
      calc
        meetingVector + outsideVector + meetingVector =
            (meetingVector + meetingVector) + outsideVector := by abel
        _ = 0 + outsideVector := by rw [haddSelf]
        _ = outsideVector := zero_add _
    have hCleanNormalizer :
        H.code.1.InBinaryNormalizer (binaryMul P S) := by
      apply (H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer _).1
      change P.vector + S.vector ∈
        FiniteSymplectic.form.orthogonal
          H.code.1.generatedVectorSubspace
      exact Submodule.add_mem _
        (by simpa [N, L] using hPVector)
        (H.code.1.generatedVectorSubspace_isotropic
          ((H.code.1.vector_mem_generatedVectorSubspace_iff S).2
            ⟨S, hSGlobal, rfl⟩))
    refine ⟨S, hSMeeting, hSGlobal, hCleanNormalizer, ?_⟩
    apply Locality.support_subset_of_vector_mem_coordinateSubspace Rᶜ
      (binaryMul P S)
    rw [hCleanVector]
    simpa [W, Locality.orthogonal_coordinateSubspace] using hOutside

end LocalStabilizerHamiltonian
end StabilizerCode
end Coding
end QEC

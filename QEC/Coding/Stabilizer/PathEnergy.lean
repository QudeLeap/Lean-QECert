import QEC.Coding.Stabilizer.Energy
import QEC.Locality.CorrectableRegions.CorrectableRegionClosure
/-!
# Pauli-path energy algebra

This module supplies the reusable algebra behind stabilizer-code energy
barriers. Path operations are computed from the actual increment list, and
energy bounds are derived from the selected stabilizer syndrome and physical
support.

No geometric strip, membrane, or loop-length conclusion is assumed here.
-/

noncomputable section

namespace QEC
namespace Coding

open PauliSymplectic
open scoped Classical

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

namespace PauliSymplectic

omit [DecidableEq ι] in
/-- Dagger reverses binary Pauli multiplication. -/
theorem binaryDagger_binaryMul (P Q : Binary ι) :
    binaryDagger (binaryMul P Q) =
      binaryMul (binaryDagger Q) (binaryDagger P) := by
  rcases P with ⟨p, ⟨px, pz⟩⟩
  rcases Q with ⟨q, ⟨qx, qz⟩⟩
  simp [binaryDagger, binaryDaggerPhase, binaryMul, binaryMulPhase]
  constructor
  · simp_rw [mul_add, add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have htwo : (2 : ZMod 2) = 0 := by decide
    ring_nf
    simp [htwo, Finset.sum_add_distrib, mul_comm, add_comm, add_left_comm,
      add_assoc]
  · exact ⟨add_comm _ _, add_comm _ _⟩

end PauliSymplectic

namespace PauliErrorPath

/-- Reverse a path by reversing its increments and daggering every step. -/
def reverse (γ : PauliErrorPath (ι := ι)) : PauliErrorPath (ι := ι) where
  increments := γ.increments.reverse.map binaryDagger
  step_weight_le_one := by
    intro step hstep
    rw [List.mem_map] at hstep
    obtain ⟨original, horiginal, rfl⟩ := hstep
    rw [weight_binaryDagger]
    exact γ.step_weight_le_one original (List.mem_reverse.mp horiginal)

omit [DecidableEq ι] in
/-- Accumulating reverse daggered increments gives the daggered product. -/
theorem accumulate_reverse_map_binaryDagger (steps : List (Binary ι)) :
    accumulate (steps.reverse.map binaryDagger) =
      binaryDagger (accumulate steps) := by
  induction steps with
  | nil => simp [accumulate]
  | cons step rest ih =>
      rw [List.reverse_cons, List.map_append, accumulate_append]
      simp only [List.map_singleton, accumulate_singleton, ih]
      rw [show accumulate (step :: rest) =
          binaryMul step (accumulate rest) by
        simp only [accumulate, List.foldl_cons, binaryMul_binaryOne_left]
        exact foldl_binaryMul_eq_binaryMul_accumulate rest step]
      exact (binaryDagger_binaryMul step (accumulate rest)).symm

@[simp]
theorem reverse_increments (γ : PauliErrorPath (ι := ι)) :
    γ.reverse.increments = γ.increments.reverse.map binaryDagger :=
  rfl

/-- Reversal reaches the dagger of the original endpoint. -/
@[simp]
theorem endpoint_reverse (γ : PauliErrorPath (ι := ι)) :
    γ.reverse.endpoint = binaryDagger γ.endpoint :=
  accumulate_reverse_map_binaryDagger γ.increments

/-- A prefix state is unchanged when it is viewed inside a longer prefix. -/
theorem stateAt_take (γ : PauliErrorPath (ι := ι)) (n m : Nat)
    (hm : m ≤ n) :
    (γ.take n).stateAt m = γ.stateAt m := by
  simp [stateAt, List.take_take, Nat.min_eq_left hm]

/-- Before the join, concatenation has exactly the states of the left path. -/
theorem stateAt_append_left (γ δ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n ≤ γ.increments.length) :
    (γ.append δ).stateAt n = γ.stateAt n := by
  simp [stateAt, append, List.take_append, hn]

/--
After the join, concatenation left-transports the states of the right path by
the endpoint of the left path.
-/
theorem stateAt_append_right (γ δ : PauliErrorPath (ι := ι)) (n : Nat)
    :
    (γ.append δ).stateAt (γ.increments.length + n) =
      binaryMul γ.endpoint (δ.stateAt n) := by
  rw [stateAt]
  change accumulate
      ((γ.increments ++ δ.increments).take (γ.increments.length + n)) = _
  rw [show
      (γ.increments ++ δ.increments).take (γ.increments.length + n) =
        γ.increments ++ δ.increments.take n by
    simp [List.take_append]]
  exact accumulate_append γ.increments (δ.increments.take n)

end PauliErrorPath

namespace StabilizerCode.LocalStabilizerHamiltonian

/-- The BT09 height of a path: maximum excess energy of an accumulated state. -/
def pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) : Nat :=
  (Finset.range (γ.increments.length + 1)).sup fun n =>
    H.btExcessEnergy (γ.stateAt n)

/-- The set of heights attained by paths with nontrivial logical endpoints. -/
def logicalPathHeights
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) : Set Nat :=
  {height | ∃ γ : PauliErrorPath (ι := ι),
    H.HasLogicalEndpoint γ ∧ H.pathHeight γ = height}

/--
The BT09 logical energy barrier, as the infimum of all logical-path heights.

No existence of a nontrivial logical path is built into this definition.
-/
def logicalEnergyBarrier
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) : Nat :=
  sInf H.logicalPathHeights

/-- Every state indexed along the path has energy at most the path height. -/
theorem btExcessEnergy_stateAt_le_pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n ≤ γ.increments.length) :
    H.btExcessEnergy (γ.stateAt n) ≤ H.pathHeight γ := by
  rw [pathHeight]
  exact Finset.le_sup (α := Nat)
    (f := fun m => H.btExcessEnergy (γ.stateAt m))
    (Finset.mem_range.mpr (show n < γ.increments.length + 1 by omega))

/-- The endpoint energy is bounded by the path height. -/
theorem btExcessEnergy_endpoint_le_pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) :
    H.btExcessEnergy γ.endpoint ≤ H.pathHeight γ := by
  simpa using
    H.btExcessEnergy_stateAt_le_pathHeight γ γ.increments.length le_rfl

/-- The empty path has zero height. -/
@[simp]
theorem pathHeight_empty
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.pathHeight (PauliErrorPath.empty (ι := ι)) = 0 := by
  simp [pathHeight, PauliErrorPath.empty, PauliErrorPath.stateAt,
    PauliErrorPath.accumulate]

/-- Taking a prefix cannot increase the maximum path energy. -/
theorem pathHeight_take_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat) :
    H.pathHeight (γ.take n) ≤ H.pathHeight γ := by
  apply Finset.sup_le
  intro m hm
  have hmle : m ≤ (γ.take n).increments.length := by
    simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
  have hmn : m ≤ n := by
    simpa using le_trans hmle (List.length_take_le n γ.increments)
  rw [PauliErrorPath.stateAt_take γ n m hmn]
  apply H.btExcessEnergy_stateAt_le_pathHeight
  exact le_trans hmle (by simp)

/-- Concatenating more increments cannot lower the maximum on the left path. -/
theorem pathHeight_le_append
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ δ : PauliErrorPath (ι := ι)) :
    H.pathHeight γ ≤ H.pathHeight (γ.append δ) := by
  apply Finset.sup_le
  intro n hn
  have hnle : n ≤ γ.increments.length := by
    simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  calc
    H.btExcessEnergy (γ.stateAt n) =
        H.btExcessEnergy ((γ.append δ).stateAt n) := by
      rw [PauliErrorPath.stateAt_append_left γ δ n hnle]
    _ ≤ H.pathHeight (γ.append δ) :=
      H.btExcessEnergy_stateAt_le_pathHeight (γ.append δ) n
        (by simp; omega)

/-- Any concrete logical path gives an upper bound on the logical barrier. -/
theorem logicalEnergyBarrier_le_pathHeight
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (hγ : H.HasLogicalEndpoint γ) :
    H.logicalEnergyBarrier ≤ H.pathHeight γ := by
  exact csInf_le' ⟨γ, hγ, rfl⟩

/-- A uniform lower bound on all logical paths bounds the logical barrier. -/
theorem le_logicalEnergyBarrier
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (bound : Nat)
    (hexists : ∃ γ : PauliErrorPath (ι := ι), H.HasLogicalEndpoint γ)
    (hlower : ∀ γ : PauliErrorPath (ι := ι),
      H.HasLogicalEndpoint γ → bound ≤ H.pathHeight γ) :
    bound ≤ H.logicalEnergyBarrier := by
  apply le_csInf
  · obtain ⟨γ, hγ⟩ := hexists
    exact ⟨H.pathHeight γ, γ, hγ, rfl⟩
  · rintro height ⟨γ, hγ, rfl⟩
    exact hlower γ hγ

/-- A selected syndrome can only be supported where one factor has syndrome. -/
theorem violatedGenerators_binaryMul_subset
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) :
    H.violatedGenerators (binaryMul E F) ⊆
      H.violatedGenerators E ∪ H.violatedGenerators F := by
  intro j hj
  simp only [mem_violatedGenerators, Finset.mem_union] at hj ⊢
  by_contra h
  push Not at h
  exact hj (commutes_binaryMul_right
    ((commutes_comm _ _).2 h.1) ((commutes_comm _ _).2 h.2) |>
      (commutes_comm _ _).1)

/-- Selected unit-defect energy is subadditive under Pauli multiplication. -/
theorem unitDefectEnergy_binaryMul_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) :
    H.unitDefectEnergy (binaryMul E F) ≤
      H.unitDefectEnergy E + H.unitDefectEnergy F := by
  calc
    _ ≤ (H.violatedGenerators E ∪ H.violatedGenerators F).card :=
      Finset.card_le_card (H.violatedGenerators_binaryMul_subset E F)
    _ ≤ (H.violatedGenerators E).card +
        (H.violatedGenerators F).card :=
      Finset.card_union_le _ _
    _ = _ := rfl

/-- BT09 excess energy is subadditive under Pauli multiplication. -/
theorem btExcessEnergy_binaryMul_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) :
    H.btExcessEnergy (binaryMul E F) ≤
      H.btExcessEnergy E + H.btExcessEnergy F := by
  simpa [btExcessEnergy, Nat.mul_add] using
    Nat.mul_le_mul_left 2 (H.unitDefectEnergy_binaryMul_le E F)

/-- Dagger does not change the selected violated-generator set. -/
@[simp]
theorem violatedGenerators_binaryDagger
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators (binaryDagger E) = H.violatedGenerators E := by
  ext j
  simp only [mem_violatedGenerators]
  simp [Commutes, binaryDagger]

/-- Dagger does not change BT09 excess energy. -/
@[simp]
theorem btExcessEnergy_binaryDagger
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.btExcessEnergy (binaryDagger E) = H.btExcessEnergy E := by
  simp [btExcessEnergy, unitDefectEnergy]

/-- Every generated stabilizer has zero selected-generator excess energy. -/
theorem btExcessEnergy_eq_zero_of_mem_generatedGroup
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    H.btExcessEnergy S = 0 := by
  have hnone : H.violatedGenerators S = ∅ := by
    ext j
    simp only [mem_violatedGenerators, Finset.notMem_empty, iff_false]
    push Not
    exact H.code.1.generatedGroup_pairwise_commutes
      hS (H.generator_mem_generatedGroup j)
  simp [btExcessEnergy, unitDefectEnergy, hnone]

/-- Selected energy is invariant under multiplication by a generated stabilizer. -/
theorem btExcessEnergy_binaryMul_generated
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    H.btExcessEnergy (binaryMul E S) = H.btExcessEnergy E := by
  apply le_antisymm
  · simpa [H.btExcessEnergy_eq_zero_of_mem_generatedGroup S hS] using
      H.btExcessEnergy_binaryMul_le E S
  · have hmul :
        binaryMul (binaryMul E S) (binaryDagger S) = E := by
      simp [binaryMul_assoc]
    calc
      H.btExcessEnergy E =
          H.btExcessEnergy
            (binaryMul (binaryMul E S) (binaryDagger S)) := by rw [hmul]
      _ ≤ H.btExcessEnergy (binaryMul E S) +
          H.btExcessEnergy (binaryDagger S) :=
        H.btExcessEnergy_binaryMul_le _ _
      _ = H.btExcessEnergy (binaryMul E S) := by
        simp [H.btExcessEnergy_eq_zero_of_mem_generatedGroup S hS]

/--
A Pauli supported on at most one qubit violates at most the recorded number of
selected terms incident on one qubit.
-/
theorem unitDefectEnergy_le_participationBound_of_weight_le_one
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (step : Binary ι) (hstep : weight step ≤ 1) :
    H.unitDefectEnergy step ≤ H.participationBound := by
  by_cases hs : support step = ∅
  · have hnone : H.violatedGenerators step = ∅ := by
      ext j
      simp only [mem_violatedGenerators, Finset.notMem_empty, iff_false]
      push Not
      apply QEC.Locality.commutes_of_disjoint_support
      simp [hs]
    simp [unitDefectEnergy, hnone]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hcard : (support step).card ≤ 1 := hstep
    have hsubset :
        H.violatedGenerators step ⊆ H.incidentGenerators i := by
      intro j hj
      rw [mem_violatedGenerators] at hj
      change j ∈ Finset.univ.filter
        (fun j => i ∈ H.generatorSupport j)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      by_contra hnot
      apply hj
      apply QEC.Locality.commutes_of_disjoint_support
      apply Finset.disjoint_left.mpr
      intro q hqstep hqgen
      have hqi : q = i :=
        (Finset.card_le_one.mp hcard q hqstep i hi)
      exact hnot (by simpa [generatorSupport, hqi] using hqgen)
    exact le_trans (Finset.card_le_card hsubset) (H.incidentGenerators_card_le i)

/-- A one-qubit step has BT09 excess energy at most twice the participation bound. -/
theorem btExcessEnergy_le_two_mul_participationBound_of_weight_le_one
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (step : Binary ι) (hstep : weight step ≤ 1) :
    H.btExcessEnergy step ≤ 2 * H.participationBound := by
  exact Nat.mul_le_mul_left 2
    (H.unitDefectEnergy_le_participationBound_of_weight_le_one step hstep)

/-- One allowed local Pauli increment changes energy by a uniformly bounded amount. -/
theorem btExcessEnergy_dist_binaryMul_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E step : Binary ι) (hstep : weight step ≤ 1) :
    Nat.dist (H.btExcessEnergy (binaryMul E step)) (H.btExcessEnergy E) ≤
      2 * H.participationBound := by
  have hforward :
      H.btExcessEnergy (binaryMul E step) ≤
        H.btExcessEnergy E + 2 * H.participationBound :=
    le_trans (H.btExcessEnergy_binaryMul_le E step)
      (Nat.add_le_add_left
        (H.btExcessEnergy_le_two_mul_participationBound_of_weight_le_one step hstep) _)
  have hback :
      H.btExcessEnergy E ≤
        H.btExcessEnergy (binaryMul E step) + 2 * H.participationBound := by
    have hmul :
        binaryMul (binaryMul E step) (binaryDagger step) = E := by
      simp [binaryMul_assoc]
    calc
      H.btExcessEnergy E =
          H.btExcessEnergy
            (binaryMul (binaryMul E step) (binaryDagger step)) := by
        rw [hmul]
      _ ≤ H.btExcessEnergy (binaryMul E step) +
          H.btExcessEnergy (binaryDagger step) :=
        H.btExcessEnergy_binaryMul_le _ _
      _ ≤ H.btExcessEnergy (binaryMul E step) +
          2 * H.participationBound :=
        Nat.add_le_add_left
          (H.btExcessEnergy_le_two_mul_participationBound_of_weight_le_one
            (binaryDagger step) (by simpa using hstep)) _
  unfold Nat.dist
  omega

/-- Every adjacent pair of stored path states obeys the local energy-change bound. -/
theorem path_step_energy_dist_le
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (γ : PauliErrorPath (ι := ι)) (n : Nat)
    (hn : n < γ.increments.length) :
    Nat.dist (H.btExcessEnergy (γ.stateAt (n + 1)))
        (H.btExcessEnergy (γ.stateAt n)) ≤
      2 * H.participationBound := by
  rw [γ.stateAt_succ n hn]
  exact H.btExcessEnergy_dist_binaryMul_le _ _
    (γ.getElem_weight_le_one n hn)

/--
Multiplying by a generated stabilizer preserves both the logical normalizer
sector and the nontrivial generated-group coset.
-/
theorem logicalCoset_binaryMul_generated_iff
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    (H.code.1.InBinaryNormalizer (binaryMul E S) ∧
        ¬ H.code.1.InGeneratedGroupUpToSign (binaryMul E S)) ↔
      (H.code.1.InBinaryNormalizer E ∧
        ¬ H.code.1.InGeneratedGroupUpToSign E) := by
  let V := H.code.1.generatedVectorSubspace
  have hSV : S.vector ∈ V :=
    (H.code.1.vector_mem_generatedVectorSubspace_iff S).2
      ⟨S, hS, rfl⟩
  have hSOrth :
      S.vector ∈ FiniteSymplectic.form.orthogonal V :=
    H.code.1.generatedVectorSubspace_isotropic hSV
  rw [← H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer,
    ← H.code.1.vector_mem_generatedVectorSubspace_iff,
    ← H.code.1.vector_mem_orthogonal_iff_inBinaryNormalizer,
    ← H.code.1.vector_mem_generatedVectorSubspace_iff]
  change
    (E.vector + S.vector ∈ FiniteSymplectic.form.orthogonal V ∧
        E.vector + S.vector ∉ V) ↔
      (E.vector ∈ FiniteSymplectic.form.orthogonal V ∧ E.vector ∉ V)
  rw [(FiniteSymplectic.form.orthogonal V).add_mem_iff_left hSOrth,
    V.add_mem_iff_left hSV]

end StabilizerCode.LocalStabilizerHamiltonian
end Coding
end QEC

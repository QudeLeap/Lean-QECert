import QEC.Locality.OptimalTradeoff.FinalComposition
/-!
# Dai--Li optimal locality tradeoff

This public terminal realizes the finite binary-stabilizer specialization of
[DL24, Theorem 1.2].  It quantifies over actual semantic parameter data, a
fixed independent Pauli-generator presentation, and a unit-separated
Euclidean embedding.  The counted objects are the distinct unordered
fixed-generator interactions of that presentation.

The explicit witnesses are Lean-QEC proof witnesses.  In particular, the
stronger above-BPT witness incorporates the project-owned repair of the
source's square-3 defect; neither that repair nor its derived constants are
attributed to DL24.
-/

noncomputable section

namespace QEC.Locality

open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
open Coding.StabilizerCode.StabilizerParameterData

universe u v

private theorem daiLi_distance_le_blockLength
    {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.distance ≤ D.blockLength := by
  rcases D.semanticDistance with ⟨E, _hNotDetectable, hWeight, _hLeast⟩
  rw [← hWeight]
  change (support E).card ≤ Fintype.card ι
  exact Finset.card_le_card (Finset.subset_univ _)

private theorem daiLi_encodedQubits_le_blockLength
    {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.encodedQubits ≤ D.blockLength := by
  rw [D.encodedQubits_eq_blockLength_sub_generatorRank]
  exact Nat.sub_le _ _

private theorem daiLi_degenerate_public_conclusion
    {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
    (D : StabilizerParameterData (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι)
    (hAboveBPT : daiLiFinalAboveBPTConstant * (D.blockLength : ℝ) ≤
      (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2)
    (hDistanceLeBlockLength : D.distance ≤ D.blockLength)
    (hEncodedLeBlockLength : D.encodedQubits ≤ D.blockLength)
    (hDegenerate : ¬ 0 < D.distance ∨ ¬ 0 < D.encodedQubits) :
    (1 / 200 : ℝ) * max (D.encodedQubits : ℝ) (D.distance : ℝ) ≤
      (D.presentation.longInteractionCount embedding
        ((1 / 200 : ℝ) * max ((D.distance : ℝ) / Real.sqrt (D.blockLength : ℝ))
          (daiLiFourthRoot
            ((D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 /
              (D.blockLength : ℝ)))) : ℝ) := by
  have hProductZero :
      (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 = 0 := by
    rcases hDegenerate with hDistance | hEncoded
    · have hDistanceZero : D.distance = 0 := Nat.eq_zero_of_not_pos hDistance
      simp [hDistanceZero]
    · have hEncodedZero : D.encodedQubits = 0 := Nat.eq_zero_of_not_pos hEncoded
      simp [hEncodedZero]
  have hConstantPositive : 0 < daiLiFinalAboveBPTConstant := by
    dsimp [daiLiFinalAboveBPTConstant]
    positivity
  have hBlockLengthNonneg : 0 ≤ (D.blockLength : ℝ) := Nat.cast_nonneg _
  have hBlockLengthRealZero : (D.blockLength : ℝ) = 0 := by
    nlinarith [mul_nonneg hConstantPositive.le hBlockLengthNonneg]
  have hBlockLengthZero : D.blockLength = 0 := by
    exact_mod_cast hBlockLengthRealZero
  have hDistanceZero : D.distance = 0 :=
    Nat.eq_zero_of_le_zero (hDistanceLeBlockLength.trans_eq hBlockLengthZero)
  have hEncodedZero : D.encodedQubits = 0 :=
    Nat.eq_zero_of_le_zero (hEncodedLeBlockLength.trans_eq hBlockLengthZero)
  simp [hDistanceZero, hEncodedZero]

/--
Dai--Li's optimal locality tradeoff [DL24, Theorem 1.2] for a finite binary
stabilizer code with one fixed independent Pauli-generator presentation.

The outer existential witnesses are absolute across every presentation and
unit-separated embedding.  The conclusion counts the cardinality of the
actual finite set of distinct unordered generator interactions; it makes no
comparison between different generator presentations.  The selected witnesses
are Lean-QEC proof constants, not constants attributed to DL24.
-/
theorem exists_daiLi_optimal_locality_tradeoff :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type v} [Fintype κ]
        (D : StabilizerParameterData (ι := ι) (κ := κ))
        (embedding : UnitSeparatedEmbedding2D ι),
        c1 * (D.blockLength : ℝ) ≤
            (D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 →
          c0 * max (D.encodedQubits : ℝ) (D.distance : ℝ) ≤
            (D.presentation.longInteractionCount embedding
              (c0 * max ((D.distance : ℝ) / Real.sqrt (D.blockLength : ℝ))
                (daiLiFourthRoot
                  ((D.encodedQubits : ℝ) * (D.distance : ℝ) ^ 2 /
                    (D.blockLength : ℝ)))) : ℝ) := by
  refine ⟨1 / 200, daiLiFinalAboveBPTConstant, by norm_num, by
    dsimp [daiLiFinalAboveBPTConstant]
    positivity, ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK D embedding hAboveBPT
  have hDistanceLeBlockLength : D.distance ≤ D.blockLength :=
    daiLi_distance_le_blockLength D
  have hEncodedLeBlockLength : D.encodedQubits ≤ D.blockLength :=
    daiLi_encodedQubits_le_blockLength D
  by_cases hDistancePositive : 0 < D.distance
  · by_cases hEncodedPositive : 0 < D.encodedQubits
    · have hInternal := daiLi_final_interaction_count_max_length D.presentation embedding D.distance
        D.semanticDistance hDistancePositive hEncodedPositive (by
          exact hAboveBPT)
      simpa [daiLiFirstLengthScale, daiLiInteractionCountThreshold,
        StabilizerParameterData.blockLength, StabilizerParameterData.encodedQubits,
        BinaryStabilizerPresentation.blockLength,
        div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hInternal
    · exact daiLi_degenerate_public_conclusion D embedding hAboveBPT hDistanceLeBlockLength
        hEncodedLeBlockLength (Or.inr hEncodedPositive)
  · exact daiLi_degenerate_public_conclusion D embedding hAboveBPT hDistanceLeBlockLength
      hEncodedLeBlockLength (Or.inl hDistancePositive)

end QEC.Locality

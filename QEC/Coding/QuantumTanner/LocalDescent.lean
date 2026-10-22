import QEC.Coding.QuantumTanner.NeighborViews

/-!
# Local weight descent from finite mixing budgets

This assembles the finite geometric part of [LZ22, proof of Theorem thm:main].
Both mixing assumptions concern the actual graphs of the square complex.
The explicit numeric inequalities remain to be obtained from the source's
large-degree regime; no Ramanujan or selected-family claim is assumed proved.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open Classical QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- A nonzero global word has a nonzero local view on each side. -/
theorem activeVerticesOnSide_nonempty_of_ne_zero
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (hx : x ≠ 0) :
    (X.activeVerticesOnSide side x).Nonempty := by
  by_contra hEmpty
  have hLocal (g : G) : X.localRestriction (g, side) x = 0 := by
    by_contra hNonzero
    exact hEmpty ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNonzero⟩⟩
  have hSum := X.sum_hammingWeight_localRestriction side x
  simp only [hLocal, HammingWeight_zero, Finset.sum_const_zero] at hSum
  exact hx ((HammingWeight_eq_zero_iff x).mp (by omega))

/-- Actual finite mixing, local-code robustness and explicit scalar budgets
construct a local tensor check decreasing any given nonzero word whose local
views lie in the corresponding dual-tensor code. -/
theorem exists_local_weight_reduction_of_finite_mixing
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB w p normalCutoff heavyCutoff : Nat)
    (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hCard : Fintype.card A = Fintype.card B)
    (hDegree : 0 < Fintype.card A + Fintype.card B)
    (hp : p ≤ Fintype.card A) (hpA : p < dA) (hpB : p < dB)
    (hRobust : IsRobust CA CB w)
    (hPunctures : IsRobustWithPunctureResistance CA CB w p)
    (hPunctureBudget : 2 * w ≤ (dA - p) * (dB - p))
    (hNormalCutoff : 0 < normalCutoff) (hWeightBudget : normalCutoff - 1 ≤ w)
    (hRows : (normalCutoff - 1) / dB < dA)
    (hColumns : (normalCutoff - 1) / dA < dB)
    (hHeavyRows : heavyCutoff + (normalCutoff - 1) / dA ≤ dB)
    (hHeavyColumns : heavyCutoff + (normalCutoff - 1) / dB ≤ dA)
    (hErrorBudget : Fintype.card B * ((normalCutoff - 1) / dB) +
      Fintype.card A * ((normalCutoff - 1) / dA) ≤ w)
    (side : Bool) (x : Word (ZMod 2) Square) (hx : x ≠ 0)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (squareSpectral unionSpectral normalThreshold gap fraction ratio uniformBudget threshold : ℝ)
    (hSquareSpectral : 0 ≤ squareSpectral) (hUnionSpectral : 0 ≤ unionSpectral)
    (hNormalThreshold : 0 < normalThreshold) (hNormalRound : normalThreshold ≤ normalCutoff)
    (hGap : 0 < gap) (hFraction : 0 ≤ fraction) (hFractionHalf : fraction ≤ 1 / 2)
    (hThreshold : 0 < threshold)
    (hSquareMixing : HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) squareSpectral)
    (hUnionMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) unionSpectral)
    (hSquareSmall : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤ normalThreshold * Fintype.card G)
    (hFractionBudget : 4 * squareSpectral ^ 2 ≤ fraction * normalThreshold ^ 2)
    (hUnionDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card + gap * Fintype.card G ≤
      (heavyCutoff : ℝ) * Fintype.card G)
    (hRatioBudget : unionSpectral ^ 2 ≤ ratio * gap ^ 2)
    (hAverageBudget : 2 * threshold * ratio ≤ 1 - fraction)
    (hMeanBudget : (Fintype.card A + Fintype.card B : Nat) *
      (fraction * (X.activeVerticesOnSide side x).card) ≤ uniformBudget * Fintype.card G)
    (hSelectionBudget : (uniformBudget + unionSpectral * Real.sqrt
      (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) *
      (Fintype.card A + Fintype.card B : Nat) ≤ (p : ℝ) * threshold)
    (hMargin : (3 * (Fintype.card B * ((normalCutoff - 1) / dB) +
      Fintype.card A * ((normalCutoff - 1) / dA)) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
      (heavyCutoff : ℝ) * threshold) :
    ∃ g : G, ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
      HammingWeight (X.localRestriction (g, !side) x + c) <
        HammingWeight (X.localRestriction (g, !side) x) := by
  let S := X.activeVerticesOnSide side x
  let E := X.exceptionalVerticesOnSide side x normalCutoff
  let N := S \ E
  let T := X.oppositeHeavySet side x heavyCutoff N
  have hES : E ⊆ S := Finset.filter_subset _ _
  have hPartition : N.card + E.card = S.card := by
    simpa only [N, Finset.inter_eq_right.mpr hES] using Finset.card_sdiff_add_card_inter S E
  have hCover := X.exists_normal_cover_of_robust CA CB dA dB w normalCutoff
    hA hB hRobust hNormalCutoff hWeightBudget hRows hColumns side x hLocal
  have hCoverage : N.card ≤ crossCount (X.heavyUnionGraph side x heavyCutoff) N T := by
    apply X.normal_card_le_heavy_crossCount_of_covers side x heavyCutoff N CA CB dA dB
      hA.choose_spec.2.2.2 hB.choose_spec.2.2.2 Finset.sdiff_subset
    intro g hg
    obtain ⟨rows, columns, hMem, hCovered, hRowSmall, hColumnSmall, hRowSize, hColumnSize⟩ :=
      hCover g (Finset.mem_sdiff.mp hg).2
    exact ⟨rows, columns, hMem, hCovered, hRowSmall, hColumnSmall,
      by omega, by omega⟩
  have hExceptional : (E.card : ℝ) ≤ fraction * S.card := by
    have hBound := X.exceptionalVertices_card_bound_of_mixing side x normalCutoff
      normalThreshold squareSpectral hNormalThreshold hNormalRound hSquareSpectral
      hSquareMixing hSquareSmall
    have hScaled := mul_le_mul_of_nonneg_right hFractionBudget (Nat.cast_nonneg S.card)
    apply le_of_mul_le_mul_left (a := normalThreshold ^ 2) ?_ (sq_pos_of_pos hNormalThreshold)
    dsimp [S, E] at *
    nlinarith
  have hHalf : 2 * E.card ≤ S.card := by
    have hScaled := mul_le_mul_of_nonneg_right hFractionHalf (Nat.cast_nonneg S.card)
    exact_mod_cast (by nlinarith : (2 : ℝ) * E.card ≤ S.card)
  have hN : N.Nonempty := by
    have hS : 0 < S.card := Finset.card_pos.mpr (X.activeVerticesOnSide_nonempty_of_ne_zero side x hx)
    apply Finset.card_pos.mp
    omega
  have hTBound : (T.card : ℝ) ≤ ratio * S.card := by
    have hBound := X.oppositeHeavySet_card_bound_of_density_gap hX side x heavyCutoff N
      unionSpectral gap hUnionSpectral hGap hUnionMixing hUnionDensity
    have hScaled := mul_le_mul_of_nonneg_right hRatioBudget (Nat.cast_nonneg S.card)
    apply le_of_mul_le_mul_left (a := gap ^ 2) ?_ (sq_pos_of_pos hGap)
    dsimp [T, S] at *
    nlinarith
  have hAverage : 2 * threshold * T.card ≤ (N.card : ℝ) := by
    have hTScaled := mul_le_mul_of_nonneg_left hTBound (by positivity : 0 ≤ 2 * threshold)
    have hAverageScaled := mul_le_mul_of_nonneg_right hAverageBudget (Nat.cast_nonneg S.card)
    have hPartition' : (N.card : ℝ) + E.card = S.card := by exact_mod_cast hPartition
    nlinarith
  have hBadAverage : (crossCount X.unionCayleyGraph E T : ℝ) ≤
      (uniformBudget + unionSpectral * Real.sqrt
        (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) * T.card := by
    apply X.exceptional_crossCount_le_of_heavy_coverage side x heavyCutoff S E
      unionSpectral fraction uniformBudget hUnionSpectral hFraction hUnionMixing
    · simpa only [Finset.inter_eq_right.mpr hES] using hHalf
    · exact hExceptional
    · exact (mul_le_mul_of_nonneg_left hExceptional
        (Nat.cast_nonneg (Fintype.card A + Fintype.card B))).trans hMeanBudget
    · exact hCoverage
  obtain ⟨g, hg, hHeavy, hBad⟩ := X.exists_high_heavy_low_exceptional_vertex side x
    heavyCutoff N E hN hDegree threshold
    (uniformBudget + unionSpectral * Real.sqrt
      (fraction * (2 * (Fintype.card A + Fintype.card B : Nat)))) p
    hThreshold (Nat.cast_nonneg p) hCoverage hAverage hBadAverage hSelectionBudget
  refine ⟨g, ?_⟩
  apply X.exists_local_reduction_of_selected_heavy_vertex hX CA CB dA dB w p hA hB
    hCard hp hpA hpB hPunctures hPunctureBudget side x heavyCutoff N E g threshold hHeavy
    (by exact_mod_cast hBad) ((normalCutoff - 1) / dA) ((normalCutoff - 1) / dB)
    hCover hErrorBudget hMargin

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

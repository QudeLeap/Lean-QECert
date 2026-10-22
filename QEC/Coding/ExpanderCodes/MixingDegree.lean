import QEC.Coding.ExpanderCodes.SmallSetExpansionSquare

/-!
# High-degree sets under expander mixing

The density contribution can be absorbed when one endpoint set is small.
The remaining square-root term bounds the size of a high-degree set. This
finite counting argument applies to weighted graphs with multiplicities.
-/

namespace QEC.Coding.SmallSetExpansion

universe u

variable {V : Type u} [Fintype V] [Nonempty V]

/-- If the uniform-density term is at most half of the degree threshold,
mixing bounds the high-degree set by the squared spectral/degree ratio. -/
theorem highDegree_card_bound_of_mixing
    (M : WeightedGraph V) (degree : Nat) (spectral threshold : ℝ)
    (hSpectral : 0 ≤ spectral) (hThreshold : 0 < threshold)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (S T : Finset V)
    (hDegree : threshold * S.card ≤ (crossCount M S T : ℝ))
    (hDensity : 2 * (degree : ℝ) * T.card ≤ threshold * Fintype.card V) :
    threshold ^ 2 * S.card ≤ 4 * spectral ^ 2 * T.card := by
  by_cases hS : S.card = 0
  · simp [hS]
    positivity
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hn : (0 : ℝ) < Fintype.card V := by positivity
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hroot : 0 ≤ Real.sqrt ((S.card : ℝ) * T.card) := Real.sqrt_nonneg _
  have hDensityScaled := mul_le_mul_of_nonneg_right hDensity hs.le
  have hDegreeScaled := mul_le_mul_of_nonneg_left hDegree hn.le
  have hMix := hMixing S T
  have hScaledN : (Fintype.card V : ℝ) * (threshold / 2 * S.card) ≤
      (Fintype.card V : ℝ) * (spectral * Real.sqrt ((S.card : ℝ) * T.card)) := by
    nlinarith
  have hScaled : threshold / 2 * S.card ≤
      spectral * Real.sqrt ((S.card : ℝ) * T.card) :=
    le_of_mul_le_mul_left hScaledN hn
  have hSquare : (threshold / 2 * S.card) ^ 2 ≤
      (spectral * Real.sqrt ((S.card : ℝ) * T.card)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hScaled
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg hs.le ht)] at hSquare
  have hCancel : (S.card : ℝ) * (threshold ^ 2 * S.card) ≤
      (S.card : ℝ) * (4 * spectral ^ 2 * T.card) := by
    nlinarith
  exact le_of_mul_le_mul_left hCancel hs

/-- A specified positive gap after the uniform-density contribution gives
the sharp squared gap bound, without the factor-four half-gap relaxation. -/
theorem highDegree_card_bound_of_density_gap
    (M : WeightedGraph V) (degree : Nat) (spectral threshold gap : ℝ)
    (hSpectral : 0 ≤ spectral) (hGap : 0 < gap)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (S T : Finset V)
    (hDegree : threshold * S.card ≤ (crossCount M S T : ℝ))
    (hDensity : (degree : ℝ) * T.card + gap * Fintype.card V ≤
      threshold * Fintype.card V) :
    gap ^ 2 * S.card ≤ spectral ^ 2 * T.card := by
  by_cases hS : S.card = 0
  · simp [hS]
    positivity
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hn : (0 : ℝ) < Fintype.card V := by positivity
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hDensityScaled := mul_le_mul_of_nonneg_right hDensity hs.le
  have hDegreeScaled := mul_le_mul_of_nonneg_left hDegree hn.le
  have hMix := hMixing S T
  have hScaledN : (Fintype.card V : ℝ) * (gap * S.card) ≤
      (Fintype.card V : ℝ) * (spectral * Real.sqrt ((S.card : ℝ) * T.card)) := by
    nlinarith
  have hScaled : gap * S.card ≤ spectral * Real.sqrt ((S.card : ℝ) * T.card) :=
    le_of_mul_le_mul_left hScaledN hn
  have hSquare : (gap * S.card) ^ 2 ≤
      (spectral * Real.sqrt ((S.card : ℝ) * T.card)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hScaled
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg hs.le ht)] at hSquare
  have hCancel : (S.card : ℝ) * (gap ^ 2 * S.card) ≤
      (S.card : ℝ) * (spectral ^ 2 * T.card) := by nlinarith
  exact le_of_mul_le_mul_left hCancel hs

/-- If the bad set is a small fraction of a set whose size is linear in
`T`, mixing gives a linear-in-`T` bound on actual bad incidences. -/
theorem crossCount_le_linear_of_card_ratio
    (M : WeightedGraph V) (degree : Nat) (spectral fraction ratio uniformBudget : ℝ)
    (hSpectral : 0 ≤ spectral) (hFraction : 0 ≤ fraction) (hRatio : 0 ≤ ratio)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (bad S T : Finset V)
    (hBad : (bad.card : ℝ) ≤ fraction * S.card)
    (hRatioBound : (S.card : ℝ) ≤ ratio * T.card)
    (hMean : (degree : ℝ) * bad.card ≤ uniformBudget * Fintype.card V) :
    (crossCount M bad T : ℝ) ≤
      (uniformBudget + spectral * Real.sqrt (fraction * ratio)) * T.card := by
  have hn : (0 : ℝ) < Fintype.card V := by positivity
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hBadRatio : (bad.card : ℝ) ≤ fraction * ratio * T.card := by
    have hScaled := mul_le_mul_of_nonneg_left hRatioBound hFraction
    nlinarith
  have hRoot : Real.sqrt ((bad.card : ℝ) * T.card) ≤
      Real.sqrt (fraction * ratio) * T.card := by
    calc
      Real.sqrt ((bad.card : ℝ) * T.card) ≤
          Real.sqrt ((fraction * ratio) * (T.card : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      _ = Real.sqrt (fraction * ratio) * T.card := by
        rw [Real.sqrt_mul (mul_nonneg hFraction hRatio), Real.sqrt_sq ht]
  have hMix := hMixing bad T
  have hMeanScaled := mul_le_mul_of_nonneg_right hMean ht
  have hRootScaled := mul_le_mul_of_nonneg_left hRoot (mul_nonneg hSpectral hn.le)
  have hScaled : (Fintype.card V : ℝ) * crossCount M bad T ≤
      (Fintype.card V : ℝ) *
        ((uniformBudget + spectral * Real.sqrt (fraction * ratio)) * T.card) := by
    nlinarith
  exact le_of_mul_le_mul_left hScaled hn

end QEC.Coding.SmallSetExpansion

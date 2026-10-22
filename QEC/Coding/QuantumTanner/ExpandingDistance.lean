import QEC.Coding.QuantumTanner.DistanceBudgets
import QEC.Coding.QuantumTanner.CayleySquareGraph

/-!
# Weight descent at sufficiently large expanding degree

This supplies the rounded scalar hypotheses of the finite distance argument
from the exponent regime of [LZ22, Theorem thm:main]. The two mixing bounds
are properties of the actual square and union graphs, not assumed conclusions
about an unspecified selected family.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

open QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

/-- The source's global weight threshold implies its active-set bound, using
the actual incidence count and the minimum-distance bound for dual tensors. -/
theorem activeVertices_card_bound_of_small_weight
    (X : LeftRightCayleySquareComplex G A B Square)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (dA dB Delta : Nat) (delta epsilon : ℝ)
    (hDelta : 0 < Delta) (hDeltaDistance : 0 < delta)
    (hCardA : Fintype.card A = Delta) (hCardB : Fintype.card B = Delta)
    (hA : MinimumDistance CA dA) (hB : MinimumDistance CB dB)
    (hDistanceA : delta * Delta ≤ (dA : ℝ)) (hDistanceB : delta * Delta ≤ (dB : ℝ))
    (side : Bool) (x : Word (ZMod 2) Square)
    (hLocal : ∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier)
    (hWeight : (HammingWeight x : ℝ) <
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon))) :
    ((X.activeVerticesOnSide side x).card : ℝ) ≤
      Fintype.card G / (4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon)) := by
  have hD : (0 : ℝ) < Delta := by exact_mod_cast hDelta
  have hCount := X.activeVerticesOnSide_card_mul_le side x (min dA dB)
    (fun g hne => hammingWeight_ge_min_of_mem_dualTensorCode CA CB dA dB
      hA.choose_spec.2.2.2 hB.choose_spec.2.2.2 _ (hLocal g) hne)
  have hDistance : delta * Delta ≤ ((min dA dB : Nat) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min hDistanceA hDistanceB
  have hCount' : delta * Delta * (X.activeVerticesOnSide side x).card ≤
      2 * (HammingWeight x : ℝ) :=
    (mul_le_mul_of_nonneg_right hDistance (Nat.cast_nonneg _)).trans (by exact_mod_cast hCount)
  have hCard : (Fintype.card G : ℝ) * (Delta : ℝ) ^ 2 = 2 * Fintype.card Square := by
    have h := X.card_group_mul_local_degree_eq_twice_card_square
    rw [hCardA, hCardB] at h
    rw [← pow_two] at h
    exact_mod_cast h
  have hPower : (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon) =
      (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) := by
    calc
      _ = (Delta : ℝ) ^ ((1 : ℝ) + (1 / 2 + epsilon)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hD, Real.rpow_one]
  have hSmall := (lt_div_iff₀ (show 0 < 4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon) by positivity)).mp hWeight
  have hScaled := mul_le_mul_of_nonneg_right hCount'
    (show 0 ≤ 4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon) by positivity)
  rw [hPower] at hSmall hScaled
  have hCardScaled := congrArg (fun z : ℝ => delta * z) hCard
  apply (le_div_iff₀ (show 0 < 4 * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon) by positivity)).mpr
  apply le_of_mul_le_mul_left (a := delta * (Delta : ℝ) ^ 2) ?_ (by positivity)
  nlinarith only [hSmall, hScaled, hCardScaled]

/-- For all sufficiently large fixed degrees, actual graph mixing and actual
puncture-resistant component codes construct a local reducing tensor check.
There is no reducing-check hypothesis in this theorem. -/
theorem exists_eventual_local_weight_reduction_of_mixing
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square : Type v) [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square],
      ∀ (X : LeftRightCayleySquareComplex G A B Square), X.HasCayleyLinkIdentities →
      ∀ (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (dA dB : Nat),
      MinimumDistance CA dA → MinimumDistance CB dB →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust CA CB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance CA CB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
        (Nat.floor ((Delta : ℝ) ^ gamma)) →
      ∀ (side : Bool) (x : Word (ZMod 2) Square), x ≠ 0 →
      (∀ g, X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier) →
      HasExpanderMixingBound (X.squareGraph side) (Delta * Delta) (4 * (Delta : ℝ)) →
      HasExpanderMixingBound X.unionCayleyGraph (Delta + Delta) (4 * Real.sqrt (Delta : ℝ)) →
      ((X.activeVerticesOnSide side x).card : ℝ) ≤
        Fintype.card G / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon)) →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B), c ∈ (tensorCode CA CB).carrier ∧
        HammingWeight (X.localRestriction (g, !side) x + c) <
          HammingWeight (X.localRestriction (g, !side) x) := by
  obtain ⟨tI, hI⟩ := exists_eventual_distance_integer_margins delta epsilon gamma
    hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  obtain ⟨tD, hD⟩ := exists_eventual_distance_density_margin delta epsilon hDeltaDistance hEpsilon
  refine ⟨max tI tD, ?_⟩
  intro Delta hDegree G A B Square _ _ _ _ _ X hX CA CB dA dB hA hB hDistanceA hDistanceB hCardA hCardB
    hRobust hPunctures side x hx hLocal hSquareMixing hUnionMixing hSmall
  obtain ⟨hTwo, hNormalPos, hNormalWeight, hpDegree, hpD, heD, hPunctureBudget,
    hErrorBudget, hMargin, hFractionHalf, hLower⟩ :=
    hI Delta ((Nat.le_max_left _ _).trans hDegree)
  obtain ⟨_, hDensity⟩ := hD Delta ((Nat.le_max_right _ _).trans hDegree)
  let d := Nat.ceil (delta * Delta)
  let e := distanceLineError delta epsilon Delta
  let p := Nat.floor ((Delta : ℝ) ^ gamma)
  let w := Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))
  let cutoff := distanceNormalCutoff epsilon Delta
  have hDPos : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hdA : d ≤ dA := Nat.ceil_le.mpr hDistanceA
  have hdB : d ≤ dB := Nat.ceil_le.mpr hDistanceB
  have hdPos : 0 < d := Nat.ceil_pos.mpr (by positivity)
  have hDivA : (cutoff - 1) / dA ≤ e := by
    apply (Nat.le_div_iff_mul_le hdPos).mpr
    exact (Nat.mul_le_mul_left _ hdA).trans (Nat.div_mul_le_self _ _)
  have hDivB : (cutoff - 1) / dB ≤ e := by
    apply (Nat.le_div_iff_mul_le hdPos).mpr
    exact (Nat.mul_le_mul_left _ hdB).trans (Nat.div_mul_le_self _ _)
  have hActualPunctureBudget : 2 * w ≤ (dA - p) * (dB - p) :=
    hPunctureBudget.trans (Nat.mul_le_mul (Nat.sub_le_sub_right hdA p)
      (Nat.sub_le_sub_right hdB p))
  have hActualErrorBudget : Fintype.card B * ((cutoff - 1) / dB) +
      Fintype.card A * ((cutoff - 1) / dA) ≤ w := by
    rw [hCardA, hCardB]
    calc
      Delta * ((cutoff - 1) / dB) + Delta * ((cutoff - 1) / dA) ≤
          Delta * e + Delta * e := Nat.add_le_add (Nat.mul_le_mul_left _ hDivB)
            (Nat.mul_le_mul_left _ hDivA)
      _ = 2 * Delta * e := by ring
      _ ≤ w := hErrorBudget
  obtain ⟨hSquareSmall, hFractionBudget, hUnionDensity, hRatioBudget,
    hAverageBudget, hMeanBudget, hSelectionBudget⟩ := distance_mixing_scalar_budgets
      delta epsilon Delta (X.activeVerticesOnSide side x).card (Fintype.card G) p
      hTwo hDeltaDistance hSmall heD hDensity hFractionHalf hLower
  have hActualMargin : (3 * (Fintype.card B * ((cutoff - 1) / dB) +
      Fintype.card A * ((cutoff - 1) / dA)) +
      2 * (p * Fintype.card B + Fintype.card A * p) : Nat) <
        ((d - e : Nat) : ℝ) * (delta ^ 2 * Delta / 256) := by
    have hNat : 3 * (Delta * ((cutoff - 1) / dB) + Delta * ((cutoff - 1) / dA)) +
        2 * (p * Delta + Delta * p) ≤ 6 * Delta * e + 4 * Delta * p := by
      have hSum := Nat.add_le_add (Nat.mul_le_mul_left Delta hDivB)
        (Nat.mul_le_mul_left Delta hDivA)
      nlinarith only [hSum]
    rw [hCardA, hCardB]
    have hReal : ((3 * (Delta * ((cutoff - 1) / dB) + Delta * ((cutoff - 1) / dA)) +
        2 * (p * Delta + Delta * p) : Nat) : ℝ) ≤ (6 * Delta * e + 4 * Delta * p : Nat) := by
      exact_mod_cast hNat
    exact hReal.trans_lt hMargin
  apply X.exists_local_weight_reduction_of_finite_mixing hX CA CB dA dB w p
    cutoff (d - e) hA hB (hCardA.trans hCardB.symm) (by omega)
    (by simpa only [hCardA] using hpDegree) (hpD.trans_le hdA) (hpD.trans_le hdB)
    hRobust hPunctures hActualPunctureBudget hNormalPos hNormalWeight
    (hDivB.trans_lt (heD.trans_le hdA)) (hDivA.trans_lt (heD.trans_le hdB))
    (by omega) (by omega) hActualErrorBudget side x hx hLocal
    (4 * Delta) (4 * Real.sqrt (Delta : ℝ)) ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon))
    (delta * Delta / 2) (64 / (Delta : ℝ) ^ (1 - 2 * epsilon))
    (64 / (delta ^ 2 * Delta)) (32 / (Delta : ℝ) * (Delta : ℝ) ^ ((1 : ℝ) / 2 + epsilon))
    (delta ^ 2 * Delta / 256)
    (by positivity) (by positivity) (Real.rpow_pos_of_pos hDPos _)
    (Nat.le_ceil _) (by positivity) (by positivity) hFractionHalf (by positivity)
    (by simpa only [hCardA, hCardB] using hSquareMixing)
    (by simpa only [hCardA, hCardB] using hUnionMixing)
    (by simpa only [hCardA, hCardB] using hSquareSmall) hFractionBudget
    (by simpa only [hCardA, hCardB] using hUnionDensity) hRatioBudget hAverageBudget
    (by simpa only [hCardA, hCardB] using hMeanBudget)
    (by simpa only [hCardA, hCardB] using hSelectionBudget) hActualMargin

end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex

namespace QEC.Coding.QuantumTanner.Data

open QEC.Coding.SmallSetExpansion

universe v

variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

/-- The actual Quantum Tanner CSS minimum satisfies the source's global
distance bound when both local-code pairs have the source robustness and the
actual square and union graphs have the required mixing bounds. The primal
and dual sectors are proved separately; selected-family existence is not a
hypothesis disguised as a distance conclusion. -/
theorem exists_eventual_minimumDistance_ge_of_mixing
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis), D.complex.HasCayleyLinkIdentities →
      ∀ (dA dB dADual dBDual : Nat),
      MinimumDistance D.codeA dA → MinimumDistance D.codeB dB →
      MinimumDistance D.codeA.dual dADual → MinimumDistance D.codeB.dual dBDual →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      delta * Delta ≤ (dADual : ℝ) → delta * Delta ≤ (dBDual : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust D.codeA D.codeB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobust D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance D.codeA D.codeB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      IsRobustWithPunctureResistance D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      (∀ side, HasExpanderMixingBound (D.complex.squareGraph side) (Delta * Delta) (4 * (Delta : ℝ))) →
      HasExpanderMixingBound D.complex.unionCayleyGraph (Delta + Delta) (4 * Real.sqrt (Delta : ℝ)) →
      ∀ distance : Nat, AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode distance →
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤ (distance : ℝ) := by
  obtain ⟨t, ht⟩ := LeftRightCayleySquareComplex.exists_eventual_local_weight_reduction_of_mixing
    delta epsilon gamma
    hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  refine ⟨max t 2, ?_⟩
  intro Delta hDegree G A B Square XBasis ZBasis _ _ _ _ _ _ _ D hX dA dB dADual dBDual hA hB hADual hBDual
    hDistanceA hDistanceB hDistanceADual hDistanceBDual hCardA hCardB
    hRobust hRobustDual hPunctures hPuncturesDual hSquareMixing hUnionMixing distance hmin
  have hLarge : t ≤ Delta := (Nat.le_max_left _ _).trans hDegree
  have hDelta : 0 < Delta := by have := (Nat.le_max_right t 2).trans hDegree; omega
  let bound := delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon))
  have hInteger : Nat.ceil bound ≤ distance := by
    apply D.minimumDistance_ge_of_local_weight_descent (Nat.ceil bound) ?_ ?_ hmin
    · intro x hx hne hSmall
      have hWeight : (HammingWeight x : ℝ) < bound := Nat.lt_ceil.mp hSmall
      have hLocal := D.localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual x hx
      have hActive := D.complex.activeVertices_card_bound_of_small_weight
        D.codeA.dual D.codeB.dual dADual dBDual Delta delta epsilon hDelta hDeltaDistance
        hCardA hCardB hADual hBDual hDistanceADual hDistanceBDual false x hLocal hWeight
      simpa only [Bool.not_false] using ht Delta hLarge G A B Square D.complex hX
        D.codeA.dual D.codeB.dual dADual dBDual hADual hBDual
        hDistanceADual hDistanceBDual hCardA hCardB hRobustDual hPuncturesDual
        false x hne hLocal (hSquareMixing false) hUnionMixing hActive
    · intro x hx hne hSmall
      have hWeight : (HammingWeight x : ℝ) < bound := Nat.lt_ceil.mp hSmall
      have hLocal := D.localRestriction_mem_dualTensorCode_of_mem_firstCoboundaryCheckCode_dual x hx
      have hActive := D.complex.activeVertices_card_bound_of_small_weight
        D.codeA D.codeB dA dB Delta delta epsilon hDelta hDeltaDistance
        hCardA hCardB hA hB hDistanceA hDistanceB true x hLocal hWeight
      simpa only [Bool.not_true] using ht Delta hLarge G A B Square D.complex hX
        D.codeA D.codeB dA dB hA hB hDistanceA hDistanceB hCardA hCardB hRobust hPunctures
        true x hne hLocal (hSquareMixing true) hUnionMixing hActive
  exact (Nat.le_ceil bound).trans (by exact_mod_cast hInteger)

/-- The same global distance theorem with only the actual left/right Cayley
spectral estimates as graph inputs. The square and union mixing hypotheses
are now derived, rather than separately supplied. -/
theorem exists_eventual_minimumDistance_ge_of_cayley_spectral
    (delta epsilon gamma : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis), D.complex.HasCayleyLinkIdentities →
      ∀ (dA dB dADual dBDual : Nat),
      MinimumDistance D.codeA dA → MinimumDistance D.codeB dB →
      MinimumDistance D.codeA.dual dADual → MinimumDistance D.codeB.dual dBDual →
      delta * Delta ≤ (dA : ℝ) → delta * Delta ≤ (dB : ℝ) →
      delta * Delta ≤ (dADual : ℝ) → delta * Delta ≤ (dBDual : ℝ) →
      Fintype.card A = Delta → Fintype.card B = Delta →
      IsRobust D.codeA D.codeB (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobust D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) →
      IsRobustWithPunctureResistance D.codeA D.codeB
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      IsRobustWithPunctureResistance D.codeA.dual D.codeB.dual
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2))) (Nat.floor ((Delta : ℝ) ^ gamma)) →
      HasMeanZeroBilinearBound D.complex.leftCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      HasMeanZeroBilinearBound D.complex.rightCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      ∀ distance : Nat, AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
        D.chainComplex.middleBoundaryCode distance →
      delta * Fintype.card Square / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤ (distance : ℝ) := by
  obtain ⟨t, ht⟩ := exists_eventual_minimumDistance_ge_of_mixing
    delta epsilon gamma hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  refine ⟨t, ?_⟩
  intro Delta hDegree G A B Square XBasis ZBasis _ _ _ _ _ _ _ D hX dA dB dADual dBDual hA hB hADual hBDual
    hDistanceA hDistanceB hDistanceADual hDistanceBDual hCardA hCardB
    hRobust hRobustDual hPunctures hPuncturesDual hLeft hRight distance hmin
  obtain ⟨hSquare, hUnion⟩ := D.complex.mixing_of_cayley_bilinear_bounds hX
    (2 * Real.sqrt (Delta : ℝ)) (2 * Real.sqrt (Delta : ℝ)) (by positivity) (by positivity) hLeft hRight
  have hProduct : (2 * Real.sqrt (Delta : ℝ)) * (2 * Real.sqrt (Delta : ℝ)) =
      4 * (Delta : ℝ) := by nlinarith only [Real.sq_sqrt (Nat.cast_nonneg Delta)]
  have hSum : 2 * Real.sqrt (Delta : ℝ) + 2 * Real.sqrt (Delta : ℝ) =
      4 * Real.sqrt (Delta : ℝ) := by ring
  apply ht Delta hDegree G A B Square XBasis ZBasis D hX dA dB dADual dBDual hA hB hADual hBDual
    hDistanceA hDistanceB hDistanceADual hDistanceBDual hCardA hCardB
    hRobust hRobustDual hPunctures hPuncturesDual ?_ ?_ distance hmin
  · simpa only [hCardA, hCardB, hProduct] using hSquare
  · simpa only [hCardA, hCardB, hSum] using hUnion

end QEC.Coding.QuantumTanner.Data

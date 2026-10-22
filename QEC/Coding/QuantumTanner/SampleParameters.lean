import QEC.Coding.QuantumTanner.Parameters

/-!
# Parameters from one actual local-code sample

The simultaneous matrix event supplies all four local distances and both
puncture-resistance estimates. Positive homology, minimum attainment, rate,
global distance, and locality are then proved for the same commuting data
[LZ22, Sections 3.2 and 4]. The spectral hypotheses concern the actual Cayley
graphs; existence of the selected arithmetic family is not asserted here.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical QEC.Coding.SmallSetExpansion

universe v

/-- Positive dimension supplies a nonzero word, so the finite-code minimum
is attained rather than an extra input to the global distance argument. -/
theorem exists_minimumDistance_of_dimension_pos
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    (hPositive : 0 < Dimension C) : ∃ d : Nat, MinimumDistance C d := by
  apply exists_minimumDistance_of_exists_nonzero C
  apply C.carrier.ne_bot_iff.mp
  intro hBot
  rw [Dimension_eq_finrank_carrier, hBot] at hPositive
  simpa using hPositive

/-- An attained local minimum inherits the real GV budget of the event. -/
theorem minimumDistance_ge_of_ceil_lower_bound
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    (bound : ℝ) (d : Nat) (hLower : HasMinimumDistanceAtLeast C (Nat.ceil bound))
    (hMinimum : MinimumDistance C d) : bound ≤ (d : ℝ) := by
  obtain ⟨x, hx, hx0, hWeight, _⟩ := hMinimum
  exact Nat.ceil_le.mp (hWeight ▸ hLower x hx hx0)

namespace Data

/-- One threshold works for every finite geometry and every successful local
draw. No global distance, rate, or minimum-attainment certificate is assumed. -/
theorem exists_eventual_parameters_of_goodLocalCodeEvent
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 ≤ rho) (hRhoHalf : rho < 1 / 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (G A B Square XBasis ZBasis : Type v)
        [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
        [Fintype XBasis] [Fintype ZBasis],
      ∀ (D : Data G A B Square XBasis ZBasis) (r : Nat), 0 < r → r < Delta →
      (r : ℝ) ≤ rho * Delta →
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∀ (sample : RandomLocalCodeSample r A B),
      D.codeA = sample.codeA → D.codeB = sample.codeB →
      GoodLocalCodeEvent r (Delta - r) (Nat.ceil (delta * Delta))
        (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
        (Nat.floor ((Delta : ℝ) ^ gamma)) sample →
      D.complex.HasCayleyLinkIdentities →
      HasMeanZeroBilinearBound D.complex.leftCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      HasMeanZeroBilinearBound D.complex.rightCayleyGraph (2 * Real.sqrt (Delta : ℝ)) →
      0 < D.blockLength ∧ 0 < D.encodedDimension ∧
      ∃ distance : Nat, D.HasParameters D.blockLength D.encodedDimension distance ∧
        (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) ∧
        delta * D.blockLength / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤
          (distance : ℝ) ∧
        QEC.Coding.BoundedLocality
          (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
          (Delta * Delta) := by
  obtain ⟨t, ht⟩ := exists_eventual_minimumDistance_ge_of_cayley_spectral
    delta epsilon gamma hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
  refine ⟨t, ?_⟩
  intro Delta hLarge G A B Square XBasis ZBasis _ _ _ _ _ _ _ D r hrPositive hrDelta
    hRowRate hCardA hCardB sample hCodeA hCodeB hGood hX hLeft hRight
  obtain ⟨hDimA, hDimB, hLowerA, hLowerB, hLowerADual, hLowerBDual,
    hPunctures, hPuncturesDual⟩ := hGood
  rw [← hCodeA] at hDimA hLowerA hLowerADual
  rw [← hCodeB] at hDimB hLowerB hLowerBDual
  rw [← hCodeA, ← hCodeB] at hPunctures hPuncturesDual
  have hDelta : 0 < Delta := hrPositive.trans hrDelta
  have hDimAPositive : 0 < Dimension D.codeA := by omega
  have hDimBPositive : 0 < Dimension D.codeB := by omega
  have hDimADual : Dimension D.codeA.dual = Delta - r := by
    rw [LinearCode.dual_dimension_eq_length_sub_dimension, Length, hCardA, hDimA]
  have hDimBDual : Dimension D.codeB.dual = r := by
    rw [LinearCode.dual_dimension_eq_length_sub_dimension, Length, hCardB, hDimB,
      Nat.sub_sub_self hrDelta.le]
  obtain ⟨dA, hdA⟩ := exists_minimumDistance_of_dimension_pos D.codeA hDimAPositive
  obtain ⟨dB, hdB⟩ := exists_minimumDistance_of_dimension_pos D.codeB hDimBPositive
  obtain ⟨dADual, hdADual⟩ := exists_minimumDistance_of_dimension_pos D.codeA.dual
    (by omega)
  obtain ⟨dBDual, hdBDual⟩ := exists_minimumDistance_of_dimension_pos D.codeB.dual
    (by omega)
  have hRate := D.source_rate_bound Delta r rho hDelta hCardA hCardB hrDelta.le
    hRho hRhoHalf hRowRate hDimA hDimB
  have hLength : 0 < D.blockLength := by
    have hCard := D.complex.card_group_mul_local_degree_eq_twice_card_square
    rw [hCardA, hCardB] at hCard
    rw [← Nat.mul_assoc] at hCard
    have hGroup : 0 < Fintype.card G := Fintype.card_pos
    have hProduct : 0 < Fintype.card G * Delta * Delta :=
      Nat.mul_pos (Nat.mul_pos hGroup hDelta) hDelta
    change 0 < Fintype.card Square
    omega
  have hDimension : 0 < D.encodedDimension := by
    have hLengthReal : 0 < (D.blockLength : ℝ) := by exact_mod_cast hLength
    have hFactor : 0 < (1 - 2 * rho) ^ 2 := sq_pos_of_pos (by linarith)
    have hDimensionReal := (mul_pos hFactor hLengthReal).trans_le hRate
    exact_mod_cast hDimensionReal
  obtain ⟨distance, hMinimum⟩ := D.exists_minimumDistance_of_encodedDimension_pos hDimension
  refine ⟨hLength, hDimension, distance, ⟨rfl, rfl, hMinimum⟩, hRate, ?_, ?_⟩
  · exact ht Delta hLarge G A B Square XBasis ZBasis D hX dA dB dADual dBDual
      hdA hdB hdADual hdBDual
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerA hdA)
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerB hdB)
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerADual hdADual)
      (minimumDistance_ge_of_ceil_lower_bound _ _ _ hLowerBDual hdBDual)
      hCardA hCardB hPunctures.isRobust hPuncturesDual.isRobust
      hPunctures hPuncturesDual hLeft hRight distance hMinimum
  · exact D.boundaryIncidence_boundedLocality_degreeSquared Delta r
      hCardA hCardB hrDelta.le hDimA hDimB

end Data

/-- Select one matrix draw before the group geometry. On every admissible
four-corner geometry whose actual Cayley graphs satisfy the spectral bounds,
that same draw gives positive rate, attained global distance, and locality.
This does not replace the arithmetic existence proof for those graphs. -/
theorem exists_eventual_good_sample_parameters
    (delta epsilon gamma rho : ℝ) (hDeltaDistance : 0 < delta)
    (hDeltaHalf : delta < 1 / 2)
    (hEpsilon : 0 < epsilon) (hEpsilonHalf : epsilon < 1 / 2)
    (hGammaLower : 1 / 2 + epsilon < gamma) (hGammaUpper : gamma < 1)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      ∀ (A B : Type v) [Fintype A] [Fintype B],
      Fintype.card A = Delta → Fintype.card B = Delta →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho Delta) A B,
        GoodLocalCodeEvent (randomRowCount rho Delta) (Delta - randomRowCount rho Delta)
          (Nat.ceil (delta * Delta))
          (Nat.floor ((Delta : ℝ) ^ ((3 : ℝ) / 2 - epsilon / 2)))
          (Nat.floor ((Delta : ℝ) ^ gamma)) sample ∧
        ∀ (G : Type v) [Group G] [Fintype G]
          (L : A → G) (R : B → G) (invA : Equiv.Perm A) (invB : Equiv.Perm B)
          (hL : Function.Injective L) (hR : Function.Injective R)
          (hLA : ∀ a, L (invA a) = (L a)⁻¹)
          (hRB : ∀ b, R (invB b) = (R b)⁻¹)
          (hTNC : ∀ g a b, L a * g ≠ g * R b),
        HasMeanZeroBilinearBound
          (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).leftCayleyGraph
          (2 * Real.sqrt (Delta : ℝ)) →
        HasMeanZeroBilinearBound
          (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).rightCayleyGraph
          (2 * Real.sqrt (Delta : ℝ)) →
        let D := canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample
        0 < D.blockLength ∧ 0 < D.encodedDimension ∧
          ∃ distance : Nat, D.HasParameters D.blockLength D.encodedDimension distance ∧
            (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) ∧
            delta * D.blockLength / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) ≤
              (distance : ℝ) ∧
            QEC.Coding.BoundedLocality
              (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
              (Delta * Delta) := by
  obtain ⟨tSample, hSample⟩ := exists_eventual_source_goodLocalCodeSample
    epsilon gamma delta rho hEpsilon hEpsilonHalf hGammaLower hGammaUpper
    hDeltaDistance hDeltaHalf hRho hRhoHalf hEntropy
  obtain ⟨tDistance, hDistance⟩ := Data.exists_eventual_parameters_of_goodLocalCodeEvent
    delta epsilon gamma rho hDeltaDistance hEpsilon hEpsilonHalf hGammaLower hGammaUpper
    hRho.le hRhoHalf
  refine ⟨max tSample (max tDistance (max 1 (Nat.ceil (2 / rho)))), ?_⟩
  intro Delta hLarge A B _ _ hCardA hCardB
  have hSampleLarge : tSample ≤ Delta := (Nat.le_max_left _ _).trans hLarge
  have hRemaining := (Nat.le_max_right _ _).trans hLarge
  have hDistanceLarge : tDistance ≤ Delta := (Nat.le_max_left _ _).trans hRemaining
  have hNumerical := (Nat.le_max_right _ _).trans hRemaining
  have hDelta : 0 < Delta := by
    have := (Nat.le_max_left 1 _).trans hNumerical
    omega
  have hRowsPositive : 0 < randomRowCount rho Delta := by
    have hCeil := (Nat.le_max_right 1 _).trans hNumerical
    have hDiv : (2 : ℝ) / rho ≤ Delta := Nat.ceil_le.mp hCeil
    have hMul := (div_le_iff₀ hRho).mp hDiv
    have hFloor := randomRowCount_lt_add_one rho Delta
    have hPositive : (0 : ℝ) < randomRowCount rho Delta := by nlinarith
    exact_mod_cast hPositive
  have hRowsDelta := randomRowCount_lt_degree hRho.le (by linarith) hDelta
  obtain ⟨sample, hGood⟩ := hSample Delta hSampleLarge A B hCardA hCardB
  refine ⟨sample, hGood, ?_⟩
  intro G _ _ L R invA invB hL hR hLA hRB hTNC hLeft hRight
  exact hDistance Delta hDistanceLarge G A B (CayleySquare L R)
    (TensorBasisIndex (tensorCode sample.codeA.dual sample.codeB.dual))
    (TensorBasisIndex (tensorCode sample.codeA sample.codeB))
    (canonicalDataOfLocalCodeSample L R invA invB hL hR hLA hRB hTNC sample)
    (randomRowCount rho Delta) hRowsPositive hRowsDelta (randomRowCount_cast_le hRho.le)
    hCardA hCardB sample rfl rfl hGood
    (cayleySquareComplex_hasCayleyLinkIdentities L R invA invB hL hR hLA hRB hTNC)
    hLeft hRight

end QEC.Coding.QuantumTanner

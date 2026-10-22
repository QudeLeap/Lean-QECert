import QEC.Coding.QuantumTanner.Goodness
import QEC.Coding.QuantumTanner.ExpandingDistance
import QEC.Coding.QuantumTanner.RobustnessTransport

/-!
# Construction-owned Quantum Tanner parameters

The check-count rate bound and attained algebraic distance belong to the
actual chain complex [LZ22, Section 3.2]. They are not independent parameter
certificates. Spectral estimates for a selected arithmetic family remain
separate from these finite-code arguments.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.Data

open Classical

universe v

variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

/-- Rank-nullity bounds the number of encoded qubits using the actual
numbers of chosen local checks, even if those checks are dependent. -/
theorem blockLength_le_encodedDimension_add_checks
    (D : Data G A B Square XBasis ZBasis) :
    D.blockLength ≤ D.encodedDimension +
      Fintype.card G * (Fintype.card XBasis + Fintype.card ZBasis) := by
  have hNull := D.chainComplex.boundary1.finrank_range_add_finrank_ker
  have hFirst := Submodule.finrank_le (LinearMap.range D.chainComplex.boundary1)
  have hSecond := D.chainComplex.boundary2.finrank_range_le
  have hBoundary := Submodule.finrank_mono D.chainComplex.middleBoundaryCode_le_middleCycleCode
  rw [finrank_word_eq_length, Length] at hNull hFirst hSecond
  rw [Fintype.card_prod] at hFirst hSecond
  rw [D.encodedDimension_eq]
  change Fintype.card Square ≤
    Module.finrank (ZMod 2) (LinearMap.ker D.chainComplex.boundary1) -
      Module.finrank (ZMod 2) (LinearMap.range D.chainComplex.boundary2) + _
  change Module.finrank (ZMod 2) (LinearMap.range D.chainComplex.boundary2) ≤
    Module.finrank (ZMod 2) (LinearMap.ker D.chainComplex.boundary1) at hBoundary
  rw [Nat.mul_add]
  omega

/-- Positive middle homology gives an actual nontrivial logical word and
hence an attained algebraic CSS minimum; attainment is not assumed. -/
theorem exists_minimumDistance_of_encodedDimension_pos
    (D : Data G A B Square XBasis ZBasis) (hPositive : 0 < D.encodedDimension) :
    ∃ distance : Nat, AlgebraicCSSMinimumDistance
      D.chainComplex.firstCoboundaryCheckCode D.chainComplex.middleBoundaryCode distance := by
  have hWitness : ∃ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.middleCycleCode.carrier ∧
        x ∉ D.chainComplex.middleBoundaryCode.carrier := by
    by_contra h
    have hLe : D.chainComplex.middleCycleCode.carrier ≤
        D.chainComplex.middleBoundaryCode.carrier := by
      intro x hx
      by_contra hn
      exact h ⟨x, hx, hn⟩
    have hEq := le_antisymm hLe D.chainComplex.middleBoundaryCode_le_middleCycleCode
    rw [D.encodedDimension_eq, Dimension_eq_finrank_carrier,
      Dimension_eq_finrank_carrier, hEq, Nat.sub_self] at hPositive
    omega
  obtain ⟨x, hx, hn⟩ := hWitness
  apply exists_algebraicCSSMinimumDistance_of_exists_logical
  exact ⟨x, Or.inr ⟨by
    rw [D.chainComplex.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
    exact hx, hn⟩⟩

/-- Complementary local-code dimensions and the actual number of squares
give the source rate bound. The real row rate need only be bounded above by
`rho`; flooring the row count therefore does not weaken the bound. -/
theorem source_rate_bound
    (D : Data G A B Square XBasis ZBasis) (Delta r : Nat) (rho : ℝ)
    (hDelta : 0 < Delta) (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta) (hRho : 0 ≤ rho) (hRhoHalf : rho < 1 / 2)
    (hRate : (r : ℝ) ≤ rho * Delta)
    (hCodeA : Dimension D.codeA = r) (hCodeB : Dimension D.codeB = Delta - r) :
    (1 - 2 * rho) ^ 2 * D.blockLength ≤ (D.encodedDimension : ℝ) := by
  have hX : Fintype.card XBasis = (Delta - r) * r := by
    rw [D.toRawData.card_xBasis_eq, Dimension_tensorCode,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      LinearCode.dual_dimension_eq_length_sub_dimension,
      Length, Length, hA, hB, hCodeA, hCodeB, Nat.sub_sub_self hr]
  have hZ : Fintype.card ZBasis = r * (Delta - r) := by
    rw [D.toRawData.card_zBasis_eq, Dimension_tensorCode, hCodeA, hCodeB]
  have hChecks := D.blockLength_le_encodedDimension_add_checks
  rw [hX, hZ] at hChecks
  have hChecksReal : (D.blockLength : ℝ) ≤ D.encodedDimension +
      (Fintype.card G : ℝ) * (((Delta - r : Nat) : ℝ) * r + r * ((Delta - r : Nat) : ℝ)) := by
    exact_mod_cast hChecks
  have hCard := D.complex.card_group_mul_local_degree_eq_twice_card_square
  rw [hA, hB] at hCard
  have hCardNat : Fintype.card G * Delta * Delta = 2 * D.blockLength := by
    simpa only [Data.blockLength, mul_assoc] using hCard
  have hCardReal : (Fintype.card G : ℝ) * Delta * Delta = 2 * D.blockLength := by
    exact_mod_cast hCardNat
  have hSub : ((Delta - r : Nat) : ℝ) = (Delta : ℝ) - r := by
    exact Nat.cast_sub hr
  rw [hSub] at hChecksReal
  have hDeltaReal : 0 < (Delta : ℝ) := by exact_mod_cast hDelta
  have hMargin : 0 ≤ (Delta : ℝ) - rho * Delta - r := by nlinarith
  have hProduct := mul_nonneg (sub_nonneg.mpr hRate) hMargin
  have hLocal : 4 * (r : ℝ) * (Delta - r) ≤
      4 * rho * (1 - rho) * (Delta : ℝ) ^ 2 := by nlinarith only [hProduct]
  have hGlobal := mul_le_mul_of_nonneg_left hLocal
    (show 0 ≤ (Fintype.card G : ℝ) / 2 by positivity)
  nlinarith only [hChecksReal, hCardReal, hGlobal]

end QEC.Coding.QuantumTanner.Data

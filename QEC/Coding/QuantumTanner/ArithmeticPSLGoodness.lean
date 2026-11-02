import QEC.Coding.QuantumTanner.ArithmeticPSLFamily
import QEC.Coding.QuantumTanner.SpectralFamily
import QEC.Coding.ExpanderCodes.PrimeFieldParameters

/-!
# Global code parameters on the concrete arithmetic PSL₂ family

One local-code draw is fixed before the even extension grows. The actual
PSL₂ groups, generators, four-corner incidence laws, fixed local indices and
cofinal group sizes are supplied by the construction, not by assumptions.
The two actual Cayley spectral inequalities remain explicit hypotheses.
This is not an unconditional proof of the LZ22 arithmetic existence theorem.
The terminal theorem also constructs the sufficiently large prime and its
nonsquare parameter; its only external input is a visible complex adjacency
operator bound for the two concrete graphs, as in the existing LPS interface.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily

open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion

variable (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
  (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)

/-- The same binary local-code matrices are used at every extension degree. -/
def sampleFamily (rho : ℝ)
    (sample : RandomLocalCodeSample (randomRowCount rho (p + 1))
      (TorusIndex epsilon) (TorusIndex epsilon)) (n : ℕ) :=
  canonicalDataOfLocalCodeSample
    (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon n) (right_injective p hOdd epsilon hEpsilon n)
    (left_inverse p hOdd epsilon hEpsilon n) (right_inverse p hOdd epsilon hEpsilon n)
    (total_nonconjugacy p hOdd epsilon hEpsilon n) sample

/-- At a sufficiently large fixed prime degree, only the two concrete spectral
estimates are still inputs to the full same-sample global parameter theorem. -/
theorem exists_eventual_sample_of_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : ℕ, ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → t ≤ p + 1 →
      ∃ sample : RandomLocalCodeSample (randomRowCount rho (p + 1))
        (TorusIndex epsilon) (TorusIndex epsilon),
      (∀ n, HasMeanZeroBilinearBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      (∀ n, HasMeanZeroBilinearBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
        (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
        (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
        (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
        (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1) sample := by
  let gamma : ℝ := 3 / 4 + eta / 2
  have hGammaLower : 1 / 2 + eta < gamma := by dsimp [gamma]; linarith
  have hGammaUpper : gamma < 1 := by dsimp [gamma]; linarith
  obtain ⟨t, ht⟩ := exists_eventual_good_sample_family
    delta eta gamma rho hDelta hDeltaHalf hEta hEtaHalf
    hGammaLower hGammaUpper hRho hRhoHalf hEntropy
  refine ⟨t, ?_⟩
  intro p _ hOdd epsilon hEpsilon hNonSquare hLarge
  have hCard := index_card p hOdd epsilon hNonSquare
  obtain ⟨sample, hSample⟩ := ht (p + 1) hLarge
    (TorusIndex epsilon) (TorusIndex epsilon) hCard hCard
  refine ⟨sample, ?_⟩
  intro hLeft hRight
  exact @hSample ℕ (fun n => GroupAt p n)
    (fun _ => inferInstance) (fun n => groupAtFintype p n) (left p hOdd epsilon hEpsilon)
    (right p hOdd epsilon hEpsilon) (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
    (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
    (total_nonconjugacy p hOdd epsilon hEpsilon) hLeft hRight (cofinal_group_card p)

/-- The conditional arithmetic existence theorem. The external spectral
consequence of [DEL21, Claim 6.7] is stated literally for the two constructed
Cayley graphs, rather than as an assumption of code goodness. The generic
complex-to-real and operator-to-bilinear bridges are the same proved
interfaces used by the LPS family assembly. No rank-three/rank-four LSV
equivalence is applied to these rank-two groups.

The prime degree can exceed any requested bound and is fixed before the
single local-code draw and the cofinal extension family are selected. -/
theorem exists_good_arithmetic_family_of_complex_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2)
    (hRamanujan : ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → ∀ n : ℕ,
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) (N : ℕ) :
    ∃ (p : ℕ) (hPrime : p.Prime),
      letI : Fact p.Prime := ⟨hPrime⟩
      ∃ (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
        N ≤ p + 1 ∧ (∀ r : ZMod p, r ^ 2 ≠ epsilon) ∧
        ∃ sample : RandomLocalCodeSample (randomRowCount rho (p + 1))
          (TorusIndex epsilon) (TorusIndex epsilon),
        HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
          (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
          (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
          (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
          (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1) sample := by
  obtain ⟨t, ht⟩ := exists_eventual_sample_of_spectral_bounds
    delta eta rho hDelta hDeltaHalf hEta hEtaHalf hRho hRhoHalf hEntropy
  obtain ⟨p, hPrime, hLarge, hOdd, epsilon, hEpsilon, hNonSquare⟩ :=
    QEC.Coding.ExpanderCodes.exists_large_prime_parameter (max N t)
  letI : Fact p.Prime := ⟨hPrime⟩
  obtain ⟨sample, hSample⟩ := ht p hOdd epsilon hEpsilon hNonSquare
    ((Nat.le_max_right N t).trans hLarge)
  refine ⟨p, hPrime, hOdd, epsilon, hEpsilon,
    (Nat.le_max_left N t).trans hLarge, hNonSquare, sample, ?_⟩
  apply hSample
  · intro n
    exact HasMeanZeroOperatorBound.toBilinearBound (by positivity)
      (hRamanujan p hOdd epsilon hEpsilon hNonSquare n).1.toReal
  · intro n
    exact HasMeanZeroOperatorBound.toBilinearBound (by positivity)
      (hRamanujan p hOdd epsilon hEpsilon hNonSquare n).2.toReal

/-- The source's nonzero-probability formulation for one uniform matrix draw.
The degree is fixed before this draw and before the cofinal family grows.
The finite-uniform event equivalence is already proved in `Goodness`; it adds
no random-code, geometric, rate, distance, or spectral assumption. -/
theorem positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2)
    (hRamanujan : ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → ∀ n : ℕ,
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
      HasMeanZeroComplexOperatorBound
        (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
        (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) (N : ℕ) :
    ∃ (p : ℕ) (hPrime : p.Prime),
      letI : Fact p.Prime := ⟨hPrime⟩
      ∃ (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
        N ≤ p + 1 ∧ (∀ r : ZMod p, r ^ 2 ≠ epsilon) ∧
        HasPositiveUniformProbability
          (HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
            (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
            (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
            (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
            (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1)) := by
  obtain ⟨p, hPrime, hOdd, epsilon, hEpsilon, hLarge, hNonSquare, sample, hGood⟩ :=
    exists_good_arithmetic_family_of_complex_spectral_bounds
      delta eta rho hDelta hDeltaHalf hEta hEtaHalf hRho hRhoHalf hEntropy hRamanujan N
  letI : Fact p.Prime := ⟨hPrime⟩
  refine ⟨p, hPrime, hOdd, epsilon, hEpsilon, hLarge, hNonSquare, ?_⟩
  exact (hasPositiveUniformProbability_iff_exists _).mpr ⟨sample, hGood⟩

/-- The fixed-degree quantifier in [LZ22, Sections 3–4]: every sufficiently
large degree in the selected odd-prime subsequence works, not merely an
unbounded collection of successful degrees. Only the spectral bounds on the
two actual graphs at that fixed degree are external inputs. The threshold
and the one successful matrix draw are independent of those bounds. -/
theorem eventually_positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
    (delta eta rho : ℝ) (hDelta : 0 < delta) (hDeltaHalf : delta < 1 / 2)
    (hEta : 0 < eta) (hEtaHalf : eta < 1 / 2)
    (hRho : 0 < rho) (hRhoHalf : rho < 1 / 2)
    (hEntropy : Real.binEntropy delta < rho * Real.log 2) :
    ∃ t : ℕ, ∀ (p : ℕ) [Fact p.Prime] (hOdd : 3 ≤ p)
      (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0),
      (∀ r : ZMod p, r ^ 2 ≠ epsilon) → t ≤ p + 1 →
      (∀ n : ℕ,
        HasMeanZeroComplexOperatorBound
          (squareComplex p hOdd epsilon hEpsilon n).leftCayleyGraph
          (2 * Real.sqrt ((p + 1 : ℕ) : ℝ)) ∧
        HasMeanZeroComplexOperatorBound
          (squareComplex p hOdd epsilon hEpsilon n).rightCayleyGraph
          (2 * Real.sqrt ((p + 1 : ℕ) : ℝ))) →
      HasPositiveUniformProbability
        (HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
          (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
          (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
          (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
          (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1)) := by
  obtain ⟨t, ht⟩ := exists_eventual_sample_of_spectral_bounds
    delta eta rho hDelta hDeltaHalf hEta hEtaHalf hRho hRhoHalf hEntropy
  refine ⟨t, ?_⟩
  intro p _ hOdd epsilon hEpsilon hNonSquare hLarge hRamanujan
  obtain ⟨sample, hSample⟩ := ht p hOdd epsilon hEpsilon hNonSquare hLarge
  apply (hasPositiveUniformProbability_iff_exists _).mpr
  refine ⟨sample, hSample ?_ ?_⟩
  · intro n
    exact HasMeanZeroOperatorBound.toBilinearBound (by positivity)
      (hRamanujan n).1.toReal
  · intro n
    exact HasMeanZeroOperatorBound.toBilinearBound (by positivity)
      (hRamanujan n).2.toReal

end QEC.Coding.QuantumTanner.ArithmeticPSLFamily

import QEC.Coding.QuantumTanner.ArithmeticPSLGoodness

/-!
# Conditional arithmetic Quantum Tanner family

The final semantic family theorem retains both actual Cayley spectral premises.
Sampled families and spectral-to-parameter methods remain in Coding.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily

open Classical QEC.Coding.ExpanderCodes.QuaternionGenerators QEC.Coding.SmallSetExpansion

-- Compare the canonical family by its constructor instead of expanding all
-- Pauli supports and classical finite enumerations during type inference.
attribute [local irreducible] fintypeTorusIndex cayleySquareFintype Family.ofData

-- Equality decisions are subsingletons. Transport the semantic observation
-- explicitly instead of reducing two different classical decision procedures.
private theorem ofData_good_independent_decidableEq
    {Index : Type} {G A B Square XBasis ZBasis : Index → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (Square i)]
    [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hCofinal : ∀ N : ℕ, ∃ i, N ≤ (family i).blockLength)
    (d₁ d₂ : ∀ i, DecidableEq (Square i)) :
    (letI := d₁
     QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily (Family.ofData family hCofinal)) →
    (letI := d₂
     QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily (Family.ofData family hCofinal)) := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  exact id

/-- Public semantic form of the conditional fixed-degree theorem. The family
in the conclusion is the canonical code family built from the same uniform
local-matrix draw, not an unrelated witness or an assumed goodness field. -/
theorem eventually_positiveProbability_good_arithmetic_code_family_of_complex_spectral_bounds
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
      HasPositiveUniformProbability (fun sample =>
        HasGoodSampleFamily (left p hOdd epsilon hEpsilon) (right p hOdd epsilon hEpsilon)
          (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
          (left_injective p hOdd epsilon hEpsilon) (right_injective p hOdd epsilon hEpsilon)
          (left_inverse p hOdd epsilon hEpsilon) (right_inverse p hOdd epsilon hEpsilon)
          (total_nonconjugacy p hOdd epsilon hEpsilon) delta eta rho (p + 1) sample ∧
        letI : ∀ n, DecidableEq (CayleySquare
            (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)) :=
          fun _ => Subtype.instDecidableEq
        let family := sampleFamily p hOdd epsilon hEpsilon rho sample
        ∃ hCofinal : ∀ N : ℕ, ∃ n, N ≤ (family n).blockLength,
          _root_.QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily
            (Family.ofData family hCofinal)) := by
  obtain ⟨t, ht⟩ :=
    eventually_positiveProbability_good_arithmetic_family_of_complex_spectral_bounds
      delta eta rho hDelta hDeltaHalf hEta hEtaHalf hRho hRhoHalf hEntropy
  refine ⟨t, ?_⟩
  intro p _ hOdd epsilon hEpsilon hNonSquare hLarge hRamanujan
  obtain ⟨sample, hGood⟩ := (hasPositiveUniformProbability_iff_exists _).mp
    (ht p hOdd epsilon hEpsilon hNonSquare hLarge hRamanujan)
  apply (hasPositiveUniformProbability_iff_exists _).mpr
  refine ⟨sample, hGood, ?_⟩
  obtain ⟨hCofinal, hAsymptotic, _, _, _⟩ := hGood
  refine ⟨hCofinal, ?_⟩
  exact ofData_good_independent_decidableEq
    (sampleFamily p hOdd epsilon hEpsilon rho sample) hCofinal _ _ hAsymptotic

end QEC.Coding.QuantumTanner.ArithmeticPSLFamily

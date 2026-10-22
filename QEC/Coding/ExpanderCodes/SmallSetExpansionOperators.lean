import QEC.Coding.ExpanderCodes.SmallSetExpansionSpectrum

/-!
# Sums and compositions of finite graph operators

Keep the unnormalized multiplicities and spectral constants. These elementary
operator laws support the Cayley sum/product estimate in [LZ22, Lemma lem:lambda].
-/

namespace QEC.Coding.SmallSetExpansion

universe u

variable {V : Type u} [Fintype V]

/-- Compose weighted adjacency matrices, counting every intermediate vertex. -/
def compose (M N : WeightedGraph V) : WeightedGraph V :=
  fun v u => ∑ w, M v w * N w u

theorem weightedNeighborSum_compose (M N : WeightedGraph V) (g : V → ℝ) (v : V) :
    weightedNeighborSum (compose M N) g v =
      weightedNeighborSum M (weightedNeighborSum N g) v := by
  classical
  simp only [weightedNeighborSum, compose, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _hw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  ring

theorem adjacencyPairing_add (M N : WeightedGraph V) (f g : V → ℝ) :
    adjacencyPairing (add M N) f g = adjacencyPairing M f g + adjacencyPairing N f g := by
  classical
  simp only [adjacencyPairing, add, Nat.cast_add, add_mul, Finset.sum_add_distrib, mul_add]

/-- Spectral constants add under a weighted graph union. -/
theorem HasMeanZeroBilinearBound.add
    {M N : WeightedGraph V} {lambda mu : ℝ}
    (hM : HasMeanZeroBilinearBound M lambda) (hN : HasMeanZeroBilinearBound N mu) :
    HasMeanZeroBilinearBound (add M N) (lambda + mu) := by
  intro f g hf hg
  rw [adjacencyPairing_add]
  calc
    _ ≤ |adjacencyPairing M f g| + |adjacencyPairing N f g| := abs_add_le _ _
    _ ≤ lambda * Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) +
        mu * Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2) := add_le_add (hM f g hf hg) (hN f g hf hg)
    _ = _ := by ring

/-- Squared mean-zero operator bounds multiply under composition. The second
operator's symmetry and regularity ensure its image remains mean-zero. -/
theorem HasMeanZeroOperatorBound.compose
    {M N : WeightedGraph V} {lambda mu : ℝ} (degreeN : Nat)
    (hSymmetricN : IsSymmetric N) (hRegularN : IsRegular N degreeN)
    (hM : HasMeanZeroOperatorBound M lambda) (hN : HasMeanZeroOperatorBound N mu) :
    HasMeanZeroOperatorBound (compose M N) (lambda * mu) := by
  intro g hg
  have hMean : (∑ v, weightedNeighborSum N g v) = 0 := by
    rw [sum_weightedNeighborSum_eq_degree_mul_sum N degreeN hSymmetricN hRegularN g,
      hg, mul_zero]
  have hFirst := hM (weightedNeighborSum N g) hMean
  have hSecond := mul_le_mul_of_nonneg_left (hN g hg) (sq_nonneg lambda)
  simp_rw [weightedNeighborSum_compose]
  calc
    _ ≤ lambda ^ 2 * ∑ v, (weightedNeighborSum N g v) ^ 2 := hFirst
    _ ≤ lambda ^ 2 * (mu ^ 2 * ∑ v, (g v) ^ 2) := hSecond
    _ = _ := by ring

/-- The two-function spectral estimate for a product of actual symmetric
regular adjacency operators, without a distance or expansion conclusion as input. -/
theorem HasMeanZeroBilinearBound.compose
    {M N : WeightedGraph V} {lambda mu : ℝ} (degreeM degreeN : Nat)
    (hSymmetricM : IsSymmetric M) (hRegularM : IsRegular M degreeM)
    (hSymmetricN : IsSymmetric N) (hRegularN : IsRegular N degreeN)
    (hLambda : 0 ≤ lambda) (hMu : 0 ≤ mu)
    (hM : HasMeanZeroBilinearBound M lambda) (hN : HasMeanZeroBilinearBound N mu) :
    HasMeanZeroBilinearBound (compose M N) (lambda * mu) := by
  apply HasMeanZeroOperatorBound.toBilinearBound (mul_nonneg hLambda hMu)
  exact HasMeanZeroOperatorBound.compose degreeN hSymmetricN hRegularN
    ((hasMeanZeroBilinearBound_iff_operatorBound hSymmetricM hRegularM hLambda).mp hM)
    ((hasMeanZeroBilinearBound_iff_operatorBound hSymmetricN hRegularN hMu).mp hN)

end QEC.Coding.SmallSetExpansion

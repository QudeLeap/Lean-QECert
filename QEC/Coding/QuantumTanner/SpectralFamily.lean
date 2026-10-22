import QEC.Coding.QuantumTanner.SampleParameters

/-!
# One local draw on an expanding geometric family

These family conclusions are derived from concrete four-corner geometry,
cofinal group sizes, and actual Cayley spectral estimates [LZ22, Sections 3–4].
The arithmetic construction of the selected PSL₂ groups and generators is
still a separate obligation; no asymptotic-goodness conclusion is stored in
the geometric input.
-/

noncomputable section

namespace QEC.Coding.QuantumTanner

open Classical QEC.Coding.SmallSetExpansion

universe u v

namespace Family

/-- At a fixed positive degree, cofinal group cardinality implies cofinal
physical length by double-counting the actual square incidences. -/
theorem cofinal_blockLength_of_group_card
    {Index : Type u} {G A B Square XBasis ZBasis : Index → Type v}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (Square i)]
    [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (Delta : Nat) (hDelta : 0 < Delta)
    (hA : ∀ i, Fintype.card (A i) = Delta)
    (hB : ∀ i, Fintype.card (B i) = Delta)
    (hGroups : ∀ N : Nat, ∃ i, N ≤ Fintype.card (G i)) :
    ∀ N : Nat, ∃ i, N ≤ (family i).blockLength := by
  intro N
  obtain ⟨i, hi⟩ := hGroups (2 * N)
  have hCard := (family i).complex.card_group_mul_local_degree_eq_twice_card_square
  rw [hA i, hB i, ← Nat.mul_assoc] at hCard
  have hFirst : Fintype.card (G i) ≤ Fintype.card (G i) * Delta :=
    Nat.le_mul_of_pos_right _ hDelta
  have hSecond : Fintype.card (G i) * Delta ≤ Fintype.card (G i) * Delta * Delta :=
    Nat.le_mul_of_pos_right _ hDelta
  refine ⟨i, ?_⟩
  change N ≤ Fintype.card (Square i)
  omega

end Family

/-- The semantic global conclusions for the actual canonical code family,
including the source's pointwise rate, distance, and degree-squared locality bounds.
This named interface keeps concrete finite-field instances from unfolding
their finite enumerations while a family theorem is specialized. -/
def HasGoodSampleFamily
    {Index : Type u} {G : Index → Type v} {A B : Type v}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [Fintype A] [Fintype B]
    (L : ∀ i, A → G i) (R : ∀ i, B → G i)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : ∀ i, Function.Injective (L i)) (hR : ∀ i, Function.Injective (R i))
    (hLA : ∀ i a, L i (invA a) = (L i a)⁻¹)
    (hRB : ∀ i b, R i (invB b) = (R i b)⁻¹)
    (hTNC : ∀ i g a b, L i a * g ≠ g * R i b)
    (delta eta rho : ℝ) (Delta : ℕ)
    (sample : RandomLocalCodeSample (randomRowCount rho Delta) A B) : Prop :=
  let family := fun i => canonicalDataOfLocalCodeSample (L i) (R i) invA invB
    (hL i) (hR i) (hLA i) (hRB i) (hTNC i) sample
  ∃ hCofinal : ∀ N : ℕ, ∃ i, N ≤ (family i).blockLength,
    QEC.QLDPC.IsAsymptoticallyGoodQLDPCFamily (Family.ofData family hCofinal) ∧
    QEC.QLDPC.HasEventualRateAtLeast (Family.ofData family hCofinal)
      ((1 - 2 * rho) ^ 2) ∧
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast (Family.ofData family hCofinal)
      (delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + eta))) ∧
    ∀ i,
      (1 - 2 * rho) ^ 2 * (family i).blockLength ≤ ((family i).encodedDimension : ℝ) ∧
      delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + eta)) *
          ((Family.ofData family hCofinal).blockLength i : ℝ) ≤
        ((Family.ofData family hCofinal).distance i : ℝ) ∧
      QEC.Coding.BoundedLocality ((Family.ofData family hCofinal).localityProfile i)
        (Delta * Delta)

/-- A single successful local draw works on every supplied cofinal geometric
family at the chosen degree. Global distance and rate are proved, not assumed;
only the actual spectral and arithmetic-geometric inputs remain conditional. -/
theorem exists_eventual_good_sample_family
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
        ∀ (Index : Type u) (G : Index → Type v)
          [∀ i, Group (G i)] [∀ i, Fintype (G i)]
          (L : ∀ i, A → G i) (R : ∀ i, B → G i)
          (invA : Equiv.Perm A) (invB : Equiv.Perm B)
          (hL : ∀ i, Function.Injective (L i)) (hR : ∀ i, Function.Injective (R i))
          (hLA : ∀ i a, L i (invA a) = (L i a)⁻¹)
          (hRB : ∀ i b, R i (invB b) = (R i b)⁻¹)
          (hTNC : ∀ i g a b, L i a * g ≠ g * R i b),
        (∀ i, HasMeanZeroBilinearBound
          (cayleySquareComplex (L i) (R i) invA invB (hL i) (hR i) (hLA i) (hRB i)
            (hTNC i)).leftCayleyGraph (2 * Real.sqrt (Delta : ℝ))) →
        (∀ i, HasMeanZeroBilinearBound
          (cayleySquareComplex (L i) (R i) invA invB (hL i) (hR i) (hLA i) (hRB i)
            (hTNC i)).rightCayleyGraph (2 * Real.sqrt (Delta : ℝ))) →
        (∀ N : Nat, ∃ i, N ≤ Fintype.card (G i)) →
        HasGoodSampleFamily L R invA invB hL hR hLA hRB hTNC
          delta epsilon rho Delta sample := by
  obtain ⟨t, ht⟩ := exists_eventual_good_sample_parameters
    delta epsilon gamma rho hDeltaDistance hDeltaHalf hEpsilon hEpsilonHalf
    hGammaLower hGammaUpper hRho hRhoHalf hEntropy
  refine ⟨max t 1, ?_⟩
  intro Delta hLarge A B _ _ hCardA hCardB
  have hDegree : 0 < Delta := by
    have := (Nat.le_max_right t 1).trans hLarge
    omega
  obtain ⟨sample, _hGood, hSample⟩ := ht Delta
    ((Nat.le_max_left _ _).trans hLarge) A B hCardA hCardB
  refine ⟨sample, ?_⟩
  intro Index G _ _ L R invA invB hL hR hLA hRB hTNC hLeft hRight hGroups
  unfold HasGoodSampleFamily
  let family := fun i => canonicalDataOfLocalCodeSample (L i) (R i) invA invB
    (hL i) (hR i) (hLA i) (hRB i) (hTNC i) sample
  have hCofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength :=
    Family.cofinal_blockLength_of_group_card family Delta hDegree
      (fun _ => hCardA) (fun _ => hCardB) hGroups
  have hFinite (i : Index) := hSample (G i) (L i) (R i) invA invB
    (hL i) (hR i) (hLA i) (hRB i) (hTNC i) (hLeft i) (hRight i)
  let distance : Index → Nat := fun i => Classical.choose (hFinite i).2.2
  have hBounds (i : Index) := Classical.choose_spec (hFinite i).2.2
  have hParameters (i : Index) :
      (family i).HasParameters (family i).blockLength (family i).encodedDimension (distance i) :=
    (hBounds i).1
  have hRate : QEC.QLDPC.HasEventualRateAtLeast (Family.ofData family hCofinal)
      ((1 - 2 * rho) ^ 2) := by
    refine ⟨0, fun i _ => ?_⟩
    exact (hBounds i).2.1
  have hDistancePointwise (i : Index) :
      delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) *
          ((Family.ofData family hCofinal).blockLength i : ℝ) ≤
        ((Family.ofData family hCofinal).distance i : ℝ) := by
    have hSemantic := Family.ofData_distance_ge_of_hasParameters family hCofinal i (hParameters i)
    have hBound := (hBounds i).2.2.1
    have hBoundReal : delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) *
        (family i).blockLength ≤ (distance i : ℝ) := by
      simpa only [div_mul_eq_mul_div] using hBound
    exact hBoundReal.trans (by exact_mod_cast hSemantic)
  have hDistance : QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (Family.ofData family hCofinal)
      (delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon))) :=
    ⟨0, fun i _ => hDistancePointwise i⟩
  have hLocalityPointwise (i : Index) :
      QEC.Coding.BoundedLocality ((Family.ofData family hCofinal).localityProfile i)
        (Delta * Delta) := by
    rw [Family.ofData_localityProfile]
    exact (hBounds i).2.2.2
  have hLocality : QEC.QLDPC.HasUniformLDPC (Family.ofData family hCofinal) :=
    ⟨Delta * Delta, hLocalityPointwise⟩
  have hRatePositive : 0 < (1 - 2 * rho) ^ 2 := sq_pos_of_pos (by linarith)
  have hDistancePositive : 0 < delta / (4 * (Delta : ℝ) ^ ((3 : ℝ) / 2 + epsilon)) := by
    apply div_pos hDeltaDistance
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hDegree) _)
  exact ⟨hCofinal, ⟨hLocality, ⟨_, hRatePositive, hRate⟩,
    ⟨_, hDistancePositive, hDistance⟩⟩, hRate, hDistance,
    fun i => ⟨(hBounds i).2.1, hDistancePointwise i, hLocalityPointwise i⟩⟩

end QEC.Coding.QuantumTanner

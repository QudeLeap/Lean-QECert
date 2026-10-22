import QEC.Coding.ExpanderCodes.JacobiParityReindex

/-!
# Coefficient reindexing in Jacobi's cube identity

This module lifts the parity equivalence on integer pairs to the finite
coefficient fibres in Jacobi's cube identity.  It is the combinatorial step
between the signed triangular cube series and the weighted theta series.
-/

namespace QEC.Coding.TannerLiftedProduct

open Finset PowerSeries

/-- Pairs occurring at degree `n` after Jacobi's parity change of variables. -/
abbrev JacobiReindexedPair (n : ℕ) :=
  {p : ℤ × ℤ // p.1 ^ 2 + p.1 + p.2 ^ 2 = n}

/-- Pairs occurring at degree `n` in the square of Jacobi's signed
half-triangular series. -/
abbrev JacobiCubePair (n : ℕ) :=
  {p : ℤ × ℤ //
    p.1 ^ 2 + p.1 + p.2 ^ 2 + p.2 = 2 * n}

/-- A concrete finite carrier for the reindexed coefficient fibre. -/
noncomputable def jacobiReindexedPairs (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-((n : ℤ)) - 1) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun p =>
    p.1 ^ 2 + p.1 + p.2 ^ 2 = n

theorem mem_jacobiReindexedPairs_iff (n : ℕ) (p : ℤ × ℤ) :
    p ∈ jacobiReindexedPairs n ↔
      p.1 ^ 2 + p.1 + p.2 ^ 2 = n := by
  rw [jacobiReindexedPairs, Finset.mem_filter]
  refine and_iff_right_of_imp fun hp => ?_
  simp only [Finset.mem_product, Finset.mem_Icc]
  have hn : (0 : ℤ) ≤ n := by positivity
  have hs_nonneg : 0 ≤ p.1 ^ 2 + p.1 := by
    by_cases hs : 0 ≤ p.1
    · nlinarith [sq_nonneg p.1]
    · have hs' : p.1 ≤ -1 := by omega
      nlinarith [sq_nonneg (p.1 + 1)]
  have ht_sq : p.2 ^ 2 ≤ n := by nlinarith
  have hs_tri : p.1 ^ 2 + p.1 ≤ n := by
    nlinarith [sq_nonneg p.2]
  constructor
  · constructor
    · by_cases hs : -1 ≤ p.1
      · omega
      · nlinarith [sq_nonneg (p.1 + 1)]
    · by_cases hs : p.1 ≤ 0
      · omega
      · nlinarith [sq_nonneg p.1]
  · constructor <;> nlinarith [sq_nonneg p.2]

noncomputable instance (n : ℕ) : Fintype (JacobiReindexedPair n) :=
  Fintype.ofEquiv
    {p : ℤ × ℤ // p ∈ jacobiReindexedPairs n}
    (Equiv.subtypeEquivRight fun p => mem_jacobiReindexedPairs_iff n p)

/-- On every coefficient fibre, the two parity charts give two copies of
the same reindexed fibre. -/
noncomputable def jacobiCubePairEquiv (n : ℕ) :
    (JacobiReindexedPair n ⊕ JacobiReindexedPair n) ≃ JacobiCubePair n :=
  let P : (ℤ × ℤ) ⊕ (ℤ × ℤ) → Prop
    | .inl p => p.1 ^ 2 + p.1 + p.2 ^ 2 = n
    | .inr p => p.1 ^ 2 + p.1 + p.2 ^ 2 = n
  let Q : ℤ × ℤ → Prop := fun p =>
    p.1 ^ 2 + p.1 + p.2 ^ 2 + p.2 = 2 * n
  Equiv.subtypeSum.symm.trans <|
    jacobiParityReindex.subtypeEquiv (p := P) (q := Q) fun p => by
      cases p with
      | inl p =>
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔ _
          rw [jacobiParityReindex_inl]
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔
            (p.1 + p.2) ^ 2 + (p.1 + p.2) +
              (p.1 - p.2) ^ 2 + (p.1 - p.2) = 2 * n
          rw [jacobi_sameParity_exponent]
          omega
      | inr p =>
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔ _
          rw [jacobiParityReindex_inr]
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔
            (p.1 + p.2) ^ 2 + (p.1 + p.2) +
              (p.2 - p.1 - 1) ^ 2 + (p.2 - p.1 - 1) = 2 * n
          rw [jacobi_oppositeParity_exponent]
          omega

noncomputable instance (n : ℕ) : Fintype (JacobiCubePair n) :=
  Fintype.ofEquiv
    (JacobiReindexedPair n ⊕ JacobiReindexedPair n)
    (jacobiCubePairEquiv n)

@[simp] theorem jacobiCubePairEquiv_inl_val (n : ℕ)
    (p : JacobiReindexedPair n) :
    (jacobiCubePairEquiv n (Sum.inl p)).1 =
      (p.1.1 + p.1.2, p.1.1 - p.1.2) := by
  rfl

@[simp] theorem jacobiCubePairEquiv_inr_val (n : ℕ)
    (p : JacobiReindexedPair n) :
    (jacobiCubePairEquiv n (Sum.inr p)).1 =
      (p.1.1 + p.1.2, p.1.2 - p.1.1 - 1) := by
  rfl

/-- The sign `(-1)^z`, written without integer exponentiation. -/
def jacobiParitySign (z : ℤ) : ℚ :=
  if Even z then 1 else -1

theorem jacobiParitySign_same_chart (s t : ℤ) :
    jacobiParitySign ((s + t) + (s - t)) = 1 := by
  rw [jacobiParitySign, if_pos]
  exact ⟨s, by ring⟩

theorem jacobiParitySign_opposite_chart (s t : ℤ) :
    jacobiParitySign ((s + t) + (t - s - 1)) = -1 := by
  rw [jacobiParitySign, if_neg]
  intro h
  obtain ⟨r, hr⟩ := h
  omega

theorem jacobiParitySign_add (k l : ℤ) :
    jacobiParitySign k * jacobiParitySign l =
      jacobiParitySign (k + l) := by
  by_cases hk : Even k <;> by_cases hl : Even l <;>
    simp [jacobiParitySign, hk, hl, Int.even_add]

/-- Signed weight in the square of Jacobi's cube series. -/
def jacobiCubePairWeight (p : ℤ × ℤ) : ℚ :=
  jacobiParitySign (p.1 + p.2) *
    (2 * (p.1 : ℚ) + 1) * (2 * (p.2 : ℚ) + 1)

/-- Weight after the parity change of variables. -/
def jacobiReindexedPairWeight (p : ℤ × ℤ) : ℚ :=
  (2 * (p.1 : ℚ) + 1) ^ 2 - (2 * (p.2 : ℚ)) ^ 2

@[simp] theorem jacobiCubePairWeight_equiv_inl (n : ℕ)
    (p : JacobiReindexedPair n) :
    jacobiCubePairWeight (jacobiCubePairEquiv n (Sum.inl p)).1 =
      jacobiReindexedPairWeight p.1 := by
  rcases p with ⟨⟨s, t⟩, hp⟩
  simp only [jacobiCubePairEquiv_inl_val, jacobiCubePairWeight,
    jacobiReindexedPairWeight, jacobiParitySign_same_chart,
    one_mul]
  exact_mod_cast jacobi_sameParity_weight s t

@[simp] theorem jacobiCubePairWeight_equiv_inr (n : ℕ)
    (p : JacobiReindexedPair n) :
    jacobiCubePairWeight (jacobiCubePairEquiv n (Sum.inr p)).1 =
      jacobiReindexedPairWeight p.1 := by
  rcases p with ⟨⟨s, t⟩, hp⟩
  simp only [jacobiCubePairEquiv_inr_val, jacobiCubePairWeight,
    jacobiReindexedPairWeight, jacobiParitySign_opposite_chart,
    neg_one_mul]
  exact_mod_cast jacobi_oppositeParity_weight s t

/-- The parity reindexing turns the signed cube-pair sum into two identical
copies of the weighted reindexed sum. -/
theorem sum_jacobiCubePairWeight (n : ℕ) :
    (∑ p : JacobiCubePair n, jacobiCubePairWeight p.1) =
      2 * ∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1 := by
  calc
    (∑ p : JacobiCubePair n, jacobiCubePairWeight p.1) =
        ∑ p : JacobiReindexedPair n ⊕ JacobiReindexedPair n,
          jacobiCubePairWeight (jacobiCubePairEquiv n p).1 :=
      (Equiv.sum_comp (jacobiCubePairEquiv n)
        (fun p : JacobiCubePair n => jacobiCubePairWeight p.1)).symm
    _ = (∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1) +
        ∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1 := by
      rw [Fintype.sum_sum_type]
      congr 1
      · apply Fintype.sum_congr
        intro p
        simpa using jacobiCubePairWeight_equiv_inl n p
      · apply Fintype.sum_congr
        intro p
        simpa using jacobiCubePairWeight_equiv_inr n p
    _ = 2 * ∑ p : JacobiReindexedPair n,
        jacobiReindexedPairWeight p.1 := by ring

/-- The nonnegative half-triangular degree `z(z+1)/2`. -/
def jacobiHalfTriangularDegree (z : ℤ) : ℕ :=
  ((z ^ 2 + z) / 2).toNat

theorem two_mul_jacobiHalfTriangularDegree (z : ℤ) :
    2 * (jacobiHalfTriangularDegree z : ℤ) = z ^ 2 + z := by
  have hnonneg : 0 ≤ z ^ 2 + z := by
    by_cases hz : 0 ≤ z
    · nlinarith [sq_nonneg z]
    · have hz' : z ≤ -1 := by omega
      nlinarith [sq_nonneg (z + 1)]
  have heven : Even (z ^ 2 + z) := by
    simpa [pow_two, mul_add] using Int.even_mul_succ_self z
  have hhalf : 2 * ((z ^ 2 + z) / 2) = z ^ 2 + z :=
    Int.two_mul_ediv_two_of_even heven
  have hhalf_nonneg : 0 ≤ (z ^ 2 + z) / 2 := by nlinarith
  rw [jacobiHalfTriangularDegree, Int.toNat_of_nonneg hhalf_nonneg]
  exact hhalf

theorem mem_integerTriangularRoots_two_mul_degree (z : ℤ) :
    z ∈ integerTriangularRoots (2 * jacobiHalfTriangularDegree z) := by
  rw [mem_integerTriangularRoots_iff]
  rw [← two_mul_jacobiHalfTriangularDegree z]
  norm_num

theorem jacobiHalfTriangularDegree_eq_of_mem
    {n : ℕ} {z : ℤ} (hz : z ∈ integerTriangularRoots (2 * n)) :
    jacobiHalfTriangularDegree z = n := by
  have hz' := (mem_integerTriangularRoots_iff (2 * n) z).mp hz
  have hd := two_mul_jacobiHalfTriangularDegree z
  norm_num at hz' hd
  omega

theorem two_mul_jacobiHalfTriangularDegree_eq_of_mem
    {n : ℕ} {z : ℤ} (hz : z ∈ integerTriangularRoots n) :
    2 * jacobiHalfTriangularDegree z = n := by
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast
  rw [two_mul_jacobiHalfTriangularDegree]
  exact (mem_integerTriangularRoots_iff n z).mp hz

/-- The square degree of an integer. -/
def jacobiSquareDegree (z : ℤ) : ℕ := z.natAbs ^ 2

theorem jacobiSquareDegree_cast (z : ℤ) :
    (jacobiSquareDegree z : ℤ) = z ^ 2 := by
  simp [jacobiSquareDegree]

theorem mem_integerSquareRoots_jacobiSquareDegree (z : ℤ) :
    z ∈ integerSquareRoots (jacobiSquareDegree z) := by
  rw [mem_integerSquareRoots_iff, ← jacobiSquareDegree_cast]

theorem jacobiSquareDegree_eq_of_mem
    {n : ℕ} {z : ℤ} (hz : z ∈ integerSquareRoots n) :
    jacobiSquareDegree z = n := by
  rw [← Nat.cast_inj (R := ℤ), jacobiSquareDegree_cast]
  exact (mem_integerSquareRoots_iff n z).mp hz

/-- A coefficient witness for the square of the signed half-triangular
series: split the degree, then choose one root in each factor. -/
abbrev JacobiCubeCoeffWitness (n : ℕ) :=
  Σ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
    {k : ℤ // k ∈ integerTriangularRoots (2 * ij.1.1)} ×
      {l : ℤ // l ∈ integerTriangularRoots (2 * ij.1.2)}

/-- Cauchy-product witnesses are exactly the integral cube-pair fibre. -/
noncomputable def jacobiCubeCoeffWitnessEquiv (n : ℕ) :
    JacobiCubeCoeffWitness n ≃ JacobiCubePair n where
  toFun w := ⟨(w.2.1.1, w.2.2.1), by
    have hk := (mem_integerTriangularRoots_iff
      (2 * w.1.1.1) w.2.1.1).mp w.2.1.2
    have hl := (mem_integerTriangularRoots_iff
      (2 * w.1.1.2) w.2.2.1).mp w.2.2.2
    have hij := Finset.mem_antidiagonal.mp w.1.2
    norm_num at hk hl
    have hijz : (w.1.1.1 : ℤ) + (w.1.1.2 : ℤ) = n := by
      exact_mod_cast hij
    calc
      w.2.1.1 ^ 2 + w.2.1.1 + w.2.2.1 ^ 2 + w.2.2.1 =
          2 * (w.1.1.1 : ℤ) + 2 * (w.1.1.2 : ℤ) := by nlinarith
      _ = 2 * n := by nlinarith⟩
  invFun p :=
    ⟨⟨(jacobiHalfTriangularDegree p.1.1,
          jacobiHalfTriangularDegree p.1.2), by
        rw [Finset.mem_antidiagonal]
        have hk := two_mul_jacobiHalfTriangularDegree p.1.1
        have hl := two_mul_jacobiHalfTriangularDegree p.1.2
        omega⟩,
      ⟨⟨p.1.1, mem_integerTriangularRoots_two_mul_degree p.1.1⟩,
        ⟨p.1.2, mem_integerTriangularRoots_two_mul_degree p.1.2⟩⟩⟩
  left_inv w := by
    rcases w with ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨k, hk⟩, ⟨l, hl⟩⟩⟩
    have hi := jacobiHalfTriangularDegree_eq_of_mem hk
    have hj := jacobiHalfTriangularDegree_eq_of_mem hl
    change jacobiHalfTriangularDegree k = i at hi
    change jacobiHalfTriangularDegree l = j at hj
    subst i
    subst j
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Coefficient witnesses for a square-theta factor followed by a
triangular-theta factor. -/
abbrev JacobiReindexedCoeffWitness (n : ℕ) :=
  Σ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
    {t : ℤ // t ∈ integerSquareRoots ij.1.1} ×
      {s : ℤ // s ∈ integerTriangularRoots ij.1.2}

/-- The theta/triangular Cauchy-product witnesses are exactly the reindexed
integer-pair fibre. -/
noncomputable def jacobiReindexedCoeffWitnessEquiv (n : ℕ) :
    JacobiReindexedCoeffWitness n ≃ JacobiReindexedPair n where
  toFun w := ⟨(w.2.2.1, w.2.1.1), by
    have ht := (mem_integerSquareRoots_iff w.1.1.1 w.2.1.1).mp w.2.1.2
    have hs := (mem_integerTriangularRoots_iff w.1.1.2 w.2.2.1).mp w.2.2.2
    have hij := Finset.mem_antidiagonal.mp w.1.2
    have hijz : (w.1.1.1 : ℤ) + (w.1.1.2 : ℤ) = n := by
      exact_mod_cast hij
    nlinarith⟩
  invFun p :=
    ⟨⟨(jacobiSquareDegree p.1.2,
          2 * jacobiHalfTriangularDegree p.1.1), by
        rw [Finset.mem_antidiagonal]
        have ht := jacobiSquareDegree_cast p.1.2
        have hs := two_mul_jacobiHalfTriangularDegree p.1.1
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        nlinarith [p.2]⟩,
      ⟨⟨p.1.2, mem_integerSquareRoots_jacobiSquareDegree p.1.2⟩,
        ⟨p.1.1, mem_integerTriangularRoots_two_mul_degree p.1.1⟩⟩⟩
  left_inv w := by
    rcases w with ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨t, ht⟩, ⟨s, hs⟩⟩⟩
    have hi := jacobiSquareDegree_eq_of_mem ht
    have hj := two_mul_jacobiHalfTriangularDegree_eq_of_mem hs
    change jacobiSquareDegree t = i at hi
    change 2 * jacobiHalfTriangularDegree s = j at hj
    subst i
    subst j
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- The bilateral signed half-triangular series before the factor `1/2`. -/
noncomputable def jacobiSignedCubeSeriesRaw : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ z : {z : ℤ // z ∈ integerTriangularRoots (2 * n)},
      jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1)

@[simp] theorem coeff_jacobiSignedCubeSeriesRaw (n : ℕ) :
    PowerSeries.coeff n jacobiSignedCubeSeriesRaw =
      ∑ z : {z : ℤ // z ∈ integerTriangularRoots (2 * n)},
        jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1) := by
  simp [jacobiSignedCubeSeriesRaw]

/-- Jacobi's normalized signed cube series
`1/2 ∑ (-1)^z (2z+1) X^(z(z+1)/2)`. -/
noncomputable def jacobiSignedCubeSeries : ℚ⟦X⟧ :=
  PowerSeries.C (1 / 2 : ℚ) * jacobiSignedCubeSeriesRaw

@[simp] theorem coeff_jacobiSignedCubeSeries (n : ℕ) :
    PowerSeries.coeff n jacobiSignedCubeSeries =
      (1 / 2 : ℚ) *
        ∑ z : {z : ℤ // z ∈ integerTriangularRoots (2 * n)},
          jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1) := by
  simp [jacobiSignedCubeSeries]

private def jacobiCubeCoeffWitnessWeight {n : ℕ}
    (w : JacobiCubeCoeffWitness n) : ℚ :=
  (jacobiParitySign w.2.1.1 * (2 * (w.2.1.1 : ℚ) + 1)) *
    (jacobiParitySign w.2.2.1 * (2 * (w.2.2.1 : ℚ) + 1))

private theorem jacobiCubeCoeffWitnessWeight_eq_pairWeight
    {n : ℕ} (w : JacobiCubeCoeffWitness n) :
    jacobiCubeCoeffWitnessWeight w =
      jacobiCubePairWeight (jacobiCubeCoeffWitnessEquiv n w).1 := by
  rw [jacobiCubeCoeffWitnessWeight, jacobiCubePairWeight]
  change
    (jacobiParitySign w.2.1.1 * (2 * (w.2.1.1 : ℚ) + 1)) *
        (jacobiParitySign w.2.2.1 * (2 * (w.2.2.1 : ℚ) + 1)) =
      jacobiParitySign (w.2.1.1 + w.2.2.1) *
        (2 * (w.2.1.1 : ℚ) + 1) * (2 * (w.2.2.1 : ℚ) + 1)
  rw [← jacobiParitySign_add]
  ring

theorem coeff_jacobiSignedCubeSeriesRaw_sq (n : ℕ) :
    PowerSeries.coeff n (jacobiSignedCubeSeriesRaw ^ 2) =
      ∑ p : JacobiCubePair n, jacobiCubePairWeight p.1 := by
  rw [pow_two, PowerSeries.coeff_mul, ← Finset.sum_attach]
  simp only [Finset.attach_eq_univ, coeff_jacobiSignedCubeSeriesRaw]
  calc
    (∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        (∑ k : {k : ℤ // k ∈ integerTriangularRoots (2 * ij.1.1)},
          jacobiParitySign k.1 * (2 * (k.1 : ℚ) + 1)) *
        ∑ l : {l : ℤ // l ∈ integerTriangularRoots (2 * ij.1.2)},
          jacobiParitySign l.1 * (2 * (l.1 : ℚ) + 1)) =
      ∑ w : JacobiCubeCoeffWitness n,
        jacobiCubeCoeffWitnessWeight w := by
          rw [Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ij
          rw [Fintype.sum_prod_type]
          exact Fintype.sum_mul_sum _ _
    _ = ∑ w : JacobiCubeCoeffWitness n,
        jacobiCubePairWeight (jacobiCubeCoeffWitnessEquiv n w).1 := by
      apply Fintype.sum_congr
      exact jacobiCubeCoeffWitnessWeight_eq_pairWeight
    _ = ∑ p : JacobiCubePair n, jacobiCubePairWeight p.1 :=
      Equiv.sum_comp (jacobiCubeCoeffWitnessEquiv n)
        (fun p : JacobiCubePair n => jacobiCubePairWeight p.1)

theorem coeff_theta_mul_jacobiWeightedTriangularSeries (n : ℕ) :
    PowerSeries.coeff n
        (rationalIntegerThetaSeries * jacobiWeightedTriangularSeries) =
      ∑ p : JacobiReindexedPair n, (2 * (p.1.1 : ℚ) + 1) ^ 2 := by
  rw [PowerSeries.coeff_mul, ← Finset.sum_attach]
  simp only [Finset.attach_eq_univ, coeff_rationalIntegerThetaSeries,
    coeff_jacobiWeightedTriangularSeries]
  calc
    (∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        ((integerSquareRoots ij.1.1).card : ℚ) *
          ∑ s ∈ integerTriangularRoots ij.1.2,
            (2 * (s : ℚ) + 1) ^ 2) =
      ∑ w : JacobiReindexedCoeffWitness n,
        (2 * (w.2.2.1 : ℚ) + 1) ^ 2 := by
          rw [Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ij
          rw [Fintype.sum_prod_type]
          simp
          left
          exact (Finset.sum_attach
            (integerTriangularRoots ij.1.2)
            (fun s : ℤ => (2 * (s : ℚ) + 1) ^ 2)).symm
    _ = ∑ w : JacobiReindexedCoeffWitness n,
        (2 * ((jacobiReindexedCoeffWitnessEquiv n w).1.1 : ℚ) + 1) ^ 2 := by
      rfl
    _ = ∑ p : JacobiReindexedPair n, (2 * (p.1.1 : ℚ) + 1) ^ 2 :=
      Equiv.sum_comp (jacobiReindexedCoeffWitnessEquiv n)
        (fun p : JacobiReindexedPair n => (2 * (p.1.1 : ℚ) + 1) ^ 2)

theorem coeff_jacobiWeightedSquareSeries_mul_bilateral (n : ℕ) :
    PowerSeries.coeff n
        (jacobiWeightedSquareSeries * rationalBilateralTriangularSeries) =
      ∑ p : JacobiReindexedPair n, (2 * (p.1.2 : ℚ)) ^ 2 := by
  rw [PowerSeries.coeff_mul, ← Finset.sum_attach]
  simp only [Finset.attach_eq_univ, coeff_jacobiWeightedSquareSeries,
    coeff_rationalBilateralTriangularSeries]
  calc
    (∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        (∑ t ∈ integerSquareRoots ij.1.1, (2 * (t : ℚ)) ^ 2) *
          ((integerTriangularRoots ij.1.2).card : ℚ)) =
      ∑ w : JacobiReindexedCoeffWitness n,
        (2 * (w.2.1.1 : ℚ)) ^ 2 := by
          rw [Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ij
          rw [Fintype.sum_prod_type]
          simp
          rw [← Finset.mul_sum]
          have hsum :
              (∑ t ∈ (integerSquareRoots ij.1.1).attach,
                (2 * (t.1 : ℚ)) ^ 2) =
                ∑ t ∈ integerSquareRoots ij.1.1,
                  (2 * (t : ℚ)) ^ 2 :=
            Finset.sum_attach (integerSquareRoots ij.1.1)
              (fun t : ℤ => (2 * (t : ℚ)) ^ 2)
          rw [hsum]
          ring
    _ = ∑ w : JacobiReindexedCoeffWitness n,
        (2 * ((jacobiReindexedCoeffWitnessEquiv n w).1.2 : ℚ)) ^ 2 := by
      rfl
    _ = ∑ p : JacobiReindexedPair n, (2 * (p.1.2 : ℚ)) ^ 2 :=
      Equiv.sum_comp (jacobiReindexedCoeffWitnessEquiv n)
        (fun p : JacobiReindexedPair n => (2 * (p.1.2 : ℚ)) ^ 2)

/-- Coefficientwise form of Jacobi's parity reindexing: the square of the
signed cube series is the difference of the two weighted theta products. -/
theorem jacobiSignedCubeSeries_sq_eq_weighted_reindex :
    jacobiSignedCubeSeries ^ 2 =
      PowerSeries.C (1 / 2 : ℚ) *
        (rationalIntegerThetaSeries * jacobiWeightedTriangularSeries -
          jacobiWeightedSquareSeries * rationalBilateralTriangularSeries) := by
  ext n
  rw [jacobiSignedCubeSeries]
  have hscale :
      (PowerSeries.C (1 / 2 : ℚ) * jacobiSignedCubeSeriesRaw) ^ 2 =
        PowerSeries.C (1 / 4 : ℚ) * jacobiSignedCubeSeriesRaw ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [← map_pow]
    norm_num
  rw [hscale, PowerSeries.coeff_C_mul,
    coeff_jacobiSignedCubeSeriesRaw_sq, sum_jacobiCubePairWeight]
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_theta_mul_jacobiWeightedTriangularSeries,
    coeff_jacobiWeightedSquareSeries_mul_bilateral]
  simp only [jacobiReindexedPairWeight]
  rw [← Finset.sum_sub_distrib]
  ring

/-- Differentiating the normalized triangular series only differentiates
its bilateral nonconstant factor. -/
theorem derivative_rationalTriangularThetaSeries :
    PowerSeries.derivative ℚ rationalTriangularThetaSeries =
      PowerSeries.C (1 / 2 : ℚ) *
        PowerSeries.derivative ℚ rationalBilateralTriangularSeries := by
  rw [rationalTriangularThetaSeries,
    (PowerSeries.derivative ℚ).leibniz, PowerSeries.derivative_C]
  simp

/-- Series-side Jacobi cube identity after the parity reindexing.  The only
remaining cube input is the specialized triple-product identity identifying
`jacobiSignedCubeSeries` with Euler's cubed product. -/
theorem jacobiSignedCubeSeries_sq_eq_theta_wronskian :
    jacobiSignedCubeSeries ^ 2 =
      rationalIntegerThetaSeries * rationalTriangularThetaSeries +
        PowerSeries.C 4 * PowerSeries.X *
          (rationalIntegerThetaSeries *
              PowerSeries.derivative ℚ rationalTriangularThetaSeries -
            PowerSeries.derivative ℚ rationalIntegerThetaSeries *
              rationalTriangularThetaSeries) := by
  rw [jacobiSignedCubeSeries_sq_eq_weighted_reindex,
    jacobiWeightedTriangularSeries_eq_derivative,
    jacobiWeightedSquareSeries_eq_derivative,
    derivative_rationalTriangularThetaSeries,
    rationalTriangularThetaSeries]
  ring


end QEC.Coding.TannerLiftedProduct

import QEC.Coding.HighDimensionalExpander.CartwrightSteger.CyclicAlgebra.LaurentEvaluation

/-!
# Residue-class Laurent coordinates of the skew ring

An exponent `n` is written uniquely as `d q + k`, with `0 ≤ k < d`.
For every constant-basis index and residue `k`, the corresponding skew
coefficients form a Laurent polynomial in the central variable `z^d`.
-/

namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger

noncomputable def skewExponentResidue
    (r : Rank) (n : ℤ) : Fin r.matrixRank := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  exact ⟨(n % (r.matrixRank : ℤ)).toNat,
    (Int.toNat_lt_of_ne_zero (ne_of_gt hdNat)).2
      (Int.emod_lt_of_pos n hd)⟩

noncomputable def skewExponentQuotient
    (r : Rank) (n : ℤ) : ℤ := n / (r.matrixRank : ℤ)

@[simp] theorem skewExponentResidue_val
    (r : Rank) (n : ℤ) :
    ((skewExponentResidue r n : Fin r.matrixRank) : ℕ) =
      (n % (r.matrixRank : ℤ)).toNat := rfl

theorem skewExponent_decomposition
    (r : Rank) (n : ℤ) :
    n = (r.matrixRank : ℤ) * skewExponentQuotient r n +
      (skewExponentResidue r n : ℕ) := by
  have hdNat : 0 < r.matrixRank :=
    lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)
  have hd : (0 : ℤ) < (r.matrixRank : ℤ) := by exact_mod_cast hdNat
  have hnonneg := Int.emod_nonneg n (ne_of_gt hd)
  have hcast : (((n % (r.matrixRank : ℤ)).toNat : ℕ) : ℤ) =
      n % (r.matrixRank : ℤ) := Int.toNat_of_nonneg hnonneg
  rw [skewExponentQuotient, skewExponentResidue_val, hcast]
  have h := Int.emod_add_mul_ediv n (r.matrixRank : ℤ)
  omega

theorem skewExponent_eq_of_residue_eq_of_quotient_eq
    (r : Rank) {m n : ℤ}
    (hres : skewExponentResidue r m = skewExponentResidue r n)
    (hquot : skewExponentQuotient r m = skewExponentQuotient r n) :
    m = n := by
  rw [skewExponent_decomposition r m,
    skewExponent_decomposition r n, hquot, hres]

noncomputable def skewLaurentCyclicLaurentCoordinate
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    LaurentPolynomial (BaseField P) :=
  f.sum fun n c =>
    if skewExponentResidue r n.toAdd = p.2 then
      LaurentPolynomial.C ((constantBasis P r).repr c p.1) *
      LaurentPolynomial.T (skewExponentQuotient r n.toAdd)
    else 0

@[simp] theorem skewLaurentCyclicLaurentCoordinate_zero
    (P : BasePrime) (r : Rank)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentCyclicLaurentCoordinate P r 0 p = 0 := by
  simp [skewLaurentCyclicLaurentCoordinate]

theorem skewLaurentCyclicLaurentCoordinate_single
    (P : BasePrime) (r : Rank)
    (m : Multiplicative ℤ) (c : ConstantExtension P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentCyclicLaurentCoordinate P r
        (SkewMonoidAlgebra.single m c) p =
      if skewExponentResidue r m.toAdd = p.2 then
        LaurentPolynomial.C ((constantBasis P r).repr c p.1) *
          LaurentPolynomial.T (skewExponentQuotient r m.toAdd)
      else 0 := by
  rw [skewLaurentCyclicLaurentCoordinate,
    SkewMonoidAlgebra.sum_single_index]
  by_cases h : skewExponentResidue r m.toAdd = p.2 <;> simp [h]

@[simp] theorem skewLaurentCyclicLaurentCoordinate_add
    (P : BasePrime) (r : Rank)
    (f g : CartwrightStegerSkewLaurentRing P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    skewLaurentCyclicLaurentCoordinate P r (f + g) p =
      skewLaurentCyclicLaurentCoordinate P r f p +
        skewLaurentCyclicLaurentCoordinate P r g p := by
  unfold skewLaurentCyclicLaurentCoordinate
  apply SkewMonoidAlgebra.sum_add_index'
  · intro n
    by_cases h : skewExponentResidue r n.toAdd = p.2 <;> simp [h]
  · intro n a b
    by_cases h : skewExponentResidue r n.toAdd = p.2
    · simp [h, add_mul]
    · simp [h]

theorem skewLaurentCyclicLaurentCoordinate_apply_quotient
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (i : Fin r.matrixRank) (n : ℤ) :
    (skewLaurentCyclicLaurentCoordinate P r f
        (i, skewExponentResidue r n)).coeff (skewExponentQuotient r n) =
      (constantBasis P r).repr
        (f.coeff (Multiplicative.ofAdd n)) i := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero =>
      rw [skewLaurentCyclicLaurentCoordinate_zero,
        SkewMonoidAlgebra.coeff_zero]
      simp only [AddMonoidAlgebra.coeff_zero, map_zero, Finsupp.zero_apply]
  | add f g hf hg =>
      simp [hf, hg, SkewMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add]
  | single m c =>
      by_cases hm : m = Multiplicative.ofAdd n
      · subst m
        rw [skewLaurentCyclicLaurentCoordinate_single]
        simp [
          ← LaurentPolynomial.single_eq_C_mul_T,
          SkewMonoidAlgebra.coeff_single_apply, AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply]
      · have hmInt : m.toAdd ≠ n := by
          intro h
          apply hm
          apply Multiplicative.toAdd.injective
          simpa using h
        have hpair :
            skewExponentResidue r m.toAdd ≠ skewExponentResidue r n ∨
              skewExponentQuotient r m.toAdd ≠ skewExponentQuotient r n := by
          by_contra h
          push Not at h
          exact hmInt (skewExponent_eq_of_residue_eq_of_quotient_eq
            r h.1 h.2)
        rcases hpair with hres | hquot
        · rw [skewLaurentCyclicLaurentCoordinate_single]
          simp [hres, SkewMonoidAlgebra.coeff_single_apply,
            hm, AddMonoidAlgebra.coeff_zero]
        · have hresCases := eq_or_ne
            (skewExponentResidue r m.toAdd) (skewExponentResidue r n)
          rcases hresCases with hres | hres
          · rw [skewLaurentCyclicLaurentCoordinate_single]
            simp [hm, hres,
              ← LaurentPolynomial.single_eq_C_mul_T, hquot,
              SkewMonoidAlgebra.coeff_single_apply, AddMonoidAlgebra.coeff_single,
              Finsupp.single_apply]
          · rw [skewLaurentCyclicLaurentCoordinate_single]
            simp [hres, SkewMonoidAlgebra.coeff_single_apply,
              hm, AddMonoidAlgebra.coeff_zero]

theorem skewLaurent_eq_zero_of_cyclicLaurentCoordinates_eq_zero
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r)
    (hzero : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      skewLaurentCyclicLaurentCoordinate P r f p = 0) :
    f = 0 := by
  apply SkewMonoidAlgebra.ext
  intro n
  apply (constantBasis P r).repr.injective
  ext i
  rw [SkewMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]
  have hn : Multiplicative.ofAdd n.toAdd = n := rfl
  rw [← hn]
  rw [← skewLaurentCyclicLaurentCoordinate_apply_quotient
    P r f i n.toAdd]
  rw [hzero]
  exact Finsupp.zero_apply

end QEC.Coding.HighDimensionalExpander.CartwrightSteger

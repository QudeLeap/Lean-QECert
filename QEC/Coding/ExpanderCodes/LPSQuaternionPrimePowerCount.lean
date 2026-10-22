import QEC.Coding.ExpanderCodes.JacobiFourSquareCount
import QEC.Coding.ExpanderCodes.LPSReducedWords

/-!
# Prime-power counts for the LPS quaternion factorization

The uniqueness part of the classical LPS quaternion factorization is a
counting argument.  Jacobi's four-square identity counts all integral
quaternions of norm `p^k`; the possible reduced-word normal forms have the
same cardinality.  This file proves both finite counts exactly, leaving the
factorization existence map as the remaining algebraic input.
-/

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- Powers of an integer congruent to one modulo four stay congruent to one
modulo four. -/
theorem lps_prime_pow_mod_four
    (hp4 : p % 4 = 1) (k : ℕ) : p ^ k % 4 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.mul_mod, hp4, ih]

private theorem four_not_dvd_prime_pow
    (hp4 : p % 4 = 1) (k : ℕ) : ¬ 4 ∣ p ^ k := by
  intro h
  have hzero := Nat.dvd_iff_mod_eq_zero.mp h
  rw [lps_prime_pow_mod_four hp4 k] at hzero
  omega

/-- Jacobi's divisor sum at `p^k` is the geometric sum
`8 (1 + p + ... + p^k)` when `p = 1 mod 4`. -/
theorem coeff_jacobiFourSquareSeries_prime_pow
    (hp : p.Prime) (hp4 : p % 4 = 1) (k : ℕ) :
    PowerSeries.coeff (p ^ k) jacobiFourSquareSeries =
      8 * ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [jacobiFourSquareSeries, PowerSeries.coeff_mk,
    if_neg (pow_ne_zero k hp.ne_zero), Nat.divisors_prime_pow hp]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  simp_rw [if_neg (four_not_dvd_prime_pow hp4 _)]

/-- Exact four-square count at every prime power used in the LPS
factorization argument. -/
theorem card_lpsQuaternionFullShell_eq_prime_pow
    (hp : p.Prime) (hp4 : p % 4 = 1) (k : ℕ) :
    (lpsQuaternionFullShell (p ^ k)).card =
      8 * ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [← coeff_integerThetaSeries_pow_four_eq_fullShell_card
      (pow_pos hp.pos k),
    integerThetaSeries_pow_four_eq_jacobiFourSquareSeries]
  exact coeff_jacobiFourSquareSeries_prime_pow hp hp4 k

/-- Total number of reduced words in the alternating spheres
`S_n + S_{n-2} + ...`.  This is the unrestricted analogue of
`lpsAlternatingClosedReducedWordCount`. -/
noncomputable def lpsAlternatingReducedWordCount
    (hp : 0 < p) : ℕ → ℕ
  | 0 => (lpsReducedWords hp 0).card
  | 1 => (lpsReducedWords hp 1).card
  | n + 2 => (lpsReducedWords hp (n + 2)).card +
      lpsAlternatingReducedWordCount hp n

/-- The alternating reduced spheres have the geometric-sum cardinality
`1 + p + ... + p^n`. -/
theorem lpsAlternatingReducedWordCount_eq_geomSum
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    lpsAlternatingReducedWordCount hp.pos n =
      ∑ i ∈ Finset.range (n + 1), p ^ i := by
  induction n using Nat.twoStepInduction with
  | zero => simp [lpsAlternatingReducedWordCount]
  | one =>
      simp [lpsAlternatingReducedWordCount,
        card_lpsReducedWords_one hp hp4, Finset.sum_range_succ,
        Nat.add_comm]
  | more n hn _hnOne =>
      rw [lpsAlternatingReducedWordCount,
        card_lpsReducedWords_add_one hp hp4 (n + 1), hn]
      simp only [Nat.add_assoc, Nat.reduceAdd, Finset.sum_range_succ]
      rw [pow_succ]
      ring

/-- The full norm-`p^n` quaternion shell has exactly eight times as many
elements as the alternating reduced spheres.  This is the finite cardinality
identity used to turn existence of the LPS normal form into uniqueness. -/
theorem card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsQuaternionFullShell (p ^ n)).card =
      8 * lpsAlternatingReducedWordCount hp.pos n := by
  rw [card_lpsQuaternionFullShell_eq_prime_pow hp hp4,
    lpsAlternatingReducedWordCount_eq_geomSum hp hp4]

/-- The normalized positive-first-coordinate shell at norm `p^n` has the
same size as the alternating reduced spheres. -/
theorem card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsQuaternionShell (p ^ n)).card =
      lpsAlternatingReducedWordCount hp.pos n := by
  have hmod : p ^ n % 4 = 1 := lps_prime_pow_mod_four hp4 n
  have hfull :=
    card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
      hp hp4 n
  have hnormalize := card_lpsQuaternionFullShell_eq_eight_mul
    (pow_pos hp.pos n) hmod
  omega

end QEC.Coding.TannerLiftedProduct

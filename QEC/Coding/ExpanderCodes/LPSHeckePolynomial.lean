import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson

/-!
# The LPS Hecke polynomial recurrence

The trace argument in the LPS Ramanujan proof uses the polynomials
`H₀ = 1`, `H₁ = X`, and `Hₙ₊₂ = X Hₙ₊₁ - p Hₙ`.  These are the Dickson
polynomials of the second kind with parameter `p`.  This file records the
recurrence and its scaled Chebyshev evaluation, including the sine identity
used in the spectral-moment calculation.
-/

namespace QEC.Coding.TannerLiftedProduct

open Polynomial

/-- The polynomial `Hₙ` used by the norm-`p` LPS Hecke correspondence. -/
noncomputable def lpsHeckePolynomial
    (R : Type*) [CommRing R] (p : R) (n : ℕ) : R[X] :=
  Polynomial.dickson 2 p n

@[simp] theorem lpsHeckePolynomial_zero
    (R : Type*) [CommRing R] (p : R) :
    lpsHeckePolynomial R p 0 = 1 := by
  rw [lpsHeckePolynomial, Polynomial.dickson_zero]
  norm_num

@[simp] theorem lpsHeckePolynomial_one
    (R : Type*) [CommRing R] (p : R) :
    lpsHeckePolynomial R p 1 = X := by
  simp [lpsHeckePolynomial]

/-- The exact recurrence stated in the LPS trace proof. -/
theorem lpsHeckePolynomial_add_two
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    lpsHeckePolynomial R p (n + 2) =
      X * lpsHeckePolynomial R p (n + 1) -
        C p * lpsHeckePolynomial R p n := by
  exact Polynomial.dickson_add_two 2 p n

@[simp] theorem lpsHeckePolynomial_eval_zero
    (R : Type*) [CommRing R] (p x : R) :
    (lpsHeckePolynomial R p 0).eval x = 1 := by
  simp

@[simp] theorem lpsHeckePolynomial_eval_one
    (R : Type*) [CommRing R] (p x : R) :
    (lpsHeckePolynomial R p 1).eval x = x := by
  simp

/-- Scalar evaluation satisfies the same Hecke recurrence. -/
theorem lpsHeckePolynomial_eval_add_two
    (R : Type*) [CommRing R] (p x : R) (n : ℕ) :
    (lpsHeckePolynomial R p (n + 2)).eval x =
      x * (lpsHeckePolynomial R p (n + 1)).eval x -
        p * (lpsHeckePolynomial R p n).eval x := by
  rw [lpsHeckePolynomial_add_two]
  simp

/-- The constant terms of the even and odd LPS Hecke polynomials.  This is
the elementary correction term which appears when the constant graph mode
is removed from the exact LPS trace formula. -/
theorem lpsHeckePolynomial_eval_zero_even_odd
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n)).eval 0 = (-p) ^ n ∧
      (lpsHeckePolynomial R p (2 * n + 1)).eval 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · rw [show 2 * (n + 1) = 2 * n + 2 by omega,
          lpsHeckePolynomial_eval_add_two, ih.1]
        simp only [zero_mul, zero_sub, pow_succ]
        ring
      · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
          lpsHeckePolynomial_eval_add_two, ih.2]
        simp

@[simp] theorem lpsHeckePolynomial_eval_zero_even
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n)).eval 0 = (-p) ^ n :=
  (lpsHeckePolynomial_eval_zero_even_odd R p n).1

@[simp] theorem lpsHeckePolynomial_eval_zero_odd
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n + 1)).eval 0 = 0 :=
  (lpsHeckePolynomial_eval_zero_even_odd R p n).2

/-- At the trivial adjacency eigenvalue `p + 1`, the `n`-th LPS Hecke
polynomial is the geometric sum `1 + p + ... + p^n`. -/
theorem lpsHeckePolynomial_eval_add_one_eq_geomSum
    (R : Type*) [CommRing R] (p : R) : ∀ n : ℕ,
    (lpsHeckePolynomial R p n).eval (p + 1) =
      ∑ i ∈ Finset.range (n + 1), p ^ i
  | 0 => by simp
  | 1 => by simp [Finset.sum_range_succ, add_comm]
  | n + 2 => by
      rw [lpsHeckePolynomial_eval_add_two,
        lpsHeckePolynomial_eval_add_one_eq_geomSum R p (n + 1),
        lpsHeckePolynomial_eval_add_one_eq_geomSum R p n]
      simp only [Finset.sum_range_succ]
      rw [pow_succ]
      ring

/-- Evaluating a polynomial at an element which kills `e` on the right and
then multiplying by `e` retains only the constant coefficient. -/
theorem polynomial_eval₂_mul_eq_eval_zero_smul
    {A : Type*} [Ring A] [Algebra ℂ A]
    (P : ℂ[X]) (x e : A) (hxe : x * e = 0) :
    P.eval₂ (algebraMap ℂ A) x * e = P.eval 0 • e := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.eval₂_add, Polynomial.eval_add, add_mul,
        hP, hQ, add_smul]
  | monomial n a =>
      cases n with
      | zero => simp [Algebra.smul_def]
      | succ n =>
          simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial,
            pow_succ, mul_assoc, hxe]

/-- Left-handed form of `polynomial_eval₂_mul_eq_eval_zero_smul`. -/
theorem mul_polynomial_eval₂_eq_eval_zero_smul
    {A : Type*} [Ring A] [Algebra ℂ A]
    (P : ℂ[X]) (x e : A) (hex : e * x = 0) :
    e * P.eval₂ (algebraMap ℂ A) x = P.eval 0 • e := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.eval₂_add, Polynomial.eval_add, mul_add,
        hP, hQ, add_smul]
  | monomial n a =>
      cases n with
      | zero => simp [Algebra.smul_def, Algebra.commutes]
      | succ n =>
          simp only [Polynomial.eval₂_monomial,
            Polynomial.eval_monomial]
          calc
            e * ((algebraMap ℂ A) a * x ^ (n + 1)) =
                (algebraMap ℂ A) a * ((e * x) * x ^ n) := by
              rw [pow_succ', ← mul_assoc,
                ← Algebra.commutes a e]
              simp [mul_assoc]
            _ = 0 := by rw [hex]; simp
            _ = (a * 0 ^ (n + 1)) • e := by simp

/-- Adding a scalar multiple of an orthogonal idempotent changes a Hecke
polynomial only by the difference of its scalar evaluations on that
idempotent.  This is the algebraic mechanism for removing the constant
eigenmode of a regular graph. -/
theorem lpsHeckePolynomial_eval₂_add_smul_idempotent
    {A : Type*} [Ring A] [Algebra ℂ A]
    (p d : ℂ) (x e : A)
    (hxe : x * e = 0) (hex : e * x = 0) (hee : e * e = e) : ∀ n : ℕ,
    (lpsHeckePolynomial ℂ p n).eval₂ (algebraMap ℂ A) (x + d • e) =
      (lpsHeckePolynomial ℂ p n).eval₂ (algebraMap ℂ A) x +
        ((lpsHeckePolynomial ℂ p n).eval d -
          (lpsHeckePolynomial ℂ p n).eval 0) • e
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [lpsHeckePolynomial_add_two]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul',
        Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [
        lpsHeckePolynomial_eval₂_add_smul_idempotent p d x e hxe hex hee (n + 1),
        lpsHeckePolynomial_eval₂_add_smul_idempotent p d x e hxe hex hee n]
      simp [mul_add, add_mul, hxe, hex, hee, sub_mul,
        mul_polynomial_eval₂_eq_eval_zero_smul,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      simp only [← Algebra.smul_def]
      module

/-- After the substitution `x ↦ 2 √p x`, the LPS Hecke polynomials are
scaled Chebyshev polynomials of the second kind. -/
theorem lpsHeckePolynomial_eval_two_mul_sqrt_mul
    {p : ℝ} (hp : 0 ≤ p) (x : ℝ) : ∀ n : ℕ,
    (lpsHeckePolynomial ℝ p n).eval (2 * Real.sqrt p * x) =
      Real.sqrt p ^ n *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x
  | 0 => by simp
  | 1 => by
      simp
      ring
  | n + 2 => by
      rw [lpsHeckePolynomial_eval_add_two,
        lpsHeckePolynomial_eval_two_mul_sqrt_mul hp x (n + 1),
        lpsHeckePolynomial_eval_two_mul_sqrt_mul hp x n]
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]
      ring_nf
      rw [Real.sq_sqrt hp]
      norm_num
      ring_nf
      simp

/-- Trigonometric form of the scaled Hecke evaluation.  This is the exact
finite-dimensional spectral expression used in the LPS trace comparison. -/
theorem lpsHeckePolynomial_eval_cos_mul_sin
    {p : ℝ} (hp : 0 ≤ p) (theta : ℝ) (n : ℕ) :
    (lpsHeckePolynomial ℝ p n).eval
          (2 * Real.sqrt p * Real.cos theta) * Real.sin theta =
      Real.sqrt p ^ n * Real.sin (((n : ℝ) + 1) * theta) := by
  rw [lpsHeckePolynomial_eval_two_mul_sqrt_mul hp]
  calc
    Real.sqrt p ^ n *
          (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos theta) *
        Real.sin theta =
        Real.sqrt p ^ n *
          ((Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos theta) *
            Real.sin theta) := by ring
    _ = Real.sqrt p ^ n * Real.sin (((n : ℝ) + 1) * theta) := by
      rw [Polynomial.Chebyshev.U_real_cos]
      norm_num

/-- Every even Chebyshev polynomial of the first kind is bounded below by
`-1` on the whole real line.  Inside `[-1,1]` this is the usual Chebyshev
bound; outside it follows from the hyperbolic branch and even parity. -/
theorem neg_one_le_chebyshevT_even (x : ℝ) (n : ℕ) :
    -1 ≤ (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ))).eval x := by
  by_cases hx : |x| ≤ 1
  · exact neg_le_of_abs_le
      (Polynomial.Chebyshev.abs_eval_T_real_le_one
        (2 * (n : ℤ)) hx)
  · have hAbs : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    by_cases hx0 : 0 ≤ x
    · have hOne : 1 ≤ x := by simpa [abs_of_nonneg hx0] using hAbs
      exact (by norm_num : (-1 : ℝ) ≤ 1).trans
        (Polynomial.Chebyshev.one_le_eval_T_real
          (2 * (n : ℤ)) hOne)
    · have hOne : 1 ≤ -x := by
        rw [← abs_of_nonpos (le_of_not_ge hx0)]
        exact hAbs
      rw [← neg_neg x, Polynomial.Chebyshev.T_eval_neg]
      rw [Int.negOnePow_even _ (even_two_mul (n : ℤ))]
      simpa using ((by norm_num : (-1 : ℝ) ≤ 1).trans
        (Polynomial.Chebyshev.one_le_eval_T_real
          (2 * (n : ℤ)) hOne))

/-- Uniform lower bound for even Chebyshev polynomials of the second kind.
This is the cancellation-control estimate needed by the finite trace method. -/
theorem neg_odd_le_chebyshevU_even (x : ℝ) : ∀ n : ℕ,
    -((2 * n + 1 : ℕ) : ℝ) ≤
      (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x
  | 0 => by simp
  | n + 1 => by
      rw [show (2 * ((n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_eq_two_mul_T_add_U]
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      have hT : -1 ≤
          (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 2)).eval x := by
        rw [show 2 * (n : ℤ) + 2 = 2 * ((n + 1 : ℕ) : ℤ) by omega]
        exact neg_one_le_chebyshevT_even x (n + 1)
      have hU : -((2 * n + 1 : ℕ) : ℝ) ≤
          (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x :=
        neg_odd_le_chebyshevU_even x n
      calc
        -((2 * (n + 1) + 1 : ℕ) : ℝ) =
            -2 + -((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 2 *
              (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 2)).eval x +
            (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x :=
          add_le_add (by linarith) hU

/-- Scaled cancellation-control bound for the even LPS Hecke polynomials. -/
theorem lpsHeckePolynomial_eval_even_scaled_lower_bound
    {p : ℝ} (hp : 0 ≤ p) (x : ℝ) (n : ℕ) :
    -((2 * n + 1 : ℕ) : ℝ) * Real.sqrt p ^ (2 * n) ≤
      (lpsHeckePolynomial ℝ p (2 * n)).eval
        (2 * Real.sqrt p * x) := by
  rw [lpsHeckePolynomial_eval_two_mul_sqrt_mul hp]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left (neg_odd_le_chebyshevU_even x n)
      (pow_nonneg (Real.sqrt_nonneg p) (2 * n)))

/-- Coordinate-free version of the even Hecke lower bound.  For positive
`p`, every real evaluation is at least `-(2n+1)pⁿ`. -/
theorem lpsHeckePolynomial_eval_even_lower_bound
    {p : ℝ} (hp : 0 < p) (x : ℝ) (n : ℕ) :
    -((2 * n + 1 : ℕ) : ℝ) * p ^ n ≤
      (lpsHeckePolynomial ℝ p (2 * n)).eval x := by
  have hsqrt : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hscaled := lpsHeckePolynomial_eval_even_scaled_lower_bound
    hp.le (x / (2 * Real.sqrt p)) n
  rw [show 2 * Real.sqrt p * (x / (2 * Real.sqrt p)) = x by
    field_simp] at hscaled
  rw [pow_mul, Real.sq_sqrt hp.le] at hscaled
  exact hscaled

/-- On the Ramanujan interval, the even Chebyshev polynomial has its
standard linear bound. -/
theorem abs_chebyshevU_even_le_odd
    (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x| ≤
      ((2 * n + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (((n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) + 2 by omega,
      Polynomial.Chebyshev.U_eq_two_mul_T_add_U]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat]
    have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one
      (2 * (n : ℤ) + 2) hx
    calc
      |2 * (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 2)).eval x +
          (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x| ≤
          |2 * (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 2)).eval x| +
            |(Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x| := abs_add_le _ _
      _ ≤ 2 + ((2 * n + 1 : ℕ) : ℝ) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith
      _ = ((2 * (n + 1) + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The spectral Ramanujan bound gives the optimal even Hecke evaluation
bound, with no asymptotic loss. -/
theorem abs_lpsHeckePolynomial_eval_even_le_of_ramanujan
    {p : ℝ} (hp : 0 < p) (x : ℝ)
    (hx : |x| ≤ 2 * Real.sqrt p) (n : ℕ) :
    |(lpsHeckePolynomial ℝ p (2 * n)).eval x| ≤
      ((2 * n + 1 : ℕ) : ℝ) * p ^ n := by
  let r := Real.sqrt p
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hx' : |x / (2 * r)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * r)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).2
    simpa [r] using hx
  have hRewrite : 2 * r * (x / (2 * r)) = x := by field_simp
  rw [← hRewrite, lpsHeckePolynomial_eval_two_mul_sqrt_mul hp.le,
    abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
  have hU := abs_chebyshevU_even_le_odd (x / (2 * r)) hx' n
  calc
    r ^ (2 * n) *
        |(Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval (x / (2 * r))| ≤
        r ^ (2 * n) * ((2 * n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hU (pow_nonneg hr.le _)
    _ = ((2 * n + 1 : ℕ) : ℝ) * p ^ n := by
      rw [pow_mul, Real.sq_sqrt hp.le]
      ring

/-- On `[1,∞)`, consecutive Chebyshev `U` values are nonnegative and grow
by at least a factor of the evaluation point. -/
theorem chebyshevU_nonnegative_and_mul_le_succ
    {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ,
    0 ≤ (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ∧
      x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
        (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x
  | 0 => by simp; linarith
  | n + 1 => by
      obtain ⟨hn0, hnstep⟩ := chebyshevU_nonnegative_and_mul_le_succ hx n
      have hnext0 : 0 ≤
          (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x :=
        (mul_nonneg (by linarith) hn0).trans hnstep
      constructor
      · exact hnext0
      · rw [show (((n + 1) + 1 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
          Polynomial.Chebyshev.U_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X]
        norm_num only [Nat.cast_add, Nat.cast_one] at hnstep hnext0 ⊢
        have hxx :
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
              x * (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
          have hmono :
              (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
                (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
            calc
              (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
                  x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x := by
                nlinarith
              _ ≤ _ := hnstep
          calc
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
                (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := hmono
            _ ≤ x *
                (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
              nlinarith
        nlinarith [hxx]

/-- On `[1,∞)`, `Uₙ(x)` dominates the elementary power `xⁿ`. -/
theorem pow_le_chebyshevU_of_one_le
    {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ,
    x ^ n ≤ (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ]
      calc
        x ^ n * x ≤
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x * x := by
          gcongr
          exact pow_le_chebyshevU_of_one_le hx n
        _ = x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x := mul_comm _ _
        _ ≤ _ := (chebyshevU_nonnegative_and_mul_le_succ hx n).2

/-- Outside `[-1,1]`, an even Chebyshev `U` value dominates the
corresponding even power of the absolute value. -/
theorem abs_pow_even_le_chebyshevU_even
    (x : ℝ) (n : ℕ) (hx : 1 ≤ |x|) :
    |x| ^ (2 * n) ≤
      (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x := by
  have h := pow_le_chebyshevU_of_one_le hx (2 * n)
  by_cases hx0 : 0 ≤ x
  · simpa [abs_of_nonneg hx0] using h
  · rw [show 2 * (n : ℤ) = ((2 * n : ℕ) : ℤ) by omega]
    conv_rhs =>
      rw [← neg_neg x, Polynomial.Chebyshev.U_eval_neg]
    rw [Int.negOnePow_even _ ⟨(n : ℤ), by push_cast; ring⟩]
    simpa [abs_of_nonpos (le_of_not_ge hx0)] using h

end QEC.Coding.TannerLiftedProduct

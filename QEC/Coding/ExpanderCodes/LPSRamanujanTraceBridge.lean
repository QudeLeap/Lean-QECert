import QEC.Coding.ExpanderCodes.LPSExactTraceFormula
import QEC.Coding.ExpanderCodes.LPSSpectralTrace

/-!
# LPS exact trace to real spectral sums

This file joins the arithmetic exact trace formula to the finite-dimensional
self-adjoint spectrum.  It also transports the real LPS Hecke polynomial
through the complex functional calculus, so subsequent growth estimates can
be stated entirely in terms of real eigenvalues.
-/

open Polynomial
open scoped MatrixGroups
open Filter Asymptotics

namespace QEC.Coding.TannerLiftedProduct

variable {p : ℕ}

/-- If every term in a finite real sum is at least `-B`, no individual
term can exceed the total by more than the worst possible contribution of
the remaining terms. -/
theorem term_le_sum_add_card_sub_one_mul_of_lower_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (B : ℝ) (i : I)
    (hLower : ∀ j, -B ≤ f j) :
    f i ≤ ∑ j, f j + ((Fintype.card I - 1 : ℕ) : ℝ) * B := by
  have hRest : ∑ _j ∈ Finset.univ.erase i, -B ≤
      ∑ j ∈ Finset.univ.erase i, f j := by
    exact Finset.sum_le_sum fun j _hj => hLower j
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    nsmul_eq_mul, Finset.card_univ] at hRest
  have hSplit : ∑ j, f j = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    calc
      ∑ j, f j = ∑ j ∈ Finset.univ.erase i, f j + f i :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
      _ = _ := add_comm _ _
  rw [hSplit]
  linarith

/-- Analytic Chebyshev endgame at any radius at least one. -/
theorem abs_le_of_chebyshevU_even_isBigO
    (x r : ℝ) (hr : 1 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ r := by
  by_contra hx
  have hxOne : 1 ≤ |x| := hr.trans (le_of_lt (lt_of_not_ge hx))
  have hPowers : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n) := by
    intro s hs
    have hTerm : (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ =>
          (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x := by
      apply isBigO_of_le atTop
      intro n
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg x) _)]
      exact (abs_pow_even_le_chebyshevU_even x n hxOne).trans
        (le_abs_self _)
    exact hTerm.trans (h s hs)
  exact hx (abs_le_of_forall_gt_evenPow_isBigO (x := x)
    (r := r) (by linarith) hPowers)

/-- Exponential control of even Chebyshev evaluations above one gives the
sharp interval `[-1,1]`. -/
theorem abs_le_one_of_chebyshevU_even_isBigO
    (x : ℝ)
    (h : ∀ s : ℝ, 1 < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ 1 :=
  abs_le_of_chebyshevU_even_isBigO x 1 (by norm_num) h

/-- Even Hecke growth at every rate above `r√p` bounds the eigenvalue by
`2r√p`, for any `r ≥ 1`. -/
theorem abs_le_two_mul_r_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    {p : ℝ} (hp : 0 < p) (lambda rBound : ℝ) (hrBound : 1 ≤ rBound)
    (h : ∀ t : ℝ, rBound * Real.sqrt p < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ p (2 * n)).eval lambda) =O[atTop]
          fun n : ℕ => t ^ (2 * n)) :
    |lambda| ≤ 2 * rBound * Real.sqrt p := by
  let r := Real.sqrt p
  let x := lambda / (2 * r)
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hr0 : r ≠ 0 := hr.ne'
  have hlambda : 2 * r * x = lambda := by
    dsimp [x]
    field_simp
  have hU : ∀ s : ℝ, rBound < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n) := by
    intro s hs
    have hrs : rBound * r < r * s := by nlinarith
    have hraw := h (r * s) hrs
    have hscaled : (fun n : ℕ =>
        r ^ (2 * n) *
          (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
        fun n : ℕ => (r * s) ^ (2 * n) := by
      apply hraw.congr'
      · filter_upwards [] with n
        rw [← hlambda, lpsHeckePolynomial_eval_two_mul_sqrt_mul hp.le]
        rfl
      · exact EventuallyEq.rfl
    have hdiv := (isBigO_mul_iff_isBigO_div
      (l := atTop)
      (f := fun n : ℕ => r ^ (2 * n))
      (g := fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x)
      (h := fun n : ℕ => (r * s) ^ (2 * n))
      (Eventually.of_forall fun n => pow_ne_zero _ hr0)).mp hscaled
    apply hdiv.congr' EventuallyEq.rfl
    filter_upwards [] with n
    rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hr0)]
  have hx := abs_le_of_chebyshevU_even_isBigO x rBound hrBound hU
  rw [← hlambda, abs_mul, abs_mul, abs_of_pos hr]
  norm_num
  dsimp [r] at hr ⊢
  nlinarith [abs_nonneg x]

/-- Sharp Hecke-growth criterion for the Ramanujan interval. -/
theorem abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    {p : ℝ} (hp : 0 < p) (lambda : ℝ)
    (h : ∀ t : ℝ, Real.sqrt p < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ p (2 * n)).eval lambda) =O[atTop]
          fun n : ℕ => t ^ (2 * n)) :
    |lambda| ≤ 2 * Real.sqrt p := by
  simpa using abs_le_two_mul_r_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    hp lambda 1 (by norm_num) (by simpa using h)

/-- Specialized sharp-growth criterion for one centered LPS adjacency
eigenvalue. -/
theorem abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
    (a : LPSResiduePrime p)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (h : ∀ t : ℝ, Real.sqrt (p : ℝ) < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
        =O[atTop] fun n : ℕ => t ^ (2 * n)) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      2 * Real.sqrt (p : ℝ) :=
  abs_le_two_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    (Nat.cast_pos.mpr a.degreePrime.pos) _ h

/-- A linear factor times `pⁿ` is exponentially bounded at every even-power
rate whose base is strictly larger than `√p`. -/
theorem odd_mul_pow_isBigO_evenPow
    {p t : ℝ} (hp : 0 ≤ p) (ht : Real.sqrt p < t) :
    (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * p ^ n) =O[atTop]
      fun n : ℕ => t ^ (2 * n) := by
  have ht0 : 0 < t := (Real.sqrt_nonneg p).trans_lt ht
  have hpt : |p| < t ^ 2 := by
    rw [abs_of_nonneg hp]
    have hs := mul_self_lt_mul_self (Real.sqrt_nonneg p) ht
    rw [← pow_two, Real.sq_sqrt hp, ← pow_two] at hs
    exact hs
  have hn := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) 1 hpt).isBigO
  have hconst := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) 0 hpt).isBigO
  have hsum := (hn.const_mul_left 2).add hconst
  apply hsum.congr'
  · filter_upwards [] with n
    norm_num
    ring
  · filter_upwards [] with n
    rw [pow_mul]

/-- Real evaluation of an LPS Hecke polynomial is unchanged after extension
of scalars to `ℂ`. -/
theorem re_eval_lpsHeckePolynomial_complex_ofReal
    (x : ℝ) (n : ℕ) :
    Complex.re ((lpsHeckePolynomial ℂ (p : ℂ) n).eval (x : ℂ)) =
      (lpsHeckePolynomial ℝ (p : ℝ) n).eval x := by
  have h : (lpsHeckePolynomial ℂ (p : ℂ) n).eval (x : ℂ) =
      Complex.ofReal ((lpsHeckePolynomial ℝ (p : ℝ) n).eval x) := by
    rw [show lpsHeckePolynomial ℂ (p : ℂ) n =
        (lpsHeckePolynomial ℝ (p : ℝ) n).map Complex.ofRealHom by
      exact (Polynomial.map_dickson
        (k := 2) (a := (p : ℝ)) Complex.ofRealHom n).symm]
    exact Polynomial.eval_map_apply
      (p := lpsHeckePolynomial ℝ (p : ℝ) n) Complex.ofRealHom x
  rw [h, Complex.ofReal_re]

/-- The Euclidean centered LPS Hecke trace is the sum of the Hecke
polynomial over the real centered-adjacency eigenvalues. -/
theorem trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
    (a : LPSResiduePrime p) (n : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n) =
      ∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℂ (p : ℂ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i : ℂ) := by
  unfold lpsCenteredEuclideanHeckeOperator
  exact trace_aeval_eq_sum_eval_eigenvalues _
    (lpsCenteredAdjacencyEuclidean_isSymmetric a) _

/-- Real form of the preceding spectral trace identity. -/
theorem re_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues
    (a : LPSResiduePrime p) (n : ℕ) :
    Complex.re (LinearMap.trace ℂ
        (EuclideanSpace ℂ PSL(2, ZMod a.q))
        (lpsCenteredEuclideanHeckeOperator a n)) =
      ∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) := by
  rw [trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact re_eval_lpsHeckePolynomial_complex_ofReal _ _

/-- Exact real spectral-sum form of the centered LPS theta trace formula. -/
theorem two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
    (a : LPSResiduePrime p) (n : ℕ) :
    2 * (∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)) =
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ i ∈ Finset.range (n + 1), (p : ℝ) ^ i) -
          (lpsHeckePolynomial ℝ (p : ℝ) n).eval 0) := by
  have h := congrArg Complex.re
    (two_mul_trace_lpsCenteredEuclideanHeckeOperator_eq_theta_sub_trivial
      a n)
  norm_num at h
  rw [re_trace_lpsCenteredEuclideanHeckeOperator_eq_sum_eval_eigenvalues] at h
  have hPow (i : ℕ) : Complex.re ((p : ℂ) ^ i) = (p : ℝ) ^ i := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  simp_rw [hPow] at h
  have hZero := re_eval_lpsHeckePolynomial_complex_ofReal
    (p := p) (0 : ℝ) n
  norm_num at hZero
  rw [hZero] at h
  simpa only [coeff_lpsTraceThetaSeries] using h

/-- The real arithmetic residual obtained after removing the trivial
representation from the exact finite LPS theta trace. -/
noncomputable def lpsCenteredThetaResidual
    (a : LPSResiduePrime p) (n : ℕ) : ℝ :=
  (Fintype.card PSL(2, ZMod a.q) : ℝ) *
      ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
    2 * ((∑ i ∈ Finset.range (n + 1), (p : ℝ) ^ i) -
      (lpsHeckePolynomial ℝ (p : ℝ) n).eval 0)

/-- At even Hecke degree, the centered theta residual is the raw trace-theta
coefficient minus a completely explicit elementary term.  In particular,
the automorphic coefficient problem no longer contains an unevaluated Hecke
polynomial at zero. -/
theorem lpsCenteredThetaResidual_even_eq_theta_sub_explicit
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2 * n) =
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ (2 * n))
            (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
          (-(p : ℝ)) ^ n) := by
  simp [lpsCenteredThetaResidual]

/-- The centered theta residual is exactly twice the real spectral Hecke
sum. -/
theorem lpsCenteredThetaResidual_eq_two_mul_sum_eigenvalues
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a n =
      2 * (∑ i : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) n).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)) := by
  exact (two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
    a n).symm

/-- Cancellation control for one centered LPS eigenvalue: the even Hecke
value is bounded by the exact spectral sum plus the universal Chebyshev
lower-bound budget for all other eigenvalues. -/
theorem lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      (∑ j : Fin (Module.finrank ℂ
          (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl j)) +
        ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by
  have hLower : ∀ j : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))),
      -(((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) ≤
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl j) := by
    intro j
    simpa only [neg_mul] using lpsHeckePolynomial_eval_even_lower_bound
      (Nat.cast_pos.mpr a.degreePrime.pos)
      ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl j) n
  simpa using term_le_sum_add_card_sub_one_mul_of_lower_bound
    (fun j : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))) =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl j))
    (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) i hLower

/-- Fully arithmetic upper bound for one even Hecke value.  After this
theorem, the only family-specific quantity on the right is the explicit
theta coefficient; all possible spectral cancellation has been paid for by
the universal `(2n+1)pⁿ` budget. -/
theorem two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    2 * (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ (2 * n))
            (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ j ∈ Finset.range (2 * n + 1), (p : ℝ) ^ j) -
          (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval 0) +
        2 * ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by
  have hTerm := lpsHeckePolynomial_eigenvalue_le_sum_add_cancellation
    a n i
  have hTrace :=
    two_mul_sum_lpsHeckePolynomial_eigenvalues_eq_theta_sub_trivial
      a (2 * n)
  linarith

/-- Residual shorthand for the preceding one-eigenvalue arithmetic bound. -/
theorem two_mul_lpsHeckePolynomial_eigenvalue_le_residual_add_cancellation
    (a : LPSResiduePrime p) (n : ℕ)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    2 * (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) ≤
      lpsCenteredThetaResidual a (2 * n) +
        2 * ((Module.finrank ℂ
            (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ) : ℝ) *
          (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by
  exact two_mul_lpsHeckePolynomial_eigenvalue_le_theta_add_cancellation
    a n i

/-- The one genuinely automorphic estimate left by the finite trace
reduction: after removing the trivial representation, the even theta-trace
residual has the optimal polynomial-times-`pⁿ` growth. -/
def HasOptimalCenteredThetaCoefficientBound
    (a : LPSResiduePrime p) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    |lpsCenteredThetaResidual a (2 * n)| ≤
      C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n)

/-- A weaker arithmetic input sufficient for the PK22 parameter schedule:
a centered theta residual of size `O((2n+1)(4p)^n)`.  It implies the needed
`4√p` spectral interval, but no converse is claimed. -/
def HasFourSqrtCenteredThetaCoefficientBound
    (a : LPSResiduePrime p) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    |lpsCenteredThetaResidual a (2 * n)| ≤
      C * (((2 * n + 1 : ℕ) : ℝ) * (4 * (p : ℝ)) ^ n)

/-- Fully expanded form of the one remaining automorphic estimate.  This
equivalence prevents the named residual predicate from hiding any spectral
or Hecke-polynomial premise: its left-hand side is exactly the explicit
theta representation number after subtraction of the elementary trivial
term displayed on the right. -/
theorem hasOptimalCenteredThetaCoefficientBound_iff_explicit
    (a : LPSResiduePrime p) :
    HasOptimalCenteredThetaCoefficientBound a ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(Fintype.card PSL(2, ZMod a.q) : ℝ) *
              ((PowerSeries.coeff (p ^ (2 * n))
                (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
            2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
              (-(p : ℝ)) ^ n)| ≤
          C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by
  unfold HasOptimalCenteredThetaCoefficientBound
  constructor <;> rintro ⟨C, hC, hBound⟩ <;>
    refine ⟨C, hC, fun n => ?_⟩
  · simpa [lpsCenteredThetaResidual_even_eq_theta_sub_explicit] using hBound n
  · simpa [lpsCenteredThetaResidual_even_eq_theta_sub_explicit] using hBound n

/-- The relaxed hypothesis is an explicit estimate on the original theta
representation count after elementary trivial-mode subtraction. -/
theorem hasFourSqrtCenteredThetaCoefficientBound_iff_explicit
    (a : LPSResiduePrime p) :
    HasFourSqrtCenteredThetaCoefficientBound a ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(Fintype.card PSL(2, ZMod a.q) : ℝ) *
              ((PowerSeries.coeff (p ^ (2 * n))
                (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
            2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
              (-(p : ℝ)) ^ n)| ≤
          C * (((2 * n + 1 : ℕ) : ℝ) * (4 * (p : ℝ)) ^ n) := by
  unfold HasFourSqrtCenteredThetaCoefficientBound
  constructor <;> rintro ⟨C, hC, hBound⟩ <;>
    refine ⟨C, hC, fun n => ?_⟩
  · simpa [lpsCenteredThetaResidual_even_eq_theta_sub_explicit] using hBound n
  · simpa [lpsCenteredThetaResidual_even_eq_theta_sub_explicit] using hBound n

/-- The optimal centered theta coefficient estimate gives every individual
centered eigenvalue the Hecke growth required by the sharp analytic
endgame. -/
theorem lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
    (a : LPSResiduePrime p) (base : ℝ) (hBase : (p : ℝ) ≤ base)
    (C : ℝ) (hC : 0 ≤ C)
    (hResidual : ∀ n : ℕ,
      |lpsCenteredThetaResidual a (2 * n)| ≤
        C * (((2 * n + 1 : ℕ) : ℝ) * base ^ n))
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (t : ℝ) (ht : Real.sqrt base < t) :
    (fun n : ℕ =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
      =O[atTop] fun n : ℕ => t ^ (2 * n) := by
  have hBase0 : 0 ≤ base := (Nat.cast_nonneg p).trans hBase
  let N : ℝ := (Module.finrank ℂ
    (EuclideanSpace ℂ PSL(2, ZMod a.q)) - 1 : ℕ)
  let K : ℝ := C + 2 * N + 1
  have hN : 0 ≤ N := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hPoint : ∀ n : ℕ,
      |(lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)| ≤
      K * (((2 * n + 1 : ℕ) : ℝ) * base ^ n) := by
    intro n
    let B : ℝ := ((2 * n + 1 : ℕ) : ℝ) * base ^ n
    let Bp : ℝ := ((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n
    let H : ℝ := (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
      ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hBp : 0 ≤ Bp := by dsimp [Bp]; positivity
    have hBpB : Bp ≤ B := by
      dsimp [Bp, B]
      gcongr
    have hLower : -B ≤ H := by
      have hLowerP : -Bp ≤ H := by
        dsimp [Bp, H]
        simpa only [neg_mul] using lpsHeckePolynomial_eval_even_lower_bound
          (Nat.cast_pos.mpr a.degreePrime.pos)
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i) n
      linarith
    have hUpper :=
      two_mul_lpsHeckePolynomial_eigenvalue_le_residual_add_cancellation
        a n i
    change 2 * H ≤ lpsCenteredThetaResidual a (2 * n) + 2 * N * Bp at hUpper
    have hRes := hResidual n
    change |lpsCenteredThetaResidual a (2 * n)| ≤ C * B at hRes
    have hResUpper : lpsCenteredThetaResidual a (2 * n) ≤ C * B :=
      (le_abs_self _).trans hRes
    change |H| ≤ K * B
    rw [abs_le]
    constructor <;> dsimp [K] <;> nlinarith
  have hTerm : (fun n : ℕ =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
      =O[atTop] fun n : ℕ =>
        K * (((2 * n + 1 : ℕ) : ℝ) * base ^ n) := by
    apply isBigO_of_le atTop
    intro n
    rw [Real.norm_eq_abs, Real.norm_of_nonneg
      (mul_nonneg hK (mul_nonneg (by positivity) (pow_nonneg hBase0 _)))]
    exact hPoint n
  exact hTerm.trans ((odd_mul_pow_isBigO_evenPow
    (p := base) (t := t) hBase0 ht).const_mul_left K)

/-- Optimal residual growth gives the sharp-rate Hecke estimate. -/
theorem lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
    (a : LPSResiduePrime p) (C : ℝ) (hC : 0 ≤ C)
    (hResidual : ∀ n : ℕ,
      |lpsCenteredThetaResidual a (2 * n)| ≤
        C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n))
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (t : ℝ) (ht : Real.sqrt (p : ℝ) < t) :
    (fun n : ℕ =>
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
      =O[atTop] fun n : ℕ => t ^ (2 * n) :=
  lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
    a (p : ℝ) le_rfl C hC hResidual i t ht

/-- The relaxed theta coefficient bound controls every centered LPS
eigenvalue at the `4√p` radius required by the PK22 schedule. -/
theorem abs_lpsCenteredEigenvalue_le_four_mul_sqrt_of_theta_bound
    (a : LPSResiduePrime p)
    (hBound : HasFourSqrtCenteredThetaCoefficientBound a)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      4 * Real.sqrt (p : ℝ) := by
  obtain ⟨C, hC, hResidual⟩ := hBound
  have hSqrt : Real.sqrt (4 * (p : ℝ)) =
      2 * Real.sqrt (p : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hGrowth : ∀ t : ℝ, 2 * Real.sqrt (p : ℝ) < t →
      (fun n : ℕ =>
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i))
        =O[atTop] fun n : ℕ => t ^ (2 * n) := by
    intro t ht
    exact lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound_at_base
      a (4 * (p : ℝ))
      (by nlinarith [show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p])
      C hC hResidual i t (by simpa [hSqrt] using ht)
  have h := abs_le_two_mul_r_mul_sqrt_of_lpsHeckePolynomial_even_isBigO
    (Nat.cast_pos.mpr a.degreePrime.pos)
    ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)
    2 (by norm_num) hGrowth
  nlinarith

/-- The optimal centered theta coefficient estimate implies the sharp
Ramanujan bound for every centered LPS adjacency eigenvalue. -/
theorem abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound
    (a : LPSResiduePrime p) (hBound : HasOptimalCenteredThetaCoefficientBound a)
    (i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q)))) :
    |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
      2 * Real.sqrt (p : ℝ) := by
  obtain ⟨C, hC, hResidual⟩ := hBound
  apply abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_evenHecke_isBigO
  intro t ht
  exact lpsHeckePolynomial_eigenvalue_isBigO_of_residual_bound
    a C hC hResidual i t ht

/-- Conversely, the Ramanujan interval bounds the centered theta residual.
The coefficient is just the finite number of centered adjacency eigenvalues. -/
theorem hasOptimalCenteredThetaCoefficientBound_of_ramanujan
    (a : LPSResiduePrime p)
    (hRamanujan : ∀ i : Fin (Module.finrank ℂ
      (EuclideanSpace ℂ PSL(2, ZMod a.q))),
      |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
        2 * Real.sqrt (p : ℝ)) :
    HasOptimalCenteredThetaCoefficientBound a := by
  let N := Module.finrank ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))
  refine ⟨2 * (N : ℝ), by positivity, fun n => ?_⟩
  let B : ℝ := ((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n
  have hTerm : ∀ i : Fin N,
      |(lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)| ≤ B := by
    intro i
    exact abs_lpsHeckePolynomial_eval_even_le_of_ramanujan
      (Nat.cast_pos.mpr a.degreePrime.pos) _ (hRamanujan i) n
  rw [lpsCenteredThetaResidual_eq_two_mul_sum_eigenvalues, abs_mul]
  have hSum : |∑ i : Fin N,
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)| ≤
      (N : ℝ) * B := by
    calc
      |∑ i : Fin N,
        (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
          ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)| ≤
        ∑ i : Fin N,
          |(lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
            ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => hTerm i)
      _ = (N : ℝ) * B := by simp
  rw [show |(2 : ℝ)| = 2 by norm_num]
  change 2 * |∑ i : Fin N,
      (lpsHeckePolynomial ℝ (p : ℝ) (2 * n)).eval
        ((lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i)| ≤
      (2 * (N : ℝ)) * B
  nlinarith [hSum]

/-- The centered theta coefficient estimate is equivalent to the full
Ramanujan eigenvalue bound for this finite LPS graph. -/
theorem hasOptimalCenteredThetaCoefficientBound_iff_ramanujan
    (a : LPSResiduePrime p) :
    HasOptimalCenteredThetaCoefficientBound a ↔
      ∀ i : Fin (Module.finrank ℂ
        (EuclideanSpace ℂ PSL(2, ZMod a.q))),
        |(lpsCenteredAdjacencyEuclidean_isSymmetric a).eigenvalues rfl i| ≤
          2 * Real.sqrt (p : ℝ) := by
  constructor
  · intro h i
    exact abs_lpsCenteredEigenvalue_le_two_mul_sqrt_of_residual_bound a h i
  · exact hasOptimalCenteredThetaCoefficientBound_of_ramanujan a

end QEC.Coding.TannerLiftedProduct

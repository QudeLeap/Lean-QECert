import QEC.Coding.ExpanderCodes.LPSMomentBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Finite spectral trace endgame for LPS

This module supplies the finite-dimensional part of the LPS trace method.
For a self-adjoint operator, the trace of a polynomial is the sum of that
polynomial over the real eigenvalues.  In particular, exponential bounds on
the even-power traces force the sharp pointwise spectral radius bound.
-/

open Filter Asymptotics
open Polynomial

namespace QEC.Coding.TannerLiftedProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Polynomial functional calculus followed by trace is the sum of the
polynomial over the real self-adjoint eigenvalues. -/
theorem trace_aeval_eq_sum_eval_eigenvalues
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (P : ℂ[X]) :
    LinearMap.trace ℂ E (aeval T P) =
      ∑ i : Fin (Module.finrank ℂ E),
        P.eval (hT.eigenvalues rfl i : ℂ) := by
  classical
  rw [LinearMap.trace_eq_sum_inner
    (aeval T P) (hT.eigenvectorBasis rfl)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Module.End.aeval_apply_of_hasEigenvector
    (hT.hasEigenvector_eigenvectorBasis rfl i)]
  rw [inner_smul_right, (hT.eigenvectorBasis rfl).inner_eq_one]
  simp

/-- The real trace of an even power is the nonnegative even spectral
moment. -/
theorem re_trace_even_pow_eq_sum_abs_eigenvalues
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) :
    Complex.re (LinearMap.trace ℂ E (T ^ (2 * n))) =
      ∑ i : Fin (Module.finrank ℂ E),
        |hT.eigenvalues rfl i| ^ (2 * n) := by
  have hTrace := trace_aeval_eq_sum_eval_eigenvalues
    T hT ((Polynomial.X : ℂ[X]) ^ (2 * n))
  simp only [map_pow, aeval_X] at hTrace
  rw [hTrace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [pow_mul, pow_mul, sq_abs]
  norm_cast

/-- The exact finite-dimensional LPS endgame: if every exponential rate
above `r` bounds the even traces, then every eigenvalue lies in `[-r,r]`. -/
theorem abs_eigenvalues_le_of_trace_evenPow_isBigO
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    {r : ℝ} (hr : 0 ≤ r)
    (hTrace : ∀ s : ℝ, r < s →
      (fun n : ℕ =>
        Complex.re (LinearMap.trace ℂ E (T ^ (2 * n)))) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    ∀ i : Fin (Module.finrank ℂ E),
      |hT.eigenvalues rfl i| ≤ r := by
  apply abs_le_of_evenMoment_isBigO
    (eigenvalue := hT.eigenvalues rfl) hr
  intro s hrs
  simpa only [re_trace_even_pow_eq_sum_abs_eigenvalues T hT] using
    hTrace s hrs

end QEC.Coding.TannerLiftedProduct

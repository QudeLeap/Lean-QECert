import QEC.Coding.ExpanderCodes.LPSAnalyticTheta
import QEC.Coding.ExpanderCodes.LPSRamanujanTraceBridge

/-!
# The LPS trace residual in Mathlib's `qExpansion` coordinates

The normalized four-variable theta product has been identified with the
formal representation-counting series.  This module transports the exact
finite LPS trace residual to the coefficient of Mathlib's analytic
`qExpansion`.  The Eisenstein/cusp decomposition and its coefficient bound
are not proved here.
-/

namespace QEC.Coding.TannerLiftedProduct

open scoped UpperHalfPlane MatrixGroups

variable {p : ℕ}

/-- Exact analytic-coefficient form of the centered LPS residual at even
Hecke degree.  The real part is explicit because the theta coefficients
are natural numbers. -/
theorem lpsCenteredThetaResidual_even_eq_qExpansion_sub_explicit
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2 * n) =
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
        (PowerSeries.coeff (p ^ (2 * n))
          (UpperHalfPlane.qExpansion 1
            (fun z : ℍ => lpsStandardTheta a.q z))).re -
        2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
          (-(p : ℝ)) ^ n) := by
  have hCoeff := coeff_qExpansion_lpsStandardTheta
    a.q a.prime.pos (p ^ (2 * n))
  have hRe :
      (PowerSeries.coeff (p ^ (2 * n))
          (UpperHalfPlane.qExpansion 1
            (fun z : ℍ => lpsStandardTheta a.q z))).re =
        ((PowerSeries.coeff (p ^ (2 * n))
          (lpsTraceThetaSeries a.q) : ℕ) : ℝ) := by
    rw [hCoeff]
    simp
  rw [lpsCenteredThetaResidual_even_eq_theta_sub_explicit, hRe]

/-- The precise remaining coefficient estimate, expressed entirely in the
analytic `qExpansion` API.  This equivalence supplies no bound by itself. -/
theorem hasFourSqrtCenteredThetaCoefficientBound_iff_qExpansion
    (a : LPSResiduePrime p) :
    HasFourSqrtCenteredThetaCoefficientBound a ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(Fintype.card PSL(2, ZMod a.q) : ℝ) *
              (PowerSeries.coeff (p ^ (2 * n))
                (UpperHalfPlane.qExpansion 1
                  (fun z : ℍ => lpsStandardTheta a.q z))).re -
            2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
              (-(p : ℝ)) ^ n)| ≤
          C * (((2 * n + 1 : ℕ) : ℝ) * (4 * (p : ℝ)) ^ n) := by
  unfold HasFourSqrtCenteredThetaCoefficientBound
  simp only [lpsCenteredThetaResidual_even_eq_qExpansion_sub_explicit]

end QEC.Coding.TannerLiftedProduct

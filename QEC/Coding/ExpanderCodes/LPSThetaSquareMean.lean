import QEC.Coding.ExpanderCodes.LPSCuspSquareLSeries
import QEC.Coding.ExpanderCodes.LPSThetaCuspidalRemainder

/-!
# LPSThetaSquareMean

Apply the proved Fourier square-mean/Mellin closure to the genuine LPS theta
minus its complete Eisenstein correction. The original PK22 main theorem and
its stronger coefficient-growth obligation remain open.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- The squared norm of each actual coefficient of the fully constructed LPS cuspidal remainder. -/
noncomputable def lpsThetaSquareCoeff (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (n : ℕ) : ℝ :=
  lpsWeightTwoCusp_squareCoeff ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) n

/-- Every genuine LPS square coefficient is the actual representation count minus the complete Eisenstein correction, squared in norm. -/
lemma lpsThetaSquareCoeff_eq_trace_sub_correction (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (n : ℕ) :
    lpsThetaSquareCoeff q hq4 n=
      ‖((PowerSeries.coeff n (lpsTraceThetaSeries q):ℕ):ℂ)-
        lpsThetaEisensteinCorrectionCoefficient q n‖^2 := by
  unfold lpsThetaSquareCoeff lpsWeightTwoCusp_squareCoeff
  rw [coeff_qExpansion_lpsThetaCuspidalRemainder]

/-- The actual LPS remainder has zero constant square coefficient. -/
lemma lpsThetaSquareCoeff_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaSquareCoeff q hq4 0=0 :=
  lpsWeightTwoCusp_squareCoeff_zero _ _

/-- The genuine horizontal square mean of the actual LPS theta remainder. -/
noncomputable def lpsThetaSquareMean (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (y : ℝ) : ℝ :=
  lpsCuspHorocycleSquareMean ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) y

/-- The actual LPS square mean is the integral of the true theta-minus-complete-correction function. -/
lemma lpsThetaSquareMean_eq_integral (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (y : ℝ) (hy : 0<y) :
    lpsThetaSquareMean q hq4 y=
      ∫ x in (0:ℝ)..1, ‖lpsStandardTheta q (lpsHorocyclePoint y hy x)-
        lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4)
          (lpsHorocyclePoint y hy x)‖^2 := by
  unfold lpsThetaSquareMean lpsCuspHorocycleSquareMean
  rw [lpsCuspHorocycle_integral _ _ y hy]
  simp only [lpsThetaCuspidalRemainder_apply]

/-- The actual LPS square mean has the genuine exponentially weighted coefficient-square expansion. -/
lemma lpsThetaSquareMean_hasSum (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)*
      (Real.exp (-(4*Real.pi*(n:ℝ))*y):ℂ)) (lpsThetaSquareMean q hq4 y:ℂ) :=
  lpsCuspHorocycleSquareMean_hasSum _ _ _ hy

/-- The actual LPS coefficient squares satisfy the proved initial quadratic average estimate. -/
lemma lpsThetaSquareCoeff_sum_bound (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range X, lpsThetaSquareCoeff q hq4 n)≤C*(X:ℝ)^2 := by
  have : NeZero ((4*q)^2) := ⟨by have hq := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsWeightTwoCusp_coeff_square_sum_bound _ _

/-- The actual LPS coefficient-square L-series converges absolutely for Re(s) greater than two. -/
lemma lpsThetaSquareLSeries_summable (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)) s := by
  have : NeZero ((4*q)^2) := ⟨by have hq := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsWeightTwoCusp_squareLSeries_summable _ _ _ hs

/-- The genuine LPS square mean has its exact Gamma-over-four-pi Mellin representation. -/
lemma lpsThetaSquareMean_mellin (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (s : ℂ) (hs : 2<s.re) :
    mellin (fun y : ℝ => (lpsThetaSquareMean q hq4 y:ℂ)) s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)) s := by
  have : NeZero ((4*q)^2) := ⟨by have hq := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspHorocycleSquareMean_mellin _ _ _ hs

end QEC.Coding.TannerLiftedProduct

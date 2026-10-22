import QEC.Coding.ExpanderCodes.LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-!
# LPSCuspSquareLSeries

The actual coefficient-square series, its initial convergence half-plane and
its true Abel/Mellin integral identities. No analytic continuation, functional
equation or near-square-root pointwise estimate is claimed here.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

/-- The squared norm of an actual q-expansion coefficient of the genuine weight-two cusp form. -/
noncomputable def lpsWeightTwoCusp_squareCoeff (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) : ℝ :=
  ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2

/-- The genuine coefficient squares are nonnegative. -/
lemma lpsWeightTwoCusp_squareCoeff_nonneg (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) :
    0≤lpsWeightTwoCusp_squareCoeff N f n := sq_nonneg _

/-- The actual cusp form has zero constant square coefficient. -/
lemma lpsWeightTwoCusp_squareCoeff_zero (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsWeightTwoCusp_squareCoeff N f 0=0 := by
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  unfold lpsWeightTwoCusp_squareCoeff
  rw [CuspFormClass.qExpansion_coeff_zero f (by norm_num) hp]
  simp

/-- The proved quadratic square-average bound gives the actual inclusive partial-sum asymptotic bound. -/
lemma lpsWeightTwoCusp_squareCoeff_sum_isBigO (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    (fun X : ℕ => ∑ n ∈ Finset.Icc 1 X, lpsWeightTwoCusp_squareCoeff N f n)
      =O[atTop] (fun X : ℕ => (X:ℝ)^(2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := lpsWeightTwoCusp_coeff_square_sum_bound N f
  refine isBigO_iff.mpr ⟨4*C,?_⟩
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun n hn => lpsWeightTwoCusp_squareCoeff_nonneg N f n)),
    Real.rpow_two,Real.norm_of_nonneg (sq_nonneg _)]
  have hsub : Finset.Icc 1 X⊆Finset.range (X+1) := by
    intro n hn
    exact Finset.mem_range.mpr (by have h := Finset.mem_Icc.mp hn;omega)
  calc
    _ ≤ ∑ n ∈ Finset.range (X+1), lpsWeightTwoCusp_squareCoeff N f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n hn hnot => lpsWeightTwoCusp_squareCoeff_nonneg N f n)
    _ ≤ C*((X+1:ℕ):ℝ)^2 := hb (X+1)
    _ ≤ (4*C)*(X:ℝ)^2 := by
      have hXR : 1≤(X:ℝ) := by exact_mod_cast hX
      push_cast
      have hsq : ((X:ℝ)+1)^2≤4*(X:ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hC]

/-- The genuine coefficient-square Dirichlet series converges absolutely throughout Re(s) greater than two. -/
lemma lpsWeightTwoCusp_squareLSeries_summable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s :=
  LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (lpsWeightTwoCusp_squareCoeff_sum_isBigO N f)
    (lpsWeightTwoCusp_squareCoeff_nonneg N f) (by norm_num) hs

/-- The actual convergent square L-series has its true Abel integral representation. -/
lemma lpsWeightTwoCusp_squareLSeries_eq_abel_integral (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    LSeries (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s=
      s*(∫ t in Set.Ioi (1:ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (lpsWeightTwoCusp_squareCoeff N f n:ℂ))*
          (t:ℂ)^(-(s+1))) :=
  LSeries_eq_mul_integral_of_nonneg (lpsWeightTwoCusp_squareCoeff N f) (by norm_num) hs
    (lpsWeightTwoCusp_squareCoeff_sum_isBigO N f)
    (lpsWeightTwoCusp_squareCoeff_nonneg N f)

/-- The actual square coefficients divided by the real-power weight form a summable series. -/
lemma lpsWeightTwoCusp_squareCoeff_div_rpow_summable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    Summable (fun n : ℕ => lpsWeightTwoCusp_squareCoeff N f n/(n:ℝ)^s.re) := by
  have h := (lpsWeightTwoCusp_squareLSeries_summable N f s hs).norm
  apply h.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · subst n
    simp [lpsWeightTwoCusp_squareCoeff_zero]
  · rw [if_neg hn,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (lpsWeightTwoCusp_squareCoeff_nonneg N f n)]

/-- The actual normalized Haar square mean of the genuine horizontal cusp form. -/
noncomputable def lpsCuspHorocycleSquareMean (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (y : ℝ) : ℝ :=
  ∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle

/-- The actual square mean is the sum of the genuine coefficient squares with exact four-pi exponential damping. -/
lemma lpsCuspHorocycleSquareMean_hasSum (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)*
      (Real.exp (-(4*Real.pi*(n:ℝ))*y):ℂ)) (lpsCuspHorocycleSquareMean N f y:ℂ) := by
  have h := lpsCuspHorocycleCircle_parseval_nat N f y hy
  have he (n : ℕ) : ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n)=
      lpsWeightTwoCusp_squareCoeff N f n*Real.exp (-(4*Real.pi*(n:ℝ))*y) := by
    rw [lpsCuspHorocycle_weight_exp]
    unfold lpsWeightTwoCusp_squareCoeff
    congr 2
    ring
  simp_rw [he] at h
  simpa only [Complex.ofReal_mul,lpsCuspHorocycleSquareMean] using hasSum_ofReal.mpr h

/-- The actual square mean has its normalized Mellin identity with the true convergent coefficient-square L-series. -/
lemma lpsCuspHorocycleSquareMean_mellin (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    mellin (fun y : ℝ => (lpsCuspHorocycleSquareMean N f y:ℂ)) s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s := by
  have hp (n : ℕ) : (lpsWeightTwoCusp_squareCoeff N f n:ℂ)=0 ∨
      0<4*Real.pi*(n:ℝ) := by
    by_cases hn : n=0
    · left
      subst n
      rw [lpsWeightTwoCusp_squareCoeff_zero,Complex.ofReal_zero]
    · right
      have hn' : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      positivity
  have hsum : Summable (fun n : ℕ => ‖(lpsWeightTwoCusp_squareCoeff N f n:ℂ)‖/
      (4*Real.pi*(n:ℝ))^s.re) := by
    have h := (lpsWeightTwoCusp_squareCoeff_div_rpow_summable N f s hs).div_const
      ((4*Real.pi)^s.re)
    apply h.congr
    intro n
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg n),div_mul_eq_div_div,div_right_comm,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (lpsWeightTwoCusp_squareCoeff_nonneg N f n)]
  have h := hasSum_mellin hp (by linarith : 0<s.re)
    (fun y hy => lpsCuspHorocycleSquareMean_hasSum N f y hy) hsum
  have he (n : ℕ) :
      Complex.Gamma s*(lpsWeightTwoCusp_squareCoeff N f n:ℂ)/((4*Real.pi*(n:ℝ):ℝ):ℂ)^s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries.term (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s n := by
    by_cases hn : n=0
    · subst n
      simp [lpsWeightTwoCusp_squareCoeff_zero]
    · rw [LSeries.term_of_ne_zero hn]
      rw [Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity : 0≤4*Real.pi) (Nat.cast_nonneg n)]
      norm_cast
      ring
  simp_rw [he] at h
  exact h.unique ((lpsWeightTwoCusp_squareLSeries_summable N f s hs).hasSum.mul_left _)

end QEC.Coding.TannerLiftedProduct

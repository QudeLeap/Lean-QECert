import QEC.Semantics.Dynamics.Davies.Pinching
import QEC.Semantics.Dynamics.Davies.Stationarity

/-! # A Davies norm bound depending on couplings, not Bohr frequencies -/

namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators ComplexOrder
noncomputable section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weighted adjoint-square sum for one physical coupling. -/
def rateSquareSum (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (rate : Frequency e → ℝ) : Operator V :=
  ∑ w : Frequency e, (rate w : ℂ) •
    (LinearMap.adjoint (frequencyComponent b e A w.val) * frequencyComponent b e A w.val)

theorem rateSquareSum_positive (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (rate : Frequency e → ℝ) (hn : ∀ w, 0 ≤ rate w) :
    (rateSquareSum b e A rate).IsPositive := by
  apply LinearMap.isPositive_sum
  intro w _
  exact (LinearMap.isPositive_adjoint_comp_self _).smul_of_nonneg (by exact_mod_cast hn w)

theorem rateSquareSum_defect_positive (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : operatorNorm A ≤ 1) (rate : Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hu : ∀ w, rate w ≤ hmax) :
    ((hmax : ℂ) • (1 : Operator V) - rateSquareSum b e A rate).IsPositive := by
  have he : (hmax : ℂ) • (1 : Operator V) - rateSquareSum b e A rate =
      (hmax : ℂ) • (1-squareSum (fun w : Frequency e => frequencyComponent b e A w.val)) +
      ∑ w : Frequency e, ((hmax-rate w : ℝ) : ℂ) •
        (LinearMap.adjoint (frequencyComponent b e A w.val) * frequencyComponent b e A w.val) := by
    simp only [rateSquareSum, squareSum, Complex.ofReal_sub, sub_smul,
      Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub]
    module
  rw [he]
  apply LinearMap.IsPositive.add
  · exact (one_sub_frequency_squareSum_positive b e A hA).smul_of_nonneg (by exact_mod_cast hm)
  · apply LinearMap.isPositive_sum
    intro w _
    exact (LinearMap.isPositive_adjoint_comp_self _).smul_of_nonneg
      (by exact_mod_cast sub_nonneg.mpr (hu w))

theorem operatorNorm_le_of_positive_defect (A : Operator V) (c : ℝ) (hc : 0 ≤ c)
    (hA : A.IsPositive) (hdef : ((c : ℂ) • (1 : Operator V) - A).IsPositive) :
    operatorNorm A ≤ c := by
  let T := LinearMap.toContinuousLinearMap A
  have hT : T.IsPositive := (LinearMap.isPositive_toContinuousLinearMap_iff A).mpr hA
  change ‖T‖ ≤ c
  rw [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp [hx, hc]
  have hden : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hlower : 0 ≤ T.reApplyInnerSelf x := hT.re_inner_nonneg_left x
  have hupper : T.reApplyInnerSelf x ≤ c * ‖x‖^2 := by
    have h := hdef.re_inner_nonneg_left x
    change 0 ≤ (inner ℂ ((c : ℂ) • x - A x) x).re at h
    rw [inner_sub_left, inner_smul_left, Complex.sub_re] at h
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero,
      show (inner ℂ x x).re = ‖x‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) x] at h
    exact sub_nonneg.mp h
  have hquot : T.rayleighQuotient x = T.reApplyInnerSelf x / ‖x‖^2 := rfl
  rw [hquot, abs_of_nonneg (div_nonneg hlower hden.le)]
  exact (div_le_iff₀ hden).mpr hupper

theorem rateSquareSum_operatorNorm_le (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : operatorNorm A ≤ 1) (rate : Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ w, 0 ≤ rate w) (hu : ∀ w, rate w ≤ hmax) :
    operatorNorm (rateSquareSum b e A rate) ≤ hmax :=
  operatorNorm_le_of_positive_defect _ hmax hm (rateSquareSum_positive b e A rate hn)
    (rateSquareSum_defect_positive b e A hA rate hmax hm hu)

theorem weightedJump_squareSum {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (rate : κ → Frequency e → ℝ) (hn : ∀ a w, 0 ≤ rate a w) :
    squareSum (weightedJump b e A rate) = ∑ a, rateSquareSum b e (A a) (rate a) := by
  unfold squareSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  unfold rateSquareSum
  apply Finset.sum_congr rfl
  intro w _
  simp only [weightedJump, map_smulₛₗ, starRingEnd_apply, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (hn _ _)]

theorem weightedJump_squareSum_operatorNorm_le {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1) (rate : κ → Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    operatorNorm (squareSum (weightedJump b e A rate)) ≤ Fintype.card κ * hmax := by
  rw [weightedJump_squareSum b e A rate hn]
  calc
    operatorNorm (∑ a, rateSquareSum b e (A a) (rate a)) ≤
        ∑ a, operatorNorm (rateSquareSum b e (A a) (rate a)) := by
      simp only [operatorNorm, map_sum]
      exact norm_sum_le _ _
    _ ≤ ∑ _a : κ, hmax := Finset.sum_le_sum (fun a _ =>
      rateSquareSum_operatorNorm_le b e (A a) (hA a) (rate a) hmax hm (hn a) (hu a))
    _ = _ := by simp

/-- CLBT's self-adjoint induced norm counts physical couplings only. -/
theorem weightedJump_dissipatorNorm_le [Nontrivial V] {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1) (rate : κ → Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax) :
    lindbladDissipatorNorm (weightedJump b e A rate) ≤ 2 * Fintype.card κ * hmax := by
  apply (dissipatorNorm_le_squareSum _).trans
  have h := weightedJump_squareSum_operatorNorm_le b e A hA rate hmax hm hn hu
  linarith

/-- Pointwise source norm estimate on every self-adjoint input. -/
theorem weightedJump_dissipator_traceNorm_le [Nontrivial V] {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (A : κ → Operator V)
    (hA : ∀ a, operatorNorm (A a) ≤ 1) (rate : κ → Frequency e → ℝ)
    (hmax : ℝ) (hm : 0 ≤ hmax) (hn : ∀ a w, 0 ≤ rate a w) (hu : ∀ a w, rate a w ≤ hmax)
    (F : Operator V) (hF : F.IsSymmetric) :
    traceNorm (lindbladDissipator (weightedJump b e A rate) F) ≤
      (2 * Fintype.card κ * hmax) * traceNorm F := by
  apply (dissipator_traceNorm_le_squareSum _ F hF).trans
  have h := weightedJump_squareSum_operatorNorm_le b e A hA rate hmax hm hn hu
  have htwo : 2 * operatorNorm (squareSum (weightedJump b e A rate)) ≤
      2 * Fintype.card κ * hmax := by linarith
  exact mul_le_mul_of_nonneg_right htwo (traceNorm_nonneg F)

end
end QEC.Semantics.Davies

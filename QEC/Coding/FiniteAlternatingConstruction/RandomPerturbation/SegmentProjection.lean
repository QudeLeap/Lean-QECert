import QEC.Coding.ProbabilisticConstruction.SphericalCap.TriangleGeometry

/-! # Exact arithmetic projection onto a segment, including coincident endpoints -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

noncomputable def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clampUnit_bounds (x : ℝ) : 0 ≤ clampUnit x ∧ clampUnit x ≤ 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clampUnit_quadratic_min {Q D t : ℝ} (hQ : 0 < Q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Q*(clampUnit (D/Q))^2-2*D*clampUnit (D/Q) ≤ Q*t^2-2*D*t := by
  by_cases hD : D ≤ 0
  · have hd : D/Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hD hQ.le
    have hc : clampUnit (D/Q) = 0 := max_eq_left ((min_le_right _ _).trans hd)
    rw [hc]
    have hprod := mul_nonpos_of_nonpos_of_nonneg hD ht0
    have hsq := mul_nonneg hQ.le (sq_nonneg t)
    nlinarith
  · have hD0 : 0 < D := lt_of_not_ge hD
    by_cases hDQ : Q ≤ D
    · have hd : 1 ≤ D/Q := (le_div_iff₀ hQ).mpr (by simpa using hDQ)
      have hc : clampUnit (D/Q) = 1 := by simp [clampUnit,min_eq_left hd]
      rw [hc]
      have hsq := mul_nonneg hQ.le (sq_nonneg (t-1))
      have hprod := mul_nonneg (sub_nonneg.mpr hDQ) (sub_nonneg.mpr ht1)
      nlinarith
    · have hd0 : 0 ≤ D/Q := (div_pos hD0 hQ).le
      have hd1 : D/Q ≤ 1 := (div_le_iff₀ hQ).mpr (by linarith)
      have hc : clampUnit (D/Q) = D/Q := by simp [clampUnit,min_eq_right hd1,max_eq_right hd0]
      rw [hc]
      have he : Q*(D/Q) = D := by field_simp [hQ.ne']
      have hsq := mul_nonneg hQ.le (sq_nonneg (t-D/Q))
      have het := congrArg (fun x : ℝ => x*t) he
      have hec := congrArg (fun x : ℝ => x*(D/Q)) he
      nlinarith

noncomputable def segmentParameter (a b z : Space) : ℝ :=
  clampUnit (inner ℝ (z-a) (b-a)/‖b-a‖^2)

noncomputable def segmentPoint (a b z : Space) : Space :=
  a+segmentParameter a b z • (b-a)

theorem segment_distance_sq (a b z : Space) (t : ℝ) :
    ‖z-(a+t • (b-a))‖^2 =
      ‖z-a‖^2-2*t*inner ℝ (z-a) (b-a)+t^2*‖b-a‖^2 := by
  have he : z-(a+t • (b-a)) = (z-a)-t • (b-a) := by abel
  rw [he,norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

/-- No division assumption is needed when the endpoints coincide. -/
theorem segmentPoint_nearest (a b z : Space) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    dist z (segmentPoint a b z) ≤ dist z (a+t • (b-a)) := by
  by_cases hba : b-a = 0
  · simp [segmentPoint,hba]
  · have hQ : 0 < ‖b-a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hba)
    have hmin := clampUnit_quadratic_min (D := inner ℝ (z-a) (b-a)) hQ ht0 ht1
    have hsq : ‖z-segmentPoint a b z‖^2 ≤ ‖z-(a+t • (b-a))‖^2 := by
      unfold segmentPoint
      rw [segment_distance_sq a b z (segmentParameter a b z),segment_distance_sq a b z t]
      change ‖z-a‖^2-2*clampUnit (inner ℝ (z-a) (b-a)/‖b-a‖^2)*
        inner ℝ (z-a) (b-a)+(clampUnit (inner ℝ (z-a) (b-a)/‖b-a‖^2))^2*‖b-a‖^2 ≤ _
      nlinarith
    rw [dist_eq_norm,dist_eq_norm]
    nlinarith [norm_nonneg (z-segmentPoint a b z),norm_nonneg (z-(a+t • (b-a)))]

end QEC.Coding.BDL26RandomPerturbation

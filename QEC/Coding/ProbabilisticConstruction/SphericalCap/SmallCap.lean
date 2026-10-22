import QEC.Coding.ProbabilisticConstruction.SphericalCap.Slab

namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal

theorem displacement_distance_sq (R : ℝ) (s v : Sphere) :
    dist (R • (s : Space)) (R • (v : Space)) ^ 2 =
      2 * R^2 * (1 - inner ℝ (v : Space) (s : Space)) := by
  rw [dist_eq_norm, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real]
  simp only [norm_coe, one_pow]
  rw [real_inner_comm (s : Space) (v : Space)]
  ring

theorem displacement_ball_preimage {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (v : Sphere) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' closedBall (R • (v : Space)) ε =
      cap v (1 - ε^2 / (2*R^2)) := by
  ext s
  change dist (R • (s : Space)) (R • (v : Space)) ≤ ε ↔
    1 - ε^2 / (2*R^2) ≤ inner ℝ (v : Space) (s : Space)
  rw [← sq_le_sq₀ dist_nonneg hε, displacement_distance_sq]
  have hden : 0 < 2*R^2 := by positivity
  rw [mul_comm (2*R^2), ← le_div_iff₀ hden]
  constructor <;> intro h <;> linarith

theorem area_chord_cap {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hεR : ε ≤ 2*R) (v : Sphere) :
    area (cap v (1-ε^2/(2*R^2))) = ENNReal.ofReal (Real.pi*ε^2/R^2) := by
  have hR2 : 0 < 2*R^2 := by positivity
  have hquot : 0 ≤ ε^2/(2*R^2) := div_nonneg (sq_nonneg _) hR2.le
  have hquot2 : ε^2/(2*R^2) ≤ 2 := by
    apply (div_le_iff₀ hR2).mpr
    have hs := (sq_le_sq₀ hε (by positivity : 0 ≤ 2*R)).mpr hεR
    nlinarith
  rw [area_cap_all]
  have he : capHeight (1-ε^2/(2*R^2)) = ε^2/(2*R^2) := by
    simp only [capHeight, max_eq_right (by linarith : (-1:ℝ) ≤ 1-ε^2/(2*R^2))]
    rw [show 1-(1-ε^2/(2*R^2)) = ε^2/(2*R^2) by ring, max_eq_right hquot]
  rw [he]
  congr 1
  ring

theorem capDisplacementLaw_closedBall_le {R c ε : ℝ} (hR : 0 < R)
    (u v : Sphere) (hc0 : -1 < c) (hc1 : c < 1)
    (hε : 0 ≤ ε) (hεR : ε ≤ 2*R) :
    capDisplacementLaw R u c (closedBall (R • (v : Space)) ε) ≤
      ENNReal.ofReal (ε^2 / (2*R^2*(1-c))) := by
  rw [capDisplacementLaw, Measure.map_apply (by fun_prop) isClosed_closedBall.measurableSet,
    displacement_ball_preimage hR hε]
  have hbound := capLaw_le_of_area_le u hc0 hc1 (measurableSet_cap v _)
    (area_chord_cap hR hε hεR v).le
  have he : (Real.pi*ε^2/R^2)/(2*Real.pi*(1-c)) = ε^2/(2*R^2*(1-c)) := by
    field_simp [Real.pi_ne_zero, hR.ne', (sub_pos.mpr hc1).ne']
    <;> ring
  rwa [he] at hbound

end QEC.Coding.ProbabilisticConstruction.SphericalCap

import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.SegmentProjection

/-! # Exact Gram projection and its singular collinearity case -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace

noncomputable def gramDet (b c : Space) : ℝ := ‖b‖^2*‖c‖^2-(inner ℝ b c)^2

theorem gramDet_nonneg (b c : Space) : 0 ≤ gramDet b c := by
  have h := real_inner_mul_inner_self_le b c
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  unfold gramDet
  nlinarith

theorem gram_residual_sq (b c : Space) (hb : b ≠ 0) :
    ‖b‖^2*‖c-(inner ℝ b c/‖b‖^2) • b‖^2 = gramDet b c := by
  have hQ : ‖b‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm b c,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  unfold gramDet
  field_simp [hQ]
  <;> ring

/-- A singular Gram matrix yields the actual scalar relation, including antiparallel vectors. -/
theorem gramDet_zero_collinear (b c : Space) (hb : b ≠ 0) (hdet : gramDet b c = 0) :
    c = (inner ℝ b c/‖b‖^2) • b := by
  have h := gram_residual_sq b c hb
  rw [hdet] at h
  have hQ : ‖b‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  have hn := (mul_eq_zero.mp h).resolve_left hQ
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

noncomputable def planeU (b c d : Space) : ℝ :=
  (‖c‖^2*inner ℝ d b-inner ℝ b c*inner ℝ d c)/gramDet b c

noncomputable def planeV (b c d : Space) : ℝ :=
  (‖b‖^2*inner ℝ d c-inner ℝ b c*inner ℝ d b)/gramDet b c

theorem plane_coefficients (b c d : Space) (hdet : gramDet b c ≠ 0) :
    ‖b‖^2*planeU b c d+inner ℝ b c*planeV b c d = inner ℝ d b ∧
      inner ℝ b c*planeU b c d+‖c‖^2*planeV b c d = inner ℝ d c := by
  constructor <;> unfold planeU planeV
  all_goals
    field_simp [hdet]
    unfold gramDet
    ring

theorem plane_residual_orthogonal (b c d : Space) (hdet : gramDet b c ≠ 0) :
    inner ℝ (d-(planeU b c d • b+planeV b c d • c)) b = 0 ∧
      inner ℝ (d-(planeU b c d • b+planeV b c d • c)) c = 0 := by
  have h := plane_coefficients b c d hdet
  simp only [inner_sub_left,inner_add_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,real_inner_comm b c]
  constructor <;> linarith

theorem plane_coefficients_unique (b c d : Space) (hdet : gramDet b c ≠ 0)
    {u v : ℝ} (hb : ‖b‖^2*u+inner ℝ b c*v = inner ℝ d b)
    (hc : inner ℝ b c*u+‖c‖^2*v = inner ℝ d c) :
    u = planeU b c d ∧ v = planeV b c d := by
  constructor
  · unfold planeU
    apply (eq_div_iff hdet).mpr
    unfold gramDet
    linear_combination ‖c‖^2*hb-inner ℝ b c*hc
  · unfold planeV
    apply (eq_div_iff hdet).mpr
    unfold gramDet
    linear_combination ‖b‖^2*hc-inner ℝ b c*hb

end QEC.Coding.BDL26RandomPerturbation

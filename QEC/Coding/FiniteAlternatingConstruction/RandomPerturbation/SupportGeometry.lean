import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Geometry

/-! # Metric separation derived from actual radius-scaled cap support -/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

/-- Normalize a supported displacement without changing its independent coordinate. -/
noncomputable def normalizedDisplacement (p : Space) {R : ℝ} (hR : 0 < R) (hp : ‖p‖ = R) :
    Sphere := ⟨R⁻¹ • p, by
  simp [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), abs_of_pos hR, hp, hR.ne']⟩

theorem normalizedDisplacement_smul (p : Space) {R : ℝ} (hR : 0 < R) (hp : ‖p‖ = R) :
    R • (normalizedDisplacement p hR hp : Space) = p := by
  simp [normalizedDisplacement, smul_smul, hR.ne']

theorem normalizedDisplacement_mem (p : Space) {R c : ℝ} (hR : 0 < R) (u : Sphere)
    (hp : p ∈ displacementCap R u c) : normalizedDisplacement p hR hp.1 ∈ cap u c := by
  have hi : R • (normalizedDisplacement p hR hp.1 : Space) ∈ displacementCap R u c := by
    rwa [normalizedDisplacement_smul]
  have he := displacementCap_preimage hR u c
  change normalizedDisplacement p hR hp.1 ∈
    ((fun s : Sphere => R • (s : Space)) ⁻¹' displacementCap R u c) at hi
  rwa [he] at hi

/-- Actual ambient displacement laws inherit the orthogonal unit-cap estimate. -/
theorem supported_pair_inner (p q : Space) {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) {i j : Fin 3} (hij : i ≠ j)
    (hp : p ∈ displacementCap R (coordinateAxis i) (Real.cos θ))
    (hq : q ∈ displacementCap R (coordinateAxis j) (Real.cos θ)) :
    ⟪p,q⟫_ℝ ≤ R^2 / 4 := by
  have h := cap_pair_inner_le (coordinateAxis i) (coordinateAxis j)
    (normalizedDisplacement p hR hp.1) (normalizedDisplacement q hR hq.1)
    (coordinateAxis_orthogonal hij) hθ0 hθ1
    (normalizedDisplacement_mem p hR _ hp) (normalizedDisplacement_mem q hR _ hq)
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg R)
  rw [← normalizedDisplacement_smul p hR hp.1, ← normalizedDisplacement_smul q hR hq.1,
    real_inner_smul_left, real_inner_smul_right]
  nlinarith

/-- The stronger cap separation gives chord length at least R, hence the source R/6 bound. -/
theorem supported_pair_chord (p q : Space) {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) {i j : Fin 3} (hij : i ≠ j)
    (hp : p ∈ displacementCap R (coordinateAxis i) (Real.cos θ))
    (hq : q ∈ displacementCap R (coordinateAxis j) (Real.cos θ)) : R ≤ ‖p-q‖ := by
  have hi := supported_pair_inner p q hR hθ0 hθ1 hij hp hq
  have hn := norm_sub_sq_real p q
  rw [hp.1, hq.1] at hn
  have hnorm := norm_nonneg (p-q)
  nlinarith

/-- Narrowness follows from the selected integer cap parameter. -/
theorem cap_integer_narrow {m : ℕ} (hm : 2 ≤ m) :
    0 < (1 : ℝ)/(12*m) ∧ (1 : ℝ)/(12*m) ≤ 1/24 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < (12 : ℝ)*m := by positivity
  refine ⟨by positivity, ?_⟩
  apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 24)).mpr
  nlinarith

/-- The radial gap is larger than the source-defined width coefficient. -/
theorem widthFactor_le_three_quarters : widthFactor ≤ 3/4 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (1 : ℝ)/6)
  unfold widthFactor
  linarith

section Perturbed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Adding a diameter-lambda original edge preserves the chord lower bound. -/
theorem perturbed_edge_lower (a b p q : E) {R lambda : ℝ}
    (hchord : R ≤ ‖p-q‖) (hold : ‖a-b‖ ≤ lambda) :
    R-lambda ≤ ‖(a+p)-(b+q)‖ := by
  have he : p-q = ((a+p)-(b+q))-(a-b) := by abel
  have h := norm_sub_le ((a+p)-(b+q)) (a-b)
  rw [← he] at h
  linarith

theorem perturbed_edge_upper (a b p q : E) {R lambda : ℝ}
    (hp : ‖p‖ = R) (hq : ‖q‖ = R) (hold : ‖a-b‖ ≤ lambda) :
    ‖(a+p)-(b+q)‖ ≤ 2*R+lambda := by
  have he : (a+p)-(b+q) = (a-b)+(p-q) := by abel
  rw [he]
  have h₁ := norm_add_le (a-b) (p-q)
  have h₂ := norm_sub_le p q
  rw [hp,hq] at h₂
  linarith

/-- All three opposite segments inherit the same radial lower bound. -/
theorem perturbed_triangle_width (a b c p q s : E) {R lambda : ℝ} (hR : 0 < R)
    (hp : ‖p‖ = R) (hq : ‖q‖ = R) (hs : ‖s‖ = R)
    (hpq : ⟪p,q⟫_ℝ ≤ R^2/4) (hps : ⟪p,s⟫_ℝ ≤ R^2/4)
    (hqs : ⟪q,s⟫_ℝ ≤ R^2/4)
    (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda) (hbc : ‖b-c‖ ≤ lambda) :
    TriangleWidthAtLeast ((b+q)-(a+p)) ((c+s)-(a+p)) (R*(1-1/4)-lambda) := by
  have hba : ‖b-a‖ ≤ lambda := by simpa only [norm_sub_rev] using hab
  have hca : ‖c-a‖ ≤ lambda := by simpa only [norm_sub_rev] using hac
  have hcb : ‖c-b‖ ≤ lambda := by simpa only [norm_sub_rev] using hbc
  have hqp : ⟪q,p⟫_ℝ ≤ R^2/4 := by simpa only [real_inner_comm] using hpq
  have hsp : ⟪s,p⟫_ℝ ≤ R^2/4 := by simpa only [real_inner_comm] using hps
  have hsq : ⟪s,q⟫_ℝ ≤ R^2/4 := by simpa only [real_inner_comm] using hqs
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 ht1
    have h := perturbed_segment_lower c a b s p q (k := 1/4) hR hs
      (by simpa only [div_eq_mul_inv,one_mul] using hsp)
      (by simpa only [div_eq_mul_inv,one_mul] using hsq) hca hcb ht0 ht1
    have he : ((c+s)-(a+p))-t • ((b+q)-(a+p)) =
        (c+s)-((1-t) • (a+p)+t • (b+q)) := by module
    rwa [he]
  · intro t ht0 ht1
    have h := perturbed_segment_lower b a c q p s (k := 1/4) hR hq
      (by simpa only [div_eq_mul_inv,one_mul] using hqp)
      (by simpa only [div_eq_mul_inv,one_mul] using hqs) hba hbc ht0 ht1
    have he : ((b+q)-(a+p))-t • ((c+s)-(a+p)) =
        (b+q)-((1-t) • (a+p)+t • (c+s)) := by module
    rwa [he]
  · intro t ht0 ht1
    have h := perturbed_segment_lower a b c p q s (k := 1/4) hR hp
      (by simpa only [div_eq_mul_inv,one_mul] using hpq)
      (by simpa only [div_eq_mul_inv,one_mul] using hps) hab hac ht0 ht1
    have he : (1-t) • ((b+q)-(a+p))+t • ((c+s)-(a+p)) =
        -((a+p)-((1-t) • (b+q)+t • (c+s))) := by module
    simpa only [he,norm_neg] using h

end Perturbed
end QEC.Coding.BDL26RandomPerturbation

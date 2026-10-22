import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Parameters
import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Incidence

/-!
# Orthogonal cap geometry and segment width

All metric estimates are derived from the actual cap supports. The radial
projection bounds the distance to an opposite segment, including its endpoints.
-/

namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace

noncomputable def coordinateAxis (i : Fin 3) : Sphere :=
  ⟨PiLp.single 2 i (1 : ℝ), by simp [Metric.mem_sphere, dist_zero_right]⟩

theorem coordinateAxis_orthogonal {i j : Fin 3} (h : i ≠ j) :
    ⟪(coordinateAxis i : Space), (coordinateAxis j : Space)⟫_ℝ = 0 := by
  simp [coordinateAxis, PiLp.inner_apply, PiLp.single_apply, h, Ne.symm h]

/-- Constructor colors are fixed even when vertex images coincide. -/
def vertexColor (P : TannerSquarePresentation) : Vertex P → Fin 3
  | .x _ => 0
  | .q _ => 1
  | .z _ => 2

theorem vertexColor_triangleVertex (P : TannerSquarePresentation) (t : Triangle P) (i : Fin 3) :
    vertexColor P (triangleVertex P t i) = i := by
  fin_cases i <;> rfl

/-- A sufficiently narrow actual cap lies close to its axis. -/
theorem cap_near_axis (u s : Sphere) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 24)
    (hs : s ∈ cap u (Real.cos θ)) : ‖(s : Space) - (u : Space)‖ ≤ 1 / 8 := by
  have hc : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  have hi : Real.cos θ ≤ ⟪(u : Space), (s : Space)⟫_ℝ := hs
  have hn := norm_sub_sq_real (s : Space) (u : Space)
  rw [norm_coe, norm_coe] at hn
  have hcomm := real_inner_comm (s : Space) (u : Space)
  have hnorm := norm_nonneg ((s : Space) - (u : Space))
  have hsq : θ ^ 2 ≤ (1 / 24 : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- Two cap coordinates on orthogonal axes have a uniform inner-product gap. -/
theorem cap_pair_inner_le (u v s t : Sphere) (huv : ⟪(u : Space), (v : Space)⟫_ℝ = 0)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 24)
    (hs : s ∈ cap u (Real.cos θ)) (ht : t ∈ cap v (Real.cos θ)) :
    ⟪(s : Space), (t : Space)⟫_ℝ ≤ 1 / 4 := by
  have hs' := cap_near_axis u s hθ0 hθ1 hs
  have ht' := cap_near_axis v t hθ0 hθ1 ht
  have h₁ := real_inner_le_norm ((s : Space) - (u : Space)) (t : Space)
  have h₂ := real_inner_le_norm (u : Space) ((t : Space) - (v : Space))
  rw [norm_coe, mul_one, inner_sub_left] at h₁
  rw [norm_coe, one_mul, inner_sub_right, huv] at h₂
  linarith

section Radial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A radial supporting functional separates a vertex from every opposite convex combination. -/
theorem radial_segment_lower (p q s : E) {R c t : ℝ} (hR : 0 < R)
    (hp : ‖p‖ = R) (hpq : ⟪p, q⟫_ℝ ≤ R ^ 2 * c)
    (hps : ⟪p, s⟫_ℝ ≤ R ^ 2 * c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R * (1 - c) ≤ ‖p - ((1 - t) • q + t • s)‖ := by
  have hq := mul_le_mul_of_nonneg_left hpq (sub_nonneg.mpr ht1)
  have hs := mul_le_mul_of_nonneg_left hps ht0
  have hb := real_inner_le_norm p (p - ((1-t) • q + t • s))
  rw [inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hp] at hb
  have hh : R * (R * (1-c)) ≤ R * ‖p - ((1-t) • q + t • s)‖ := by nlinarith
  exact (mul_le_mul_iff_right₀ hR).mp hh

/-- A triangle of diameter at most lambda moves its opposite convex segment by at most lambda. -/
theorem old_segment_upper (a b c : E) {lambda t : ℝ}
    (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖a - ((1-t) • b + t • c)‖ ≤ lambda := by
  have he : a - ((1-t) • b + t • c) = (1-t) • (a-b) + t • (a-c) := by module
  rw [he]
  calc
    _ ≤ ‖(1-t) • (a-b)‖ + ‖t • (a-c)‖ := norm_add_le _ _
    _ = (1-t) * ‖a-b‖ + t * ‖a-c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1-t) * lambda + t * lambda :=
      add_le_add (mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left hac ht0)
    _ = lambda := by ring

/-- Add the original bounded-diameter positions to a radially separated triangle. -/
theorem perturbed_segment_lower (a b c p q s : E) {R k lambda t : ℝ}
    (hR : 0 < R) (hp : ‖p‖ = R) (hpq : ⟪p,q⟫_ℝ ≤ R^2*k)
    (hps : ⟪p,s⟫_ℝ ≤ R^2*k) (hab : ‖a-b‖ ≤ lambda) (hac : ‖a-c‖ ≤ lambda)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R*(1-k)-lambda ≤ ‖(a+p)-((1-t) • (b+q)+t • (c+s))‖ := by
  have hr := radial_segment_lower p q s hR hp hpq hps ht0 ht1
  have ho := old_segment_upper a b c hab hac ht0 ht1
  have he : p-((1-t) • q+t • s) =
      ((a+p)-((1-t) • (b+q)+t • (c+s))) - (a-((1-t) • b+t • c)) := by module
  rw [he] at hr
  have hn := norm_sub_le ((a+p)-((1-t) • (b+q)+t • (c+s))) (a-((1-t) • b+t • c))
  linarith

end Radial
end QEC.Coding.BDL26RandomPerturbation

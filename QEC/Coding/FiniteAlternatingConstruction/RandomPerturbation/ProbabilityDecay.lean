import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.EventProbability

/-! # Uniform inverse-scale decay of the actual geometric event probability -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem event_probability_real_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P R c)).real
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ℝ)*(18*2/(R*(1-c)))^4 := by
  have hb := event_probability_le P J radius lambda K e hR hc0 hc1
  have htop : (Fintype.card (Grid K) : ENNReal)*ENNReal.ofReal (18*2/(R*(1-c)))^4 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have h := ENNReal.toReal_mono htop hb
  have hden : 0 < 1-c := sub_pos.mpr hc1
  have hn : 0 ≤ (18*2 : ℝ)/(R*(1-c)) := by positivity
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hn] using h

/-- The conservative 125-ball coefficient also dominates the directly proved radius-two bound.
This constant depends only on the fixed cap parameters, not input size or lambda. -/
noncomputable def probabilityCoefficient (a : ℕ) (c : ℝ) : ℝ :=
  ((2*(a+2)+1 : ℕ)^3 : ℝ)*(125*18/((a : ℝ)*(1-c)))^4

theorem event_probability_real_decay (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (a lambda : ℕ) (ha : 0 < a) (hl : 1 ≤ lambda)
    (e : Event P J radius) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) :
    (Measure.pi (vertexLaw P ((a : ℝ)*lambda) c)).real
      (localEvent (eventSupport P J radius)
        (eventBad P J radius lambda ((a+2)*lambda)) e) ≤
      probabilityCoefficient a c/(lambda : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlR : (0 : ℝ) < lambda := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hl)
  have hden : 0 < 1-c := sub_pos.mpr hc1
  let B : ℝ := 125*18/((a : ℝ)*(1-c))
  have hhit0 : 0 ≤ (18*2 : ℝ)/((a : ℝ)*lambda*(1-c)) := by positivity
  have hhit : (18*2 : ℝ)/((a : ℝ)*lambda*(1-c)) ≤ B/(lambda : ℝ) := by
    calc
      _ ≤ (125*18 : ℝ)/((a : ℝ)*lambda*(1-c)) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ = B/(lambda : ℝ) := by
        dsimp [B]
        field_simp [haR.ne',hlR.ne',hden.ne']
        <;> ring
  have hgrid : (Fintype.card (Grid ((a+2)*lambda)) : ℝ) ≤
      ((2*(a+2)+1 : ℕ)^3 : ℝ)*(lambda : ℝ)^3 := by
    exact_mod_cast scaled_grid_card_le (a+2) lambda hl
  have hb := event_probability_real_le P J radius lambda ((a+2)*lambda) e
    (mul_pos haR hlR) hc0 hc1
  calc
    _ ≤ (Fintype.card (Grid ((a+2)*lambda)) : ℝ)*
        (18*2/((a : ℝ)*lambda*(1-c)))^4 := hb
    _ ≤ (((2*(a+2)+1 : ℕ)^3 : ℝ)*(lambda : ℝ)^3)*(B/(lambda : ℝ))^4 :=
      mul_le_mul hgrid (pow_le_pow_left₀ hhit0 hhit 4) (by positivity) (by positivity)
    _ = probabilityCoefficient a c/(lambda : ℝ) := by
      rw [cubic_times_four_hits hlR]
      rfl

end QEC.Coding.BDL26RandomPerturbation

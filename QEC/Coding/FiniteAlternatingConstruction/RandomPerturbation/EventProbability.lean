import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Events

/-! # Actual finite-net bad-event probabilities -/

namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

/-- Joint triangle independence is derived before taking the finite union of grid centers. -/
theorem event_probability_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius)
    {R c : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) :
    Measure.pi (vertexLaw P R c)
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e) ≤
      (Fintype.card (Grid K) : ENNReal)*ENNReal.ofReal (18*2/(R*(1-c)))^4 := by
  let test (g : Grid K) : Set (Vertex P → Space) :=
    {p | ∀ a : e.val, (fun i => p (triangleVertex P a.val i)) ∈
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex P a.val i)))
        (eventCenter P J radius lambda K e g) 2}
  have he : localEvent (eventSupport P J radius) (eventBad P J radius lambda K) e =
      ⋃ g : Grid K, test g := by
    ext p
    simpa only [test,Set.mem_iUnion,Set.mem_setOf_eq] using mem_global_event P J radius lambda K e p
  have hb (g : Grid K) : Measure.pi (vertexLaw P R c) (test g) ≤
      ENNReal.ofReal (18*2/(R*(1-c)))^4 := by
    have h := monochromatic_triangle_hit_probability P (fun a : e.val => a.val)
      Subtype.val_injective (fun a b => e.property.2.1 a.val a.property b.val b.property)
      hR hc0 hc1 (by norm_num : (0 : ℝ) ≤ 2)
      (fun v => lambda • ((1/2 : ℝ) • J v)) (eventCenter P J radius lambda K e g)
    simpa only [Fintype.card_coe,e.property.1] using h
  rw [he]
  calc
    _ ≤ ∑ g : Grid K, Measure.pi (vertexLaw P R c) (test g) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _g : Grid K, ENNReal.ofReal (18*2/(R*(1-c)))^4 :=
      Finset.sum_le_sum (fun g _ => hb g)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- At integral scale lambda>=1 the grid count is cubic with a scale-independent coefficient. -/
theorem scaled_grid_card_le (a lambda : ℕ) (hl : 1 ≤ lambda) :
    Fintype.card (Grid (a*lambda)) ≤ (2*a+1)^3*lambda^3 := by
  rw [grid_card]
  have hb : 2*(a*lambda)+1 ≤ (2*a+1)*lambda := by nlinarith
  calc
    _ ≤ ((2*a+1)*lambda)^3 := Nat.pow_le_pow_left hb 3
    _ = _ := by rw [mul_pow]

/-- Cubic search volume times four inverse-scale hit factors gives inverse-scale decay. -/
theorem cubic_times_four_hits {lambda C B : ℝ} (hl : 0 < lambda) :
    C*lambda^3*(B/lambda)^4 = (C*B^4)/lambda := by
  field_simp [hl.ne']

end QEC.Coding.BDL26RandomPerturbation

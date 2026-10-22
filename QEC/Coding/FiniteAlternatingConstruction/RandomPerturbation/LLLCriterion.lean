import QEC.Coding.FiniteAlternatingConstruction.RandomPerturbation.Parameters
import Mathlib.Algebra.Order.Ring.Pow

/-! # Explicit uniform weights for the finite asymmetric local lemma -/

namespace QEC.Coding.BDL26RandomPerturbation

noncomputable def lllWeight (D : ℕ) : ℝ := 1/(2*((D : ℝ)+1))

theorem lllWeight_bounds (D : ℕ) :
    0 < lllWeight D ∧ lllWeight D ≤ 1/2 ∧ lllWeight D < 1 := by
  have hd : 0 < 2*((D : ℝ)+1) := by positivity
  have hpos : 0 < lllWeight D := by unfold lllWeight; positivity
  have hhalf : lllWeight D ≤ 1/2 := by
    unfold lllWeight
    apply (div_le_iff₀ hd).mpr
    have hn : (0 : ℝ) ≤ D := by positivity
    nlinarith
  exact ⟨hpos,hhalf,by linarith⟩

theorem lllWeight_mul (D : ℕ) : 2*((D : ℝ)+1)*lllWeight D = 1 := by
  have hd : (D : ℝ)+1 ≠ 0 := by positivity
  unfold lllWeight
  field_simp [hd]

/-- Bernoulli gives a uniform positive lower bound for the entire neighbor product. -/
theorem lll_neighbor_product_lower {I : Type*} (D : ℕ) (s : Finset I)
    (hcard : s.card ≤ D) :
    (1/2 : ℝ) ≤ ∏ _i ∈ s, (1-lllWeight D) := by
  have hx := lllWeight_bounds D
  have hd : (s.card : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_right hd hx.1.le
  have he := lllWeight_mul D
  have hsmall : (s.card : ℝ)*lllWeight D ≤ 1/2 := by nlinarith
  have hb := one_add_mul_le_pow (a := -lllWeight D) (by linarith : -2 ≤ -lllWeight D) s.card
  rw [Finset.prod_const]
  have hb' : 1-(s.card : ℝ)*lllWeight D ≤ (1-lllWeight D)^s.card := by
    simpa only [sub_eq_add_neg,mul_neg] using hb
  linarith

/-- The actual degree and probability bounds can be substituted directly into this criterion. -/
theorem uniform_lll_criterion {I : Type*} (D : ℕ) (s : Finset I)
    (hcard : s.card ≤ D) {p : ℝ} (hp : p ≤ 1/(4*((D : ℝ)+1))) :
    p ≤ lllWeight D * ∏ _i ∈ s, (1-lllWeight D) := by
  have hx := lllWeight_bounds D
  have hprod := mul_le_mul_of_nonneg_left (lll_neighbor_product_lower D s hcard) hx.1.le
  have he : (1 : ℝ)/(4*((D : ℝ)+1)) = lllWeight D*(1/2) := by
    have hd : (D : ℝ)+1 ≠ 0 := by positivity
    unfold lllWeight
    field_simp [hd]
    <;> ring
  calc
    p ≤ 1/(4*((D : ℝ)+1)) := hp
    _ = lllWeight D*(1/2) := he
    _ ≤ _ := hprod

end QEC.Coding.BDL26RandomPerturbation

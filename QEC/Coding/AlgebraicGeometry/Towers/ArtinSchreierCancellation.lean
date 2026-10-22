import Mathlib.FieldTheory.Perfect
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticRefinement
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-!
# Local Artin--Schreier cancellation in characteristic two

The key local step in the Garcia--Stichtenoth compositum argument replaces the
ratio of two simple-pole Artin--Schreier parameters by a square plus an element
of the maximal ideal.  This file proves that replacement from the actual finite
residue field, and proves the resulting characteristic-two coordinate identity.

No compositum, different exponent, ramification index, genus, or divisor
formula is asserted here.  Those conclusions require the later place and
integral-closure arguments.
-/

open scoped Polynomial RatFunc WithZero

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

variable {K : Type*} [Field K] [Algebra F256 K]

/-- A unit in the valuation ring is a square modulo the maximal ideal.  The
square root is lifted from the actual finite residue field, while the error is
an actual member of the maximal ideal. -/
theorem exists_unit_square_add_maximalIdeal
    (P : GlobalPlace F256 K) [Finite P.residueField]
    (q : P.valuationRing)
    (hq : q ∉ IsLocalRing.maximalIdeal P.valuationRing) :
    ∃ u w : P.valuationRing,
      q = u ^ 2 + w ∧
        u ∉ IsLocalRing.maximalIdeal P.valuationRing ∧
        w ∈ IsLocalRing.maximalIdeal P.valuationRing := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
  letI : Algebra F256 P.residueField := GlobalPlace.residueAlgebra P
  letI : CharP P.residueField 2 :=
    charP_of_injective_algebraMap
      (algebraMap F256 P.residueField).injective 2
  obtain ⟨r, hr⟩ :=
    surjective_frobenius P.residueField 2 (P.residue q)
  have hr_square : r ^ 2 = P.residue q := by
    simpa only [frobenius_def] using hr
  obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective r
  have hu' : P.residue u = r := by
    simpa only [GlobalPlace.residue] using hu
  let w : P.valuationRing := q - u ^ 2
  have hw_residue : P.residue w = 0 := by
    simp only [w, map_sub, map_pow, hu', hr_square, sub_self]
  have hw : w ∈ IsLocalRing.maximalIdeal P.valuationRing :=
    (P.residue_eq_zero_iff w).mp hw_residue
  have hu_not_maximal : u ∉ IsLocalRing.maximalIdeal P.valuationRing := by
    intro hu_maximal
    have hu_zero : P.residue u = 0 :=
      (P.residue_eq_zero_iff u).mpr hu_maximal
    apply hq
    rw [← P.residue_eq_zero_iff, ← hr_square, ← hu', hu_zero]
    norm_num
  refine ⟨u, w, ?_, hu_not_maximal, hw⟩
  simp only [w]
  ring

private theorem ne_zero_of_order_eq_neg_one
    (P : GlobalPlace F256 K) {z : K} (hz : P.order z = -1) : z ≠ 0 := by
  intro hzero
  subst z
  simp [GlobalPlace.order] at hz

private theorem valuation_eq_one_of_order_eq_zero
    (P : GlobalPlace F256 K) {z : K} (hz : z ≠ 0)
    (horder : P.order z = 0) : P.valuation z = 1 := by
  have hvaluation_ne : P.valuation z ≠ 0 :=
    P.valuation.ne_zero_iff.mpr hz
  have hlog : WithZero.log (P.valuation z) = 0 := by
    unfold GlobalPlace.order at horder
    omega
  calc
    P.valuation z = WithZero.exp (WithZero.log (P.valuation z)) :=
      (WithZero.exp_log hvaluation_ne).symm
    _ = 1 := by rw [hlog]; simp

/-- A regular multiple of a normalized simple pole, plus a regular term, is
either still a normalized simple pole or becomes regular.  The conclusion
uses the discrete integer normalization; it does not assume a cancellation
case in advance. -/
theorem order_regular_mul_simplePole_add_regular
    (P : GlobalPlace F256 K) (x c r : K)
    (hx : P.order x = -1)
    (hc : GlobalPlace.RegularAt P c)
    (hr : GlobalPlace.RegularAt P r) :
    P.order (c * x + r) = -1 ∨ 0 ≤ P.order (c * x + r) := by
  have hx_ne : x ≠ 0 := ne_zero_of_order_eq_neg_one P hx
  have hxvaluation_ne : P.valuation x ≠ 0 :=
    P.valuation.ne_zero_iff.mpr hx_ne
  have hxlog : WithZero.log (P.valuation x) = 1 := by
    unfold GlobalPlace.order at hx
    omega
  have hxvaluation : P.valuation x = WithZero.exp (1 : ℤ) := by
    calc
      P.valuation x = WithZero.exp (WithZero.log (P.valuation x)) :=
        (WithZero.exp_log hxvaluation_ne).symm
      _ = WithZero.exp (1 : ℤ) := by rw [hxlog]
  have hcxvaluation : P.valuation (c * x) ≤ WithZero.exp (1 : ℤ) := by
    rw [P.valuation.map_mul, hxvaluation]
    simpa only [one_mul] using
      mul_le_mul_left hc (WithZero.exp (1 : ℤ))
  have hone_le_exp : (1 : ℤᵐ⁰) ≤ WithZero.exp (1 : ℤ) := by
    simpa only [WithZero.exp_zero] using
      (WithZero.exp_le_exp.mpr (show (0 : ℤ) ≤ 1 by omega))
  have hrvaluation : P.valuation r ≤ WithZero.exp (1 : ℤ) :=
    hr.trans hone_le_exp
  have hsumvaluation :
      P.valuation (c * x + r) ≤ WithZero.exp (1 : ℤ) :=
    (P.valuation.map_add (c * x) r).trans
      (max_le hcxvaluation hrvaluation)
  by_cases hsum : c * x + r = 0
  · right
    rw [hsum]
    simp [GlobalPlace.order]
  · have hsumvaluation_ne : P.valuation (c * x + r) ≠ 0 :=
      P.valuation.ne_zero_iff.mpr hsum
    have hlog_le : WithZero.log (P.valuation (c * x + r)) ≤ 1 :=
      (WithZero.log_le_iff_le_exp hsumvaluation_ne (a := 1)).mpr
        hsumvaluation
    have horder_ge : -1 ≤ P.order (c * x + r) := by
      unfold GlobalPlace.order
      omega
    omega

/-- The transformed Artin--Schreier right-hand side has the local dichotomy
needed by the compositum proof once the coefficient and error term have been
shown regular at the upper place. -/
theorem artinSchreier_transformedRhs_order_dichotomy
    (P : GlobalPlace F256 K) (x z₁ u w : K)
    (hx : P.order x = -1)
    (hu : GlobalPlace.RegularAt P u)
    (hzw : GlobalPlace.RegularAt P (z₁ * w)) :
    P.order ((u - u ^ 2) * x + z₁ * w) = -1 ∨
      0 ≤ P.order ((u - u ^ 2) * x + z₁ * w) := by
  have hu_mem : u ∈ P.valuationRing :=
    (P.regularAt_iff_mem_valuationRing u).mp hu
  have hu_sq_mem : u ^ 2 ∈ P.valuationRing := by
    rw [pow_two]
    exact P.valuationRing.mul_mem _ _ hu_mem hu_mem
  have hcoefficient : GlobalPlace.RegularAt P (u - u ^ 2) :=
    (P.regularAt_iff_mem_valuationRing (u - u ^ 2)).mpr
      (P.valuationRing.sub_mem hu_mem hu_sq_mem)
  exact order_regular_mul_simplePole_add_regular P x (u - u ^ 2)
    (z₁ * w) hx hcoefficient hzw

variable [Algebra (Polynomial F256) K] [Algebra (RatFunc F256) K]
variable [IsScalarTower (Polynomial F256) (RatFunc F256) K]
variable [_root_.FunctionField F256 K]
variable [Algebra.IsSeparable (RatFunc F256) K]

/-- The ratio of two actual normalized simple-pole parameters is a unit square
plus a maximal-ideal error.  This is the precise residue-field cancellation
input used in the later two-extension compositum argument. -/
theorem exists_simplePoleRatio_square_add_maximalIdeal
    (P : GlobalPlace F256 K) (z₁ z₂ : K)
    (hz₁ : P.order z₁ = -1) (hz₂ : P.order z₂ = -1) :
    ∃ u w : P.valuationRing,
      z₂ / z₁ = (u : K) ^ 2 + (w : K) ∧
        u ∉ IsLocalRing.maximalIdeal P.valuationRing ∧
        w ∈ IsLocalRing.maximalIdeal P.valuationRing := by
  have hz₁_ne : z₁ ≠ 0 := ne_zero_of_order_eq_neg_one P hz₁
  have hz₂_ne : z₂ ≠ 0 := ne_zero_of_order_eq_neg_one P hz₂
  have hratio_ne : z₂ / z₁ ≠ 0 := div_ne_zero hz₂_ne hz₁_ne
  have hratio_order : P.order (z₂ / z₁) = 0 := by
    rw [div_eq_mul_inv, P.order_mul hz₂_ne (inv_ne_zero hz₁_ne),
      P.order_inv, hz₁, hz₂]
    norm_num
  have hratio_regular : GlobalPlace.RegularAt P (z₂ / z₁) :=
    (P.regularAt_iff_order_nonnegative hratio_ne).mpr (by omega)
  let q : P.valuationRing :=
    ⟨z₂ / z₁, (P.mem_valuationRing_iff (z₂ / z₁)).mpr hratio_regular⟩
  have hq_not_maximal : q ∉ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change ¬P.valuation (z₂ / z₁) < 1
    rw [valuation_eq_one_of_order_eq_zero P hratio_ne hratio_order]
    exact lt_irrefl 1
  letI : Finite P.residueField := GlobalPlace.finite_residueField P
  obtain ⟨u, w, hq, hu, hw⟩ :=
    exists_unit_square_add_maximalIdeal P q hq_not_maximal
  refine ⟨u, w, ?_, hu, hw⟩
  have hq_field := congrArg (fun y : P.valuationRing => (y : K)) hq
  simp only [q, map_add, map_pow] at hq_field ⊢
  exact hq_field

/-- Translating one Artin--Schreier coordinate by the lifted square root gives
the literal transformed right-hand side from the local compositum proof. -/
theorem artinSchreier_translate_equation
    {L : Type*} [Field L] [CharP L 2]
    (x₁ x₂ z₁ z₂ u w : L)
    (hx₁ : x₁ ^ 2 + x₁ = z₁)
    (hx₂ : x₂ ^ 2 + x₂ = z₂)
    (hz₂ : z₂ = z₁ * (u ^ 2 + w)) :
    (x₂ - u * x₁) ^ 2 + (x₂ - u * x₁) =
      (u - u ^ 2) * x₁ + z₁ * w := by
  have htwo : (2 : L) = 0 := CharP.cast_eq_zero L 2
  calc
    (x₂ - u * x₁) ^ 2 + (x₂ - u * x₁) =
        (x₂ ^ 2 + x₂) + u ^ 2 * (x₁ ^ 2 + x₁) +
          (u - u ^ 2) * x₁ := by
      linear_combination -(u * x₁ * (x₂ + 1)) * htwo
    _ = z₂ + u ^ 2 * z₁ + (u - u ^ 2) * x₁ := by rw [hx₁, hx₂]
    _ = (u - u ^ 2) * x₁ + z₁ * w := by
      rw [hz₂]
      linear_combination (z₁ * u ^ 2) * htwo

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

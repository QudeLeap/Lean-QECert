import QEC.Distillation.FifteenQubitH.Recurrence

/-!
# BK15 threshold, convergence, and H-fidelity bridge

This module develops the exact real recurrence derived in
`BK15.Recurrence` from the concrete fifteen-qubit accepted run.  It keeps the
analytic recurrence connected to that protocol throughout: the scalar map is a
local coordinate for the proved accepted-output error, never a replacement for
the physical construction.
-/

noncomputable section

namespace QEC
namespace Distillation
namespace BK15
namespace Threshold

open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

/-- The signed source-A bias attached to a raw real error parameter. -/
def bk15Bias (epsilon : Real) : Real := 1 - 2 * epsilon

/-- The analytic coordinate of the actual accepted-output error recurrence. -/
def bk15Recurrence (epsilon : Real) : Real :=
  (1 - 15 * bk15Bias epsilon ^ 7 + 15 * bk15Bias epsilon ^ 8 -
    bk15Bias epsilon ^ 15) /
    (2 * (1 + 15 * bk15Bias epsilon ^ 8))

/-- The polynomial obtained from a non-endpoint fixed point in bias
coordinates. -/
def bk15FixedPolynomial (bias : Real) : Real :=
  bias ^ 14 - 15 * bias ^ 8 + 15 * bias ^ 6 - 1

/-- The cubic controlling the unique non-endpoint BK15 fixed point. -/
def bk15FixedCubic (y : Real) : Real := y ^ 3 - 5 * y ^ 2 + 6 * y - 16

theorem bk15Bias_eq_recurrence_bias (epsilon : BK15Epsilon) :
    bk15Bias epsilon.epsilon = bk15_r epsilon := by
  rfl

theorem bk15Recurrence_denominator_pos (epsilon : Real) :
    0 < 1 + 15 * bk15Bias epsilon ^ 8 := by
  have hpow : 0 <= bk15Bias epsilon ^ 8 := by positivity
  nlinarith

theorem bk15Recurrence_scaled_denominator_pos (epsilon : Real) :
    0 < 2 * (1 + 15 * bk15Bias epsilon ^ 8) := by
  nlinarith [bk15Recurrence_denominator_pos epsilon]

/-- The scalar coordinate is exactly the error of #707's actual accepted
BK15 run on every strict physical input. -/
theorem bk15Recurrence_eq_actual_acceptedOutputError
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    bk15Recurrence epsilon.epsilon =
      bk15OutputError (bk15Run epsilon hpositive).acceptedOutput aZeroDensity := by
  rw [bk15_acceptedOutputError_closed_form epsilon hpositive]
  rfl

/-- The transformed recurrence used for fixed-point and sign analysis. -/
theorem one_sub_two_mul_bk15Recurrence (epsilon : Real) :
    1 - 2 * bk15Recurrence epsilon =
      bk15Bias epsilon ^ 7 * (15 + bk15Bias epsilon ^ 8) /
        (1 + 15 * bk15Bias epsilon ^ 8) := by
  have hdenom : 1 + 15 * bk15Bias epsilon ^ 8 ≠ 0 :=
    (bk15Recurrence_denominator_pos epsilon).ne'
  unfold bk15Recurrence
  field_simp [hdenom]
  ring

theorem bk15Recurrence_zero : bk15Recurrence 0 = 0 := by
  norm_num [bk15Recurrence, bk15Bias]

theorem bk15Recurrence_half : bk15Recurrence (1 / 2) = 1 / 2 := by
  norm_num [bk15Recurrence, bk15Bias]

theorem bk15FixedPolynomial_eq_zero_of_interior_fixed
    {epsilon : Real} (hhalf : epsilon < 1 / 2)
    (hfixed : bk15Recurrence epsilon = epsilon) :
    bk15FixedPolynomial (bk15Bias epsilon) = 0 := by
  have hdenom : 1 + 15 * bk15Bias epsilon ^ 8 ≠ 0 :=
    (bk15Recurrence_denominator_pos epsilon).ne'
  have hbias_ne : bk15Bias epsilon ≠ 0 := by
    unfold bk15Bias
    linarith
  have htransform := one_sub_two_mul_bk15Recurrence epsilon
  rw [hfixed] at htransform
  field_simp [hdenom] at htransform
  have hproduct :
      bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon) = 0 := by
    calc
      bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon) =
          -(bk15Bias epsilon * (1 + 15 * bk15Bias epsilon ^ 8) -
            bk15Bias epsilon ^ 7 * (15 + bk15Bias epsilon ^ 8)) := by
              unfold bk15FixedPolynomial
              ring
      _ = 0 := by
              unfold bk15Bias at htransform ⊢
              ring_nf at htransform ⊢
              linarith
  exact (mul_eq_zero.mp hproduct).resolve_left hbias_ne

theorem bk15FixedPolynomial_cubic_factor (bias : Real) (hbias : bias ≠ 0) :
    bk15FixedPolynomial bias / bias ^ 7 =
      (bias - bias⁻¹) *
        bk15FixedCubic ((bias + bias⁻¹) ^ 2) := by
  unfold bk15FixedPolynomial bk15FixedCubic
  field_simp [hbias]
  ring

theorem bk15FixedCubic_strictMonoOn :
    StrictMonoOn bk15FixedCubic (Set.Ici 4) := by
  intro x hx y hy hxy
  have hx' : 4 <= x := hx
  have hy' : 4 <= y := hy
  have hfactor :
      bk15FixedCubic y - bk15FixedCubic x =
        (y - x) * (y ^ 2 + x * y + x ^ 2 - 5 * (x + y) + 6) := by
    unfold bk15FixedCubic
    ring
  have hcoefficient : 0 < y ^ 2 + x * y + x ^ 2 - 5 * (x + y) + 6 := by
    have hshift : y ^ 2 + x * y + x ^ 2 - 5 * (x + y) + 6 =
        14 + 7 * (x - 4) + 7 * (y - 4) +
          (x - 4) ^ 2 + (x - 4) * (y - 4) + (y - 4) ^ 2 := by
      ring
    rw [hshift]
    have hxnonneg : 0 <= x - 4 := sub_nonneg.mpr hx'
    have hynonneg : 0 <= y - 4 := sub_nonneg.mpr hy'
    positivity
  nlinarith [hfactor, mul_pos (sub_pos.mpr hxy) hcoefficient]

private theorem bias_add_inv_ge_two {bias : Real} (hpositive : 0 < bias) :
    2 <= bias + bias⁻¹ := by
  have hidentity : bias + bias⁻¹ - 2 = (bias - 1) ^ 2 / bias := by
    field_simp [hpositive.ne']
    ring
  have hnonneg : 0 <= (bias - 1) ^ 2 / bias := by positivity
  linarith

private theorem bias_cubic_argument_mem_Ici_four
    {bias : Real} (hpositive : 0 < bias) :
    (bias + bias⁻¹) ^ 2 ∈ Set.Ici (4 : Real) := by
  have hsum := bias_add_inv_ge_two hpositive
  let x : Real := bias + bias⁻¹
  have hsum' : 2 <= x := by simpa [x] using hsum
  change 4 <= x ^ 2
  have hproduct : 0 <=
      (x - 2) * (x + 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private theorem bias_sub_inv_neg {bias : Real}
    (hpositive : 0 < bias) (hlt_one : bias < 1) :
    bias - bias⁻¹ < 0 := by
  have hidentity : bias - bias⁻¹ = (bias ^ 2 - 1) / bias := by
    field_simp [hpositive.ne']
  have hsq_lt : bias ^ 2 < 1 := by
    have hmul : 0 < bias * (1 - bias) := mul_pos hpositive (sub_pos.mpr hlt_one)
    nlinarith
  rw [hidentity]
  exact div_neg_of_neg_of_pos (by linarith) hpositive

private theorem cubic_eq_zero_of_fixedPolynomial_root
    {bias : Real} (hpositive : 0 < bias) (hlt_one : bias < 1)
    (hroot : bk15FixedPolynomial bias = 0) :
    bk15FixedCubic ((bias + bias⁻¹) ^ 2) = 0 := by
  have hfactor := bk15FixedPolynomial_cubic_factor bias hpositive.ne'
  rw [hroot] at hfactor
  norm_num at hfactor
  exact hfactor.resolve_left
    (ne_of_lt (bias_sub_inv_neg hpositive hlt_one))

private theorem fixedPolynomial_root_unique_in_unitInterval
    {left right : Real} (hleft : 0 < left) (hleft_one : left < 1)
    (hright : 0 < right) (hright_one : right < 1)
    (hleft_root : bk15FixedPolynomial left = 0)
    (hright_root : bk15FixedPolynomial right = 0) :
    left = right := by
  have hleft_cubic :=
    cubic_eq_zero_of_fixedPolynomial_root hleft hleft_one hleft_root
  have hright_cubic :=
    cubic_eq_zero_of_fixedPolynomial_root hright hright_one hright_root
  have hleft_mem := bias_cubic_argument_mem_Ici_four hleft
  have hright_mem := bias_cubic_argument_mem_Ici_four hright
  have hargument : (left + left⁻¹) ^ 2 = (right + right⁻¹) ^ 2 := by
    apply (bk15FixedCubic_strictMonoOn.eq_iff_eq hleft_mem hright_mem).mp
    rw [hleft_cubic, hright_cubic]
  have hleft_sum_pos : 0 < left + left⁻¹ := by positivity
  have hright_sum_pos : 0 < right + right⁻¹ := by positivity
  have hsum : left + left⁻¹ = right + right⁻¹ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hargument with h | h
    · exact h
    · exfalso
      rw [h] at hleft_sum_pos
      linarith
  have hproduct : (left - right) * (left * right - 1) = 0 := by
    calc
      (left - right) * (left * right - 1) =
          left * right * ((left + left⁻¹) - (right + right⁻¹)) := by
            field_simp [hleft.ne', hright.ne']
            ring
      _ = 0 := by rw [hsum]; ring
  rcases mul_eq_zero.mp hproduct with heq | hunit
  · exact sub_eq_zero.mp heq
  · exfalso
    have hproduct_lt : left * right < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hleft.le hleft_one hright_one.le
    nlinarith

/-- The two exact rational bias endpoints corresponding to the required
epsilon bracket. -/
def bk15BiasUpper : Real := 35851 / 50000

def bk15BiasLower : Real := 35853 / 50000

theorem bk15BiasUpper_lt_lower : bk15BiasUpper < bk15BiasLower := by
  norm_num [bk15BiasUpper, bk15BiasLower]

theorem bk15FixedPolynomial_upper_neg : bk15FixedPolynomial bk15BiasUpper < 0 := by
  norm_num [bk15FixedPolynomial, bk15BiasUpper]

theorem bk15FixedPolynomial_lower_pos : 0 < bk15FixedPolynomial bk15BiasLower := by
  norm_num [bk15FixedPolynomial, bk15BiasLower]

private theorem exists_interior_bias_fixedPolynomial_root :
    ∃ bias, bk15BiasUpper < bias ∧ bias < bk15BiasLower ∧
      bk15FixedPolynomial bias = 0 := by
  have hcontinuous : Continuous bk15FixedPolynomial := by
    unfold bk15FixedPolynomial
    fun_prop
  have himage := intermediate_value_Icc bk15BiasUpper_lt_lower.le
    hcontinuous.continuousOn
      ⟨bk15FixedPolynomial_upper_neg.le,
        bk15FixedPolynomial_lower_pos.le⟩
  rcases himage with ⟨bias, hbias_mem, hbias_root⟩
  refine ⟨bias, ?_, ?_, hbias_root⟩
  · rcases hbias_mem with ⟨hupper, hlower⟩
    exact lt_of_le_of_ne hupper (by
      intro heq
      rw [← heq] at hbias_root
      linarith [bk15FixedPolynomial_upper_neg])
  · rcases hbias_mem with ⟨hupper, hlower⟩
    exact lt_of_le_of_ne hlower (by
      intro heq
      rw [heq] at hbias_root
      linarith [bk15FixedPolynomial_lower_pos])

private theorem existsUnique_interior_bias_fixedPolynomial_root :
    ∃! bias, 0 < bias ∧ bias < 1 ∧ bk15FixedPolynomial bias = 0 := by
  rcases exists_interior_bias_fixedPolynomial_root with
    ⟨bias, hupper, hlower, hroot⟩
  refine ⟨bias, ?_, ?_⟩
  · refine ⟨?_, ?_, hroot⟩
    · have : 0 < bk15BiasUpper := by norm_num [bk15BiasUpper]
      linarith
    · have : bk15BiasLower < 1 := by norm_num [bk15BiasLower]
      linarith
  · intro other hother
    have hbias_pos : 0 < bias := by
      have hendpoint : 0 < bk15BiasUpper := by
        norm_num [bk15BiasUpper]
      linarith
    have hbias_one : bias < 1 := by
      have hendpoint : bk15BiasLower < 1 := by
        norm_num [bk15BiasLower]
      linarith
    exact fixedPolynomial_root_unique_in_unitInterval
      (by exact hother.1) (by exact hother.2.1)
      hbias_pos hbias_one
      hother.2.2 hroot

/-- The uniquely proved nontrivial BK15 fixed-point bias. -/
noncomputable def bk15BiasStar : Real :=
  Classical.choose existsUnique_interior_bias_fixedPolynomial_root

theorem bk15BiasStar_pos : 0 < bk15BiasStar :=
  (Classical.choose_spec existsUnique_interior_bias_fixedPolynomial_root).1.1

theorem bk15BiasStar_lt_one : bk15BiasStar < 1 :=
  (Classical.choose_spec existsUnique_interior_bias_fixedPolynomial_root).1.2.1

theorem bk15FixedPolynomial_biasStar :
    bk15FixedPolynomial bk15BiasStar = 0 :=
  (Classical.choose_spec existsUnique_interior_bias_fixedPolynomial_root).1.2.2

private theorem bk15BiasStar_between_rational_endpoints :
    bk15BiasUpper < bk15BiasStar ∧ bk15BiasStar < bk15BiasLower := by
  rcases exists_interior_bias_fixedPolynomial_root with
    ⟨bias, hupper, hlower, hroot⟩
  have hbias_pos : 0 < bias := by
    have hendpoint : 0 < bk15BiasUpper := by
      norm_num [bk15BiasUpper]
    linarith
  have hbias_one : bias < 1 := by
    have hendpoint : bk15BiasLower < 1 := by
      norm_num [bk15BiasLower]
    linarith
  have heq : bias = bk15BiasStar :=
    fixedPolynomial_root_unique_in_unitInterval
      hbias_pos hbias_one bk15BiasStar_pos bk15BiasStar_lt_one
      hroot bk15FixedPolynomial_biasStar
  rw [heq] at hupper hlower
  exact ⟨hupper, hlower⟩

/-- The unique nontrivial physical error fixed point of the actual BK15
recurrence. -/
noncomputable def epsilonStar : Real := (1 - bk15BiasStar) / 2

theorem bk15Bias_epsilonStar : bk15Bias epsilonStar = bk15BiasStar := by
  unfold bk15Bias epsilonStar
  ring

theorem epsilonStar_pos : 0 < epsilonStar := by
  unfold epsilonStar
  linarith [bk15BiasStar_lt_one]

theorem epsilonStar_lt_half : epsilonStar < 1 / 2 := by
  unfold epsilonStar
  linarith [bk15BiasStar_pos]

theorem epsilonStar_rational_bracket :
    14147 / 100000 < epsilonStar ∧ epsilonStar < 14149 / 100000 := by
  have hbounds := bk15BiasStar_between_rational_endpoints
  unfold epsilonStar
  constructor
  · calc
      (14147 : Real) / 100000 = (1 - bk15BiasLower) / 2 := by
        norm_num [bk15BiasLower]
      _ < (1 - bk15BiasStar) / 2 := by linarith [hbounds.2]
  · calc
      (1 - bk15BiasStar) / 2 < (1 - bk15BiasUpper) / 2 := by
        linarith [hbounds.1]
      _ = (14149 : Real) / 100000 := by
        norm_num [bk15BiasUpper]

/-- The exact difference factor whose sign controls one recurrence step. -/
theorem bk15Recurrence_sub_input (epsilon : Real) :
    bk15Recurrence epsilon - epsilon =
      -(bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon)) /
        (2 * (1 + 15 * bk15Bias epsilon ^ 8)) := by
  have hdenom : 1 + 15 * bk15Bias epsilon ^ 8 ≠ 0 :=
    (bk15Recurrence_denominator_pos epsilon).ne'
  unfold bk15Recurrence bk15FixedPolynomial bk15Bias
  field_simp [hdenom]
  ring

theorem bk15Recurrence_eq_of_fixedPolynomial
    {epsilon : Real} (hroot : bk15FixedPolynomial (bk15Bias epsilon) = 0) :
    bk15Recurrence epsilon = epsilon := by
  have hsub := bk15Recurrence_sub_input epsilon
  rw [hroot] at hsub
  norm_num at hsub
  linarith

theorem bk15Recurrence_epsilonStar :
    bk15Recurrence epsilonStar = epsilonStar := by
  apply bk15Recurrence_eq_of_fixedPolynomial
  rw [bk15Bias_epsilonStar]
  exact bk15FixedPolynomial_biasStar

theorem bk15Recurrence_fixed_iff
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk15Recurrence epsilon = epsilon ↔
      epsilon = 0 ∨ epsilon = epsilonStar ∨ epsilon = 1 / 2 := by
  constructor
  · intro hfixed
    rcases eq_or_lt_of_le hzero with hepsilon | hpositive
    · exact Or.inl hepsilon.symm
    rcases eq_or_lt_of_le hhalf with hhalf_eq | hlt_half
    · exact Or.inr (Or.inr hhalf_eq)
    have hroot := bk15FixedPolynomial_eq_zero_of_interior_fixed
      hlt_half hfixed
    have hbias_pos : 0 < bk15Bias epsilon := by
      unfold bk15Bias
      linarith
    have hbias_one : bk15Bias epsilon < 1 := by
      unfold bk15Bias
      linarith
    have heq_bias : bk15Bias epsilon = bk15BiasStar :=
      fixedPolynomial_root_unique_in_unitInterval
        hbias_pos hbias_one bk15BiasStar_pos bk15BiasStar_lt_one
        hroot bk15FixedPolynomial_biasStar
    right; left
    rw [← bk15Bias_epsilonStar] at heq_bias
    unfold bk15Bias at heq_bias
    linarith
  · rintro (rfl | rfl | rfl)
    · exact bk15Recurrence_zero
    · exact bk15Recurrence_epsilonStar
    · exact bk15Recurrence_half

private theorem bias_add_inv_strictAnti_of_lt
    {smaller larger : Real}
    (hsmaller_pos : 0 < smaller) (hsmaller_one : smaller < 1)
    (hlarger_pos : 0 < larger) (hlarger_one : larger < 1)
    (hlt : smaller < larger) :
    larger + larger⁻¹ < smaller + smaller⁻¹ := by
  have hidentity :
      larger * smaller * ((larger + larger⁻¹) - (smaller + smaller⁻¹)) =
        (larger - smaller) * (larger * smaller - 1) := by
    field_simp [hsmaller_pos.ne', hlarger_pos.ne']
    ring
  have hproduct_lt : larger * smaller < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hlarger_pos.le hlarger_one hsmaller_one.le
  have hright_neg : (larger - smaller) * (larger * smaller - 1) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (by linarith)
  have hleft_neg :
      larger * smaller * ((larger + larger⁻¹) - (smaller + smaller⁻¹)) < 0 := by
    rw [hidentity]
    exact hright_neg
  exact sub_neg.mp <|
    neg_of_mul_neg_right hleft_neg (mul_pos hlarger_pos hsmaller_pos).le

private theorem fixedPolynomial_pos_of_biasStar_lt
    {bias : Real} (hstar_lt : bk15BiasStar < bias) (hbias_one : bias < 1) :
    0 < bk15FixedPolynomial bias := by
  have hbias_pos : 0 < bias := bk15BiasStar_pos.trans hstar_lt
  have hsum_lt :
      bias + bias⁻¹ < bk15BiasStar + bk15BiasStar⁻¹ :=
    bias_add_inv_strictAnti_of_lt
      bk15BiasStar_pos bk15BiasStar_lt_one hbias_pos hbias_one hstar_lt
  have hbias_sum_pos : 0 < bias + bias⁻¹ := by positivity
  have hstar_sum_pos : 0 < bk15BiasStar + bk15BiasStar⁻¹ := by
    exact add_pos bk15BiasStar_pos (inv_pos.mpr bk15BiasStar_pos)
  have hargument_lt :
      (bias + bias⁻¹) ^ 2 < (bk15BiasStar + bk15BiasStar⁻¹) ^ 2 :=
    (sq_lt_sq₀ hbias_sum_pos.le hstar_sum_pos.le).mpr hsum_lt
  have hbias_mem := bias_cubic_argument_mem_Ici_four hbias_pos
  have hstar_mem := bias_cubic_argument_mem_Ici_four bk15BiasStar_pos
  have hcubic_lt := bk15FixedCubic_strictMonoOn hbias_mem hstar_mem hargument_lt
  have hstar_cubic := cubic_eq_zero_of_fixedPolynomial_root
    bk15BiasStar_pos bk15BiasStar_lt_one bk15FixedPolynomial_biasStar
  have hcubic_neg : bk15FixedCubic ((bias + bias⁻¹) ^ 2) < 0 := by
    rw [hstar_cubic] at hcubic_lt
    exact hcubic_lt
  have hfactor := bk15FixedPolynomial_cubic_factor bias hbias_pos.ne'
  have hdiv_pos : 0 < bk15FixedPolynomial bias / bias ^ 7 := by
    rw [hfactor]
    exact mul_pos_of_neg_of_neg (bias_sub_inv_neg hbias_pos hbias_one) hcubic_neg
  exact (div_pos_iff_of_pos_right (pow_pos hbias_pos _)).mp hdiv_pos

private theorem bk15Recurrence_numerator_weight_sum (epsilon : Real) :
    1 - 15 * bk15Bias epsilon ^ 7 + 15 * bk15Bias epsilon ^ 8 -
        bk15Bias epsilon ^ 15 =
      32 *
        (35 * (epsilon ^ 3 * (1 - epsilon) ^ 12) +
          168 * (epsilon ^ 5 * (1 - epsilon) ^ 10) +
          435 * (epsilon ^ 7 * (1 - epsilon) ^ 8) +
          280 * (epsilon ^ 9 * (1 - epsilon) ^ 6) +
          105 * (epsilon ^ 11 * (1 - epsilon) ^ 4) + epsilon ^ 15) := by
  unfold bk15Bias
  ring

theorem bk15Recurrence_pos_of_pos_lt_epsilonStar
    {epsilon : Real} (hpositive : 0 < epsilon) (hthreshold : epsilon < epsilonStar) :
    0 < bk15Recurrence epsilon := by
  have hclean : 0 < 1 - epsilon := by
    linarith [hthreshold, epsilonStar_lt_half]
  let weightSum : Real :=
    35 * (epsilon ^ 3 * (1 - epsilon) ^ 12) +
      168 * (epsilon ^ 5 * (1 - epsilon) ^ 10) +
      435 * (epsilon ^ 7 * (1 - epsilon) ^ 8) +
      280 * (epsilon ^ 9 * (1 - epsilon) ^ 6) +
      105 * (epsilon ^ 11 * (1 - epsilon) ^ 4) + epsilon ^ 15
  have hfirst : 0 < 35 * (epsilon ^ 3 * (1 - epsilon) ^ 12) := by
    positivity
  have hrest : 0 <=
      168 * (epsilon ^ 5 * (1 - epsilon) ^ 10) +
        435 * (epsilon ^ 7 * (1 - epsilon) ^ 8) +
        280 * (epsilon ^ 9 * (1 - epsilon) ^ 6) +
        105 * (epsilon ^ 11 * (1 - epsilon) ^ 4) + epsilon ^ 15 := by
    positivity
  have hweightSum : 0 < weightSum := by
    dsimp [weightSum]
    linarith
  have hdenom := bk15Recurrence_scaled_denominator_pos epsilon
  unfold bk15Recurrence
  rw [bk15Recurrence_numerator_weight_sum]
  exact div_pos (mul_pos (by norm_num) hweightSum) hdenom

/-- Below the exact interior fixed point, an accepted BK15 recurrence step
strictly improves the error. -/
theorem bk15Recurrence_lt_input
    {epsilon : Real} (hpositive : 0 < epsilon) (hthreshold : epsilon < epsilonStar) :
    bk15Recurrence epsilon < epsilon := by
  have hbias_star_lt : bk15BiasStar < bk15Bias epsilon := by
    rw [← bk15Bias_epsilonStar]
    unfold bk15Bias
    linarith
  have hbias_one : bk15Bias epsilon < 1 := by
    unfold bk15Bias
    linarith
  have hpoly : 0 < bk15FixedPolynomial (bk15Bias epsilon) :=
    fixedPolynomial_pos_of_biasStar_lt hbias_star_lt hbias_one
  have hproduct : 0 < bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon) := by
    have hbias_pos : 0 < bk15Bias epsilon := bk15BiasStar_pos.trans hbias_star_lt
    positivity
  apply sub_neg.mp
  rw [bk15Recurrence_sub_input]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hproduct)
    (bk15Recurrence_scaled_denominator_pos epsilon)

/-! ## Iteration below the certified threshold -/

/-- The accepted-error coordinate after a finite number of recursive BK15
rounds. -/
def bk15Iteration (epsilon : Real) (rounds : Nat) : Real :=
  (bk15Recurrence^[rounds]) epsilon

@[simp] theorem bk15Iteration_zero (epsilon : Real) :
    bk15Iteration epsilon 0 = epsilon := rfl

theorem bk15Iteration_succ (epsilon : Real) (rounds : Nat) :
    bk15Iteration epsilon (rounds + 1) =
      bk15Recurrence (bk15Iteration epsilon rounds) := by
  rw [bk15Iteration, bk15Iteration, Function.iterate_succ_apply']

theorem bk15Iteration_pos_and_lt_epsilonStar
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    0 < bk15Iteration epsilon rounds ∧
      bk15Iteration epsilon rounds < epsilonStar := by
  induction rounds with
  | zero => exact ⟨hpositive, hthreshold⟩
  | succ rounds ih =>
      rw [bk15Iteration_succ]
      constructor
      · exact bk15Recurrence_pos_of_pos_lt_epsilonStar ih.1 ih.2
      · exact (bk15Recurrence_lt_input ih.1 ih.2).trans ih.2

theorem bk15Iteration_antitone
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) :
    Antitone (bk15Iteration epsilon) := by
  apply antitone_nat_of_succ_le
  intro rounds
  rw [bk15Iteration_succ]
  exact (bk15Recurrence_lt_input
    (bk15Iteration_pos_and_lt_epsilonStar epsilon hpositive hthreshold rounds).1
    (bk15Iteration_pos_and_lt_epsilonStar epsilon hpositive hthreshold rounds).2).le

private theorem bk15Recurrence_continuousAt (epsilon : Real) :
    ContinuousAt bk15Recurrence epsilon := by
  have hnumerator : ContinuousAt
      (fun input : Real =>
        1 - 15 * bk15Bias input ^ 7 + 15 * bk15Bias input ^ 8 -
          bk15Bias input ^ 15) epsilon := by
    unfold bk15Bias
    fun_prop
  have hdenominator : ContinuousAt
      (fun input : Real => 2 * (1 + 15 * bk15Bias input ^ 8)) epsilon := by
    unfold bk15Bias
    fun_prop
  unfold bk15Recurrence
  exact hnumerator.div hdenominator
    (bk15Recurrence_scaled_denominator_pos epsilon).ne'

/-- Below the exact threshold, recursive accepted BK15 errors converge to zero. -/
theorem bk15Iteration_tendsto_zero
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) :
    Filter.Tendsto (bk15Iteration epsilon) Filter.atTop (nhds 0) := by
  let sequence : Nat -> Real := bk15Iteration epsilon
  have hinvariant : ∀ rounds,
      0 < sequence rounds ∧ sequence rounds < epsilonStar := by
    intro rounds
    exact bk15Iteration_pos_and_lt_epsilonStar epsilon hpositive hthreshold rounds
  have hanti : Antitone sequence :=
    bk15Iteration_antitone epsilon hpositive hthreshold
  have hbdd : BddBelow (Set.range sequence) := by
    refine ⟨0, ?_⟩
    rintro value ⟨rounds, rfl⟩
    exact (hinvariant rounds).1.le
  let limit : Real := ⨅ rounds, sequence rounds
  have htendsto : Filter.Tendsto sequence Filter.atTop (nhds limit) := by
    exact tendsto_atTop_ciInf hanti hbdd
  have hlimit_nonneg : 0 <= limit := by
    exact le_ciInf fun rounds => (hinvariant rounds).1.le
  have hlimit_le_input : limit <= epsilon := by
    have hle : limit <= sequence 0 := ciInf_le hbdd 0
    simpa [limit, sequence] using hle
  have hlimit_half : limit <= 1 / 2 := by
    linarith [hlimit_le_input, hthreshold, epsilonStar_lt_half]
  have hcontinuous : ContinuousAt bk15Recurrence limit :=
    bk15Recurrence_continuousAt limit
  have hmap : Filter.Tendsto
      (fun rounds => bk15Recurrence (sequence rounds)) Filter.atTop
      (nhds (bk15Recurrence limit)) :=
    hcontinuous.tendsto.comp htendsto
  have hsucc_atTop : Filter.Tendsto (fun rounds : Nat => rounds + 1)
      Filter.atTop Filter.atTop := by
    exact (strictMono_nat_of_lt_succ fun rounds =>
      Nat.lt_succ_self (rounds + 1)).tendsto_atTop
  have hshift : Filter.Tendsto (fun rounds => sequence (rounds + 1))
      Filter.atTop (nhds limit) := htendsto.comp hsucc_atTop
  have hmap_shift : Filter.Tendsto (fun rounds => sequence (rounds + 1))
      Filter.atTop (nhds (bk15Recurrence limit)) := by
    simpa [sequence, bk15Iteration_succ] using hmap
  have hfixed : bk15Recurrence limit = limit :=
    tendsto_nhds_unique hmap_shift hshift
  have hlimit_zero : limit = 0 := by
    rcases (bk15Recurrence_fixed_iff limit hlimit_nonneg hlimit_half).mp hfixed with
      hzero_limit | hthreshold_limit | hhalf_limit
    · exact hzero_limit
    · exfalso
      rw [hthreshold_limit] at hlimit_le_input
      linarith
    · exfalso
      rw [hhalf_limit] at hlimit_le_input
      linarith [hthreshold, epsilonStar_lt_half]
  simpa [sequence, hlimit_zero] using htendsto

/-- Every positive target error is reached after finitely many accepted rounds. -/
theorem bk15Iteration_eventually_lt
    (epsilon target : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (htarget : 0 < target) :
    ∃ rounds : Nat, bk15Iteration epsilon rounds < target := by
  have htendsto := bk15Iteration_tendsto_zero epsilon hpositive hthreshold
  exact ((tendsto_order.mp htendsto).2 target htarget).exists

/-- The physical input parameter at a scheduled depth.  Its bounds are proved
from the recurrence invariant rather than assumed by the schedule. -/
noncomputable def bk15IterationEpsilon
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) : BK15Epsilon where
  epsilon := bk15Iteration epsilon rounds
  nonneg := (bk15Iteration_pos_and_lt_epsilonStar
    epsilon hpositive hthreshold rounds).1.le
  le_half := (bk15Iteration_pos_and_lt_epsilonStar
    epsilon hpositive hthreshold rounds).2.trans epsilonStar_lt_half |>.le

@[simp] theorem bk15IterationEpsilon_error
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    (bk15IterationEpsilon epsilon hpositive hthreshold rounds).epsilon =
      bk15Iteration epsilon rounds := rfl

/-- The actual accepted output selected at a scheduled depth. -/
noncomputable def bk15AcceptedLayer
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    DensityOperator QubitSpace :=
  (bk15Run (bk15IterationEpsilon epsilon hpositive hthreshold rounds)
    (bk15Iteration_pos_and_lt_epsilonStar
      epsilon hpositive hthreshold rounds).1).acceptedOutput

/-- Each scheduled layer is #707's actual normalized accepted BK15 output,
and its source-A error is the next genuine iterate. -/
theorem bk15AcceptedLayer_error_eq_iteration_succ
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    bk15OutputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
      aZeroDensity = bk15Iteration epsilon (rounds + 1) := by
  rw [bk15Iteration_succ]
  symm
  simpa [bk15AcceptedLayer] using
    bk15Recurrence_eq_actual_acceptedOutputError
      (bk15IterationEpsilon epsilon hpositive hthreshold rounds)
      (bk15Iteration_pos_and_lt_epsilonStar
        epsilon hpositive hthreshold rounds).1

/-- Dephasing the actual accepted output produces exactly the diagonal
resource required at the next scheduled depth.  This is the physical handoff
between consecutive selected accepted layers. -/
theorem bk15AcceptedLayer_dephased_eq_nextResource
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    aBasisDephasing.mapDensity
        (bk15AcceptedLayer epsilon hpositive hthreshold rounds) =
      diagonalAResource
        (bk15IterationEpsilon epsilon hpositive hthreshold (rounds + 1)) := by
  apply aBasisDephasing_mapDensity_eq_diagonalAResource
  change bk15Iteration epsilon (rounds + 1) =
    aInputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
  change bk15Iteration epsilon (rounds + 1) =
    bk15OutputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
      aZeroDensity
  exact (bk15AcceptedLayer_error_eq_iteration_succ
    epsilon hpositive hthreshold rounds).symm

/-! ## Cubic small-error coefficient -/

/-- The recurrence divided by the leading cubic power, with its removable
singularity at zero filled in by the polynomial expression. -/
def bk15CubicRatio (epsilon : Real) : Real :=
  16 *
      (35 * (1 - epsilon) ^ 12 +
        168 * (epsilon ^ 2 * (1 - epsilon) ^ 10) +
        435 * (epsilon ^ 4 * (1 - epsilon) ^ 8) +
        280 * (epsilon ^ 6 * (1 - epsilon) ^ 6) +
        105 * (epsilon ^ 8 * (1 - epsilon) ^ 4) + epsilon ^ 12) /
    (1 + 15 * bk15Bias epsilon ^ 8)

private theorem bk15Recurrence_div_cube_eq_cubicRatio
    {epsilon : Real} (hepsilon : epsilon ≠ 0) :
    bk15Recurrence epsilon / epsilon ^ 3 = bk15CubicRatio epsilon := by
  rw [bk15Recurrence, bk15Recurrence_numerator_weight_sum]
  unfold bk15CubicRatio
  field_simp [hepsilon,
    (bk15Recurrence_scaled_denominator_pos epsilon).ne']
  ring

private theorem bk15CubicRatio_continuousAt_zero :
    ContinuousAt bk15CubicRatio 0 := by
  have hnumerator : ContinuousAt
      (fun epsilon : Real =>
        16 *
          (35 * (1 - epsilon) ^ 12 +
            168 * (epsilon ^ 2 * (1 - epsilon) ^ 10) +
            435 * (epsilon ^ 4 * (1 - epsilon) ^ 8) +
            280 * (epsilon ^ 6 * (1 - epsilon) ^ 6) +
            105 * (epsilon ^ 8 * (1 - epsilon) ^ 4) + epsilon ^ 12)) 0 := by
    fun_prop
  have hdenominator : ContinuousAt
      (fun epsilon : Real => 1 + 15 * bk15Bias epsilon ^ 8) 0 := by
    unfold bk15Bias
    fun_prop
  unfold bk15CubicRatio
  exact hnumerator.div hdenominator (by norm_num [bk15Bias])

/-- The actual accepted-error recurrence has leading small-error coefficient
`35`, in the one-sided physical limit. -/
theorem bk15Recurrence_cubic_limit :
    Filter.Tendsto (fun epsilon : Real => bk15Recurrence epsilon / epsilon ^ 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 35) := by
  have hratio : Filter.Tendsto bk15CubicRatio
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 35) := by
    convert tendsto_nhdsWithin_of_tendsto_nhds
      bk15CubicRatio_continuousAt_zero.tendsto using 1;
      norm_num [bk15CubicRatio, bk15Bias]
  refine hratio.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  exact (bk15Recurrence_div_cube_eq_cubicRatio hepsilon.ne').symm

/-! ## H-fidelity entry criterion -/

/-- The source-A error coordinate induced by the repository's square-root
maximum H fidelity. -/
def bk15HInputError (rho : DensityOperator QubitSpace) : Real :=
  1 - hFidelity rho ^ 2

/-- The exact H-fidelity threshold corresponding to `epsilonStar`. -/
def FStar : Real := Real.sqrt (1 - epsilonStar)

private theorem one_sub_epsilonStar_pos : 0 < 1 - epsilonStar := by
  linarith [epsilonStar_pos, epsilonStar_lt_half]

theorem FStar_sq : FStar ^ 2 = 1 - epsilonStar := by
  unfold FStar
  rw [Real.sq_sqrt]
  exact one_sub_epsilonStar_pos.le

theorem FStar_nonneg : 0 <= FStar := by
  exact Real.sqrt_nonneg _

theorem FStar_pos : 0 < FStar := by
  unfold FStar
  exact Real.sqrt_pos.mpr one_sub_epsilonStar_pos

/-- A rational certificate around the exact square-root H-fidelity threshold. -/
theorem FStar_rational_bracket :
    463 / 500 < FStar ∧ FStar < 927 / 1000 := by
  constructor
  · have hsquare : (463 / 500 : Real) ^ 2 < 1 - epsilonStar := by
      linarith [epsilonStar_rational_bracket.2]
    nlinarith [FStar_sq, FStar_nonneg]
  · have hsquare : 1 - epsilonStar < (927 / 1000 : Real) ^ 2 := by
      linarith [epsilonStar_rational_bracket.1]
    nlinarith [FStar_sq, FStar_nonneg]

theorem bk15HInputError_nonneg (rho : DensityOperator QubitSpace) :
    0 <= bk15HInputError rho := by
  have hfidelity := hFidelity_mem_Icc rho
  unfold bk15HInputError
  have hfactor : 0 <= hFidelity rho * (1 - hFidelity rho) :=
    mul_nonneg hfidelity.1 (sub_nonneg.mpr hfidelity.2)
  nlinarith

/-- The strict H-fidelity criterion is precisely strong enough for the
certified source-A recurrence threshold. -/
theorem bk15HInputError_lt_epsilonStar_of_FStar_lt
    (rho : DensityOperator QubitSpace) (hfidelity : FStar < hFidelity rho) :
    bk15HInputError rho < epsilonStar := by
  have hfid := hFidelity_mem_Icc rho
  have hsquare : FStar ^ 2 < hFidelity rho ^ 2 :=
    (sq_lt_sq₀ FStar_nonneg hfid.1).mpr hfidelity
  rw [FStar_sq] at hsquare
  unfold bk15HInputError
  linarith

/-- The literal H-to-source-A transport identifies the analytic entry error
with the actual framed input's negative-A error. -/
theorem bk15HInputError_eq_sourceAFramedInput_error
    (rho : DensityOperator QubitSpace) :
    bk15HInputError rho = aInputError (sourceAFramedInput rho) := by
  simpa [bk15HInputError] using
    (sourceAFramedInput_error_eq_one_sub_hFidelity_sq rho).symm

/-- The strict source-domain parameter constructed from an H input.  This is
exactly #706's canonicalized input parameter, with its witnesses written in
the H-derived error coordinate used below. -/
noncomputable def bk15HInputEpsilon
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) : BK15Epsilon :=
  hCanonicalizedInputEpsilon rho
    (by
      change 0 < bk15HInputError rho
      exact hpositive)
    (by
      change bk15HInputError rho <= 1 / 2
      exact hleHalf)

theorem bk15HInputEpsilon_error
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    (bk15HInputEpsilon rho hpositive hleHalf).epsilon = bk15HInputError rho :=
  rfl

theorem bk15HInputEpsilon_pos
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    0 < (bk15HInputEpsilon rho hpositive hleHalf).epsilon := by
  change 0 < bk15HInputError rho
  exact hpositive

/-- The same H input, after the real canonicalization, source-frame transport,
and dephasing route, is exactly the diagonal A resource used by the concrete
BK15 run. -/
theorem bk15HInput_dephased_eq_diagonalAResource
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    hCanonicalizedDephasedInput rho =
      diagonalAResource (bk15HInputEpsilon rho hpositive hleHalf) := by
  simpa [bk15HInputEpsilon] using
    hCanonicalizedDephasedInput_eq_diagonalAResource rho
      (by
        change 0 < bk15HInputError rho
        exact hpositive)
      (by
        change bk15HInputError rho <= 1 / 2
        exact hleHalf)

/-! ## Semantic finite accepted-run schedules -/

/-- A finite selected BK15 execution tree.  Leaves store the original
canonical H-frame resource density.  Each internal node stores its fifteen
selected child executions and the actual normalized accepted BK15 density at
that node; validity is proved separately below rather than stored as a field. -/
inductive BK15SemanticSchedule (rho : DensityOperator QubitSpace) : Nat -> Type
  | leaf (resource : DensityOperator QubitSpace) : BK15SemanticSchedule rho 0
  | accepted {depth : Nat}
      (children : Fin 15 -> BK15SemanticSchedule rho depth)
      (acceptedOutput : DensityOperator QubitSpace) :
      BK15SemanticSchedule rho (depth + 1)

namespace BK15SemanticSchedule

/-- Number of original H-derived resources consumed by a semantic schedule. -/
def leafCount {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK15SemanticSchedule rho depth -> Nat
  | _, .leaf _ => 1
  | _, .accepted children _ => Finset.univ.sum fun site => leafCount (children site)

/-- The source-A density available at the root of a semantic schedule.  A leaf
is transported from its stored H frame; an internal node exposes its actual
accepted BK15 output. -/
noncomputable def rootOutput {rho : DensityOperator QubitSpace} :
    {depth : Nat} -> BK15SemanticSchedule rho depth -> DensityOperator QubitSpace
  | _, .leaf resource => sourceA0Transport.conjDensity resource
  | _, .accepted _ acceptedOutput => acceptedOutput

/-- The fifteen physical resources supplied to an internal schedule node are
the A-basis dephasings of its fifteen child-root outputs. -/
noncomputable def rootInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK15SemanticSchedule rho (depth + 1)) :
    ResourceInput 15 QubitSpace :=
  match schedule with
  | .accepted children _ => fun site =>
      aBasisDephasing.mapDensity (rootOutput (children site))

/-- The literal BK15 tensor preparation of a semantic node's derived inputs. -/
noncomputable def preparedInput {rho : DensityOperator QubitSpace} {depth : Nat}
    (schedule : BK15SemanticSchedule rho (depth + 1)) :
    DensityOperator BK15Register :=
  bk15PrepareInput (rootInput schedule)

end BK15SemanticSchedule

/-- The complete depth-`rounds` semantic schedule: every leaf stores the
original canonical H resource, and every internal node records the actual
accepted BK15 output at its recurrence depth. -/
noncomputable def bk15CompleteSemanticSchedule
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) :
    (rounds : Nat) -> BK15SemanticSchedule rho rounds
  | 0 => .leaf (hCanonicalizedInput rho)
  | depth + 1 => .accepted
      (fun _ => bk15CompleteSemanticSchedule rho hpositive hthreshold depth)
      (bk15AcceptedLayer (bk15HInputError rho) hpositive hthreshold depth)

/-- A complete semantic depth-`rounds` schedule consumes exactly `15 ^ rounds`
original H-derived resource leaves. -/
theorem bk15SemanticSchedule_leafCount
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    BK15SemanticSchedule.leafCount
        (bk15CompleteSemanticSchedule rho hpositive hthreshold rounds) =
      15 ^ rounds := by
  induction rounds with
  | zero => rfl
  | succ depth ih =>
      simp [bk15CompleteSemanticSchedule, BK15SemanticSchedule.leafCount, ih,
        Nat.pow_succ, Nat.mul_comm]

private theorem bk15HInputEpsilon_eq_bk15IterationEpsilon_zero
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) :
    bk15HInputEpsilon rho hpositive (hthreshold.trans epsilonStar_lt_half).le =
      bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold 0 := by
  rfl

/-- Dephasing the root of a complete semantic schedule gives the exact
diagonal A resource at the corresponding recurrence depth.  The base case is
the literal H-to-A transport; every successor uses the actual accepted layer
handoff. -/
theorem bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    aBasisDephasing.mapDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold rounds)) =
      diagonalAResource
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold rounds) := by
  cases rounds with
  | zero =>
      rw [← bk15HInputEpsilon_eq_bk15IterationEpsilon_zero rho hpositive hthreshold]
      simpa [BK15SemanticSchedule.rootOutput, bk15CompleteSemanticSchedule,
        hCanonicalizedDephasedInput, sourceAFramedInput] using
        bk15HInput_dephased_eq_diagonalAResource rho hpositive
          (hthreshold.trans epsilonStar_lt_half).le
  | succ depth =>
      simpa [BK15SemanticSchedule.rootOutput, bk15CompleteSemanticSchedule] using
        bk15AcceptedLayer_dephased_eq_nextResource
          (bk15HInputError rho) hpositive hthreshold depth

/-- Each semantic internal node supplies the same fifteen resources as its
actual BK15 run at the matching recurrence depth. -/
theorem bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput := by
  funext site
  change aBasisDephasing.mapDensity
      (BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold depth)) =
    diagonalAResource
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
  exact bk15SemanticSchedule_rootOutput_dephased_eq_iterationResource
    rho hpositive hthreshold depth

/-- The matching concrete BK15 run consumes exactly the fifteen derived
resources stored at every semantic internal node. -/
theorem bk15SemanticSchedule_root_resourceCount
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    (bk15Run
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
      (bk15Iteration_pos_and_lt_epsilonStar
        (bk15HInputError rho) hpositive hthreshold depth).1).resourceCount = 15 := by
  exact bk15Run_resourceCount _ _

/-- The prepared tensor state of a semantic node is exactly the prepared
input used by its matching actual BK15 run. -/
theorem bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.preparedInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
        ((bk15Run
          (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
          (bk15Iteration_pos_and_lt_epsilonStar
            (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) := by
  change bk15PrepareInput
      (BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) =
    bk15PrepareInput
      ((bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput)
  rw [bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput
    rho hpositive hthreshold depth]

/-- The root density stored by a complete semantic internal node is the actual
normalized accepted output of its matching BK15 run. -/
theorem bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput := by
  rfl

/-- A parent semantic node obtains each resource by dephasing the selected
root output of the corresponding complete child schedule. -/
theorem bk15SemanticSchedule_recursive_handoff
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar)
    (depth : Nat) (site : Fin 15) :
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 2)) site =
      aBasisDephasing.mapDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) := by
  rfl

/-- The concrete run realization exposed by a semantic internal node.  This
is a proved interface, not a property stored in the schedule data. -/
theorem bk15SemanticSchedule_realizesRun
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat) :
    (bk15Run
      (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
      (bk15Iteration_pos_and_lt_epsilonStar
        (bk15HInputError rho) hpositive hthreshold depth).1).resourceCount = 15 ∧
    BK15SemanticSchedule.rootInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
    BK15SemanticSchedule.preparedInput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
        ((bk15Run
          (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
          (bk15Iteration_pos_and_lt_epsilonStar
            (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
    BK15SemanticSchedule.rootOutput
        (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
      (bk15Run
        (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
        (bk15Iteration_pos_and_lt_epsilonStar
          (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput := by
  exact ⟨bk15SemanticSchedule_root_resourceCount rho hpositive hthreshold depth,
    bk15SemanticSchedule_rootInput_eq_bk15Run_noisyInput rho hpositive hthreshold depth,
    bk15SemanticSchedule_preparedInput_eq_bk15Run_preparedInput
      rho hpositive hthreshold depth,
    bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
      rho hpositive hthreshold depth⟩

/-- On the strict H branch, the first selected accepted execution is the
actual #707 BK15 run and has the certified recurrence error. -/
theorem bk15HInput_actualAccepted_error
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    bk15Recurrence (bk15HInputError rho) =
      bk15OutputError
        (bk15Run (bk15HInputEpsilon rho hpositive hleHalf)
          (bk15HInputEpsilon_pos rho hpositive hleHalf)).acceptedOutput
        aZeroDensity := by
  exact bk15Recurrence_eq_actual_acceptedOutputError
      (bk15HInputEpsilon rho hpositive hleHalf)
      (bk15HInputEpsilon_pos rho hpositive hleHalf)

/-- Return a selected actual accepted source-A output to the H frame by the
inverse of the literal source-A transport. -/
noncomputable def bk15AcceptedLayerHOutput
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    DensityOperator QubitSpace :=
  sourceA0Transport.symm.conjDensity
    (bk15AcceptedLayer epsilon hpositive hthreshold rounds)

private theorem sourceA0Transport_symm_conj_aPositive :
    sourceA0Transport.symm.conjOperator (aBasisProjector .positive) =
      hProjector hReference := by
  calc
    sourceA0Transport.symm.conjOperator (aBasisProjector .positive) =
        sourceA0Transport.symm.conjOperator
          (sourceA0Transport.conjOperator (hProjector hReference)) := by
            rw [sourceA0Transport_conj_hReference_projector]
    _ = hProjector hReference :=
      sourceA0Transport.symm_conjOperator_conjOperator _

/-- The inverse transport makes the reference-H squared overlap of the
returned density exactly the positive-A overlap of the actual accepted output. -/
theorem sourceAReturnedH_referenceSquaredOverlap
    (sigma : DensityOperator QubitSpace) :
    projectionSquaredOverlap (hProjector hReference)
        (sourceA0Transport.symm.conjDensity sigma) =
      aInputSquaredOverlap sigma := by
  unfold aInputSquaredOverlap
  calc
    projectionSquaredOverlap (hProjector hReference)
        (sourceA0Transport.symm.conjDensity sigma) =
      projectionSquaredOverlap
        (sourceA0Transport.symm.conjOperator (aBasisProjector .positive))
        (sourceA0Transport.symm.conjDensity sigma) := by
          rw [sourceA0Transport_symm_conj_aPositive]
    _ = projectionSquaredOverlap (aBasisProjector .positive) sigma :=
      projectionSquaredOverlap_conjDensity sourceA0Transport.symm
        (aBasisProjector .positive) sigma

/-- Any source-A density, transported back by the inverse source frame, has
H-infidelity no greater than its negative-A error. -/
theorem sourceAReturnedHInfidelity_le_aInputError
    (sigma : DensityOperator QubitSpace) :
    1 - hFidelity (sourceA0Transport.symm.conjDensity sigma) ^ 2 <=
      aInputError sigma := by
  let returned : DensityOperator QubitSpace :=
    sourceA0Transport.symm.conjDensity sigma
  have href_le : hDirectionFidelity returned hReference <= hFidelity returned := by
    unfold hFidelity
    exact Finset.le_sup' (hDirectionFidelity returned)
      (Finset.mem_univ hReference)
  have hdir_nonneg : 0 <= hDirectionFidelity returned hReference :=
    (hDirectionFidelity_mem_Icc returned hReference).1
  have hfidelity_nonneg : 0 <= hFidelity returned :=
    (hFidelity_mem_Icc returned).1
  have hsquare : hDirectionFidelity returned hReference ^ 2 <=
      hFidelity returned ^ 2 := by
    have hfactor : 0 <=
        (hFidelity returned - hDirectionFidelity returned hReference) *
          (hFidelity returned + hDirectionFidelity returned hReference) :=
      mul_nonneg (sub_nonneg.mpr href_le)
        (add_nonneg hfidelity_nonneg hdir_nonneg)
    nlinarith
  have hoverlap := sourceAReturnedH_referenceSquaredOverlap sigma
  have hprojection_nonneg : 0 <=
      projectionSquaredOverlap (hProjector hReference) returned :=
    projectionSquaredOverlap_nonneg (hProjector hReference) returned
      (hProjector_isSymmetricProjection hReference)
  have hdirection_sq : hDirectionFidelity returned hReference ^ 2 =
      projectionSquaredOverlap (hProjector hReference) returned := by
    unfold hDirectionFidelity projectionFidelity
    rw [Real.sq_sqrt]
    exact hprojection_nonneg
  unfold aInputError
  rw [← hoverlap]
  nlinarith

/-- The genuine returned H density of an actual scheduled accepted layer has
H-infidelity bounded by the next accepted-error iterate. -/
theorem bk15AcceptedLayerHInfidelity_le_iteration_succ
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) (rounds : Nat) :
    1 - hFidelity
        (bk15AcceptedLayerHOutput epsilon hpositive hthreshold rounds) ^ 2 <=
      bk15Iteration epsilon (rounds + 1) := by
  calc
    1 - hFidelity
        (bk15AcceptedLayerHOutput epsilon hpositive hthreshold rounds) ^ 2 <=
        bk15OutputError (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
          aZeroDensity := by
            simpa [bk15AcceptedLayerHOutput, bk15OutputError] using
              sourceAReturnedHInfidelity_le_aInputError
                (bk15AcceptedLayer epsilon hpositive hthreshold rounds)
    _ = bk15Iteration epsilon (rounds + 1) :=
      bk15AcceptedLayer_error_eq_iteration_succ
        epsilon hpositive hthreshold rounds

/-- The raw zero-error endpoint is ideal under the complete decoded operation;
this is deliberately separate from normalized accepted/rejected branches. -/
theorem bk15RawZeroEndpoint_is_ideal :
    decodedOperation.mapDensity (rawInput zeroEpsilon) = aZeroDensity := by
  exact decodedOperation_zeroEpsilon

/-- The physical H-frame density returned by the raw ideal endpoint. -/
noncomputable def bk15IdealReturnedHOutput : DensityOperator QubitSpace :=
  sourceA0Transport.symm.conjDensity
    (decodedOperation.mapDensity (rawInput zeroEpsilon))

private theorem bk15IdealReturnedHOutput_infidelity_zero :
    1 - hFidelity bk15IdealReturnedHOutput ^ 2 = 0 := by
  have hbound := sourceAReturnedHInfidelity_le_aInputError
    (decodedOperation.mapDensity (rawInput zeroEpsilon))
  have hsource_zero :
      aInputError (decodedOperation.mapDensity (rawInput zeroEpsilon)) = 0 := by
    simpa [bk15OutputError] using zeroEpsilon_decoded_output_error
  have hle : 1 - hFidelity bk15IdealReturnedHOutput ^ 2 <= 0 := by
    simpa [bk15IdealReturnedHOutput, hsource_zero] using hbound
  have hfidelity := hFidelity_mem_Icc bk15IdealReturnedHOutput
  have hfactor : 0 <= hFidelity bk15IdealReturnedHOutput *
      (1 - hFidelity bk15IdealReturnedHOutput) :=
    mul_nonneg hfidelity.1 (sub_nonneg.mpr hfidelity.2)
  nlinarith

/-- The returned H density for a finite selected accepted schedule.  On the
strict branch, every successor depth is literally the inverse-frame transport
of the semantic schedule's actual root accepted density.  The non-strict
branch is the separately proved raw ideal endpoint only at zero; other
out-of-domain inputs retain their canonicalized physical density. -/
noncomputable def bk15AcceptedRunHOutput
    (rho : DensityOperator QubitSpace) (rounds : Nat) :
    DensityOperator QubitSpace :=
  if hstrict : 0 < bk15HInputError rho ∧ bk15HInputError rho < epsilonStar then
    match rounds with
    | 0 => hCanonicalizedInput rho
    | depth + 1 => sourceA0Transport.symm.conjDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hstrict.1 hstrict.2 (depth + 1)))
  else if bk15HInputError rho = 0 then bk15IdealReturnedHOutput
  else hCanonicalizedInput rho

/-- The actual returned H-infidelity of a finite selected accepted schedule. -/
def bk15AcceptedRunHInfidelity
    (rho : DensityOperator QubitSpace) (rounds : Nat) : Real :=
  1 - hFidelity (bk15AcceptedRunHOutput rho rounds) ^ 2

/-- The strict returned H output is the inverse transport of the semantic
schedule's actual root accepted density, rather than a detached scalar layer. -/
theorem bk15AcceptedRunHOutput_succ_eq_semanticSchedule
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    bk15AcceptedRunHOutput rho (rounds + 1) =
      sourceA0Transport.symm.conjDensity
        (BK15SemanticSchedule.rootOutput
          (bk15CompleteSemanticSchedule rho hpositive hthreshold (rounds + 1))) := by
  have hstrict : 0 < bk15HInputError rho ∧
      bk15HInputError rho < epsilonStar := ⟨hpositive, hthreshold⟩
  simp [bk15AcceptedRunHOutput, hstrict]

private theorem bk15AcceptedRunHInfidelity_succ_le_iteration
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    bk15AcceptedRunHInfidelity rho (rounds + 1) <=
      bk15Iteration (bk15HInputError rho) (rounds + 1) := by
  rw [bk15AcceptedRunHInfidelity, bk15AcceptedRunHOutput_succ_eq_semanticSchedule
    rho hpositive hthreshold]
  rw [bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
    rho hpositive hthreshold rounds]
  exact bk15AcceptedLayerHInfidelity_le_iteration_succ
    (bk15HInputError rho) hpositive hthreshold rounds

private theorem bk15AcceptedRunHInfidelity_ideal
    (rho : DensityOperator QubitSpace)
    (hzero : bk15HInputError rho = 0) (rounds : Nat) :
    bk15AcceptedRunHInfidelity rho rounds = 0 := by
  have hnot_strict : ¬ (0 < bk15HInputError rho ∧
      bk15HInputError rho < epsilonStar) := by
    rintro ⟨hpositive, _⟩
    linarith
  unfold bk15AcceptedRunHInfidelity
  rw [bk15AcceptedRunHOutput, dif_neg hnot_strict]
  rw [if_pos hzero]
  exact bk15IdealReturnedHOutput_infidelity_zero

/-- The strict H branch supplies the real input handoff and actual first
accepted layer before returning a finite physical H-output witness with its
semantic schedule, actual run realization, and exact resource count. -/
private theorem bk15HfidelityDistillation_strict
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar)
    (delta : Real) (hdelta : 0 < delta) :
    hCanonicalizedDephasedInput rho =
        diagonalAResource
          (bk15HInputEpsilon rho hpositive
            (hthreshold.trans epsilonStar_lt_half).le) ∧
      bk15Recurrence (bk15HInputError rho) =
        bk15OutputError
          (bk15Run
            (bk15HInputEpsilon rho hpositive
              (hthreshold.trans epsilonStar_lt_half).le)
            (bk15HInputEpsilon_pos rho hpositive
            (hthreshold.trans epsilonStar_lt_half).le)).acceptedOutput
          aZeroDensity ∧
      ∃ depth : Nat,
        bk15AcceptedRunHInfidelity rho (depth + 1) < delta ∧
        BK15SemanticSchedule.leafCount
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          15 ^ (depth + 1) ∧
        BK15SemanticSchedule.rootInput
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          (bk15Run
            (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
            (bk15Iteration_pos_and_lt_epsilonStar
              (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
        BK15SemanticSchedule.preparedInput
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          (bk15Run
            (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
            (bk15Iteration_pos_and_lt_epsilonStar
              (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
            ((bk15Run
              (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
              (bk15Iteration_pos_and_lt_epsilonStar
                (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
        BK15SemanticSchedule.rootOutput
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          (bk15Run
            (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
            (bk15Iteration_pos_and_lt_epsilonStar
              (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
        bk15AcceptedRunHOutput rho (depth + 1) =
          sourceA0Transport.symm.conjDensity
            (BK15SemanticSchedule.rootOutput
              (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) := by
  have hhalf : bk15HInputError rho <= 1 / 2 :=
    (hthreshold.trans epsilonStar_lt_half).le
  refine ⟨bk15HInput_dephased_eq_diagonalAResource rho hpositive hhalf,
    bk15HInput_actualAccepted_error rho hpositive hhalf, ?_⟩
  rcases bk15Iteration_eventually_lt (bk15HInputError rho) delta
      hpositive hthreshold hdelta with ⟨depth, hdepth⟩
  have hrealization :=
    bk15SemanticSchedule_realizesRun rho hpositive hthreshold depth
  refine ⟨depth, ?_, bk15SemanticSchedule_leafCount rho hpositive hthreshold
    (depth + 1), hrealization.2.1, hrealization.2.2.1,
    hrealization.2.2.2, ?_⟩
  · calc
      bk15AcceptedRunHInfidelity rho (depth + 1) <=
          bk15Iteration (bk15HInputError rho) (depth + 1) :=
        bk15AcceptedRunHInfidelity_succ_le_iteration rho hpositive hthreshold depth
      _ <= bk15Iteration (bk15HInputError rho) depth :=
        bk15Iteration_antitone (bk15HInputError rho) hpositive hthreshold
          (Nat.le_succ depth)
      _ < delta := hdepth
  · exact bk15AcceptedRunHOutput_succ_eq_semanticSchedule
      rho hpositive hthreshold depth

/-- Any input above `FStar` has either the separately proved raw ideal endpoint
or a finite semantic selected-accepted BK15 schedule.  In the strict branch,
the witness exposes the exact `15^k` leaf count, derived resource input,
prepared tensor input, actual accepted root, and returned H density; it makes
no retry-cost, yield, or probability claim. -/
theorem bk15HfidelityDistillation
    (rho : DensityOperator QubitSpace)
    (hfidelity : FStar < hFidelity rho) (delta : Real) (hdelta : 0 < delta) :
    ∃ rounds : Nat,
      bk15AcceptedRunHInfidelity rho rounds < delta ∧
        (bk15HInputError rho = 0 ∨
          ∃ (hpositive : 0 < bk15HInputError rho)
            (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat),
            rounds = depth + 1 ∧
            BK15SemanticSchedule.leafCount
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              15 ^ (depth + 1) ∧
            BK15SemanticSchedule.rootInput
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              (bk15Run
                (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                (bk15Iteration_pos_and_lt_epsilonStar
                  (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
            BK15SemanticSchedule.preparedInput
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              (bk15Run
                (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                (bk15Iteration_pos_and_lt_epsilonStar
                  (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
                ((bk15Run
                  (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                  (bk15Iteration_pos_and_lt_epsilonStar
                    (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
            BK15SemanticSchedule.rootOutput
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              (bk15Run
                (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                (bk15Iteration_pos_and_lt_epsilonStar
                  (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
            bk15AcceptedRunHOutput rho (depth + 1) =
              sourceA0Transport.symm.conjDensity
                (BK15SemanticSchedule.rootOutput
                  (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)))) := by
  have hthreshold : bk15HInputError rho < epsilonStar :=
    bk15HInputError_lt_epsilonStar_of_FStar_lt rho hfidelity
  by_cases hzero : bk15HInputError rho = 0
  · refine ⟨0, ?_, Or.inl hzero⟩
    rw [bk15AcceptedRunHInfidelity_ideal rho hzero]
    exact hdelta
  · have hpositive : 0 < bk15HInputError rho :=
      lt_of_le_of_ne (bk15HInputError_nonneg rho) (Ne.symm hzero)
    rcases bk15HfidelityDistillation_strict rho hpositive hthreshold delta hdelta with
      ⟨_, _, depth, hinfidelity, hleafCount, hinput, hprepared, houtput, hreturned⟩
    exact ⟨depth + 1, hinfidelity,
      Or.inr ⟨hpositive, hthreshold, depth, rfl, hleafCount, hinput, hprepared,
        houtput, hreturned⟩⟩

end Threshold
end BK15
end Distillation
end QEC

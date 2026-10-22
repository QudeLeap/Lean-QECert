import QEC.Coding.AlgebraicGeometry.Towers.ExplicitGarciaStichtenothTower

/-!
# The multiplication-code divisor on the explicit normal-closure family

The divisor is exactly `floor ((16 alpha - 2) / 3) A` from
[Ngu24, Theorem: AG multiplication family]. Its coefficient and degree
estimates use the actual fibre degrees and intrinsic genus already proved
for the normal closure. No rate, distance or asymptotic property is assumed.
-/

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- The integer floor coefficient in the source's chosen divisor. -/
def f256MultiplicationCoefficient (i : ℕ) : ℤ :=
  (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) / 3

/-- The actual source divisor, supported on the zero fibre. -/
def f256MultiplicationDivisor (i : ℕ) :
    Divisor (GlobalPlace F256 (f256GarciaStichtenothField i)) :=
  f256MultiplicationCoefficient i • f256GarciaStichtenothDivisorA i

theorem f256MultiplicationCoefficient_lower (i : ℕ) :
    5 * (f256GarciaStichtenothAlpha i : ℤ) ≤ f256MultiplicationCoefficient i := by
  have h := f256GarciaStichtenothAlpha_two_le i
  unfold f256MultiplicationCoefficient
  omega

theorem f256MultiplicationCoefficient_upper (i : ℕ) :
    3 * f256MultiplicationCoefficient i ≤ 16 * (f256GarciaStichtenothAlpha i : ℤ) - 2 := by
  unfold f256MultiplicationCoefficient
  omega

theorem f256MultiplicationCoefficient_pos (i : ℕ) :
    0 < f256MultiplicationCoefficient i := by
  have h := f256MultiplicationCoefficient_lower i
  have hα := f256GarciaStichtenothAlpha_two_le i
  omega

theorem f256MultiplicationDivisor_nonnegative (i : ℕ) :
    0 ≤ f256MultiplicationDivisor i := by
  intro P
  change 0 ≤ f256MultiplicationCoefficient i * f256GarciaStichtenothDivisorA i P
  exact mul_nonneg (le_of_lt (f256MultiplicationCoefficient_pos i))
    (f256GarciaStichtenothDivisorA_nonnegative i P)

theorem f256GarciaStichtenothDivisorA_selected_eq_zero (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) :
    f256GarciaStichtenothDivisorA i (f256GarciaStichtenothSelectedPlace i j) = 0 := by
  classical
  by_contra h
  have hA := Finsupp.mem_support_iff.mpr h
  have hD : f256GarciaStichtenothSelectedPlace i j ∈
      (f256GarciaStichtenothDivisorD i).support := by
    apply Finsupp.mem_support_iff.mpr
    change sourceGaloisClosureSelectedDivisor (i + 2)
      (sourceGaloisClosureSelectedRationalPlace (i + 2) j).place ≠ 0
    erw [sourceGaloisClosureSelectedDivisor_apply]
    norm_num
  exact Finset.disjoint_left.mp (f256GarciaStichtenothDivisorA_support_disjoint_D i) hA hD

theorem f256MultiplicationDivisor_selected_eq_zero (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) :
    f256MultiplicationDivisor i (f256GarciaStichtenothSelectedPlace i j) = 0 := by
  change f256MultiplicationCoefficient i *
    f256GarciaStichtenothDivisorA i (f256GarciaStichtenothSelectedPlace i j) = 0
  rw [f256GarciaStichtenothDivisorA_selected_eq_zero, mul_zero]

/-- The pointwise divisor inequality used in the actual residue pairing. -/
theorem three_mul_f256MultiplicationDivisor_le (i : ℕ) :
    (3 : ℤ) • f256MultiplicationDivisor i ≤
      f256GarciaStichtenothCanonicalDivisor i + f256GarciaStichtenothDivisorD i := by
  rw [f256GarciaStichtenothCanonicalDivisor_eq, sub_add_cancel]
  intro P
  change 3 * (f256MultiplicationCoefficient i * f256GarciaStichtenothDivisorA i P) ≤
    (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) * f256GarciaStichtenothDivisorA i P +
      ((f256GarciaStichtenothBeta i : ℤ) - 2) * f256GarciaStichtenothDivisorB i P
  have hA := f256GarciaStichtenothDivisorA_nonnegative i P
  have hB := f256GarciaStichtenothDivisorB_nonnegative i P
  have hβ : (0 : ℤ) ≤ (f256GarciaStichtenothBeta i : ℤ) - 2 := by
    have h := f256GarciaStichtenothBeta_two_le i
    omega
  have hs := mul_le_mul_of_nonneg_right (f256MultiplicationCoefficient_upper i) hA
  have hb := mul_nonneg hβ hB
  nlinarith

theorem f256MultiplicationDivisor_degree (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) =
      f256MultiplicationCoefficient i *
        Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) := by
  have h := (Divisor.degreeHom GlobalPlace.residueDegree).map_zsmul
    (f256MultiplicationCoefficient i) (f256GarciaStichtenothDivisorA i)
  simp only [zsmul_eq_mul] at h
  exact h

/-- Denominator-free genus identity; the two subtracted terms are genuine
fibre degrees, not assumed bounds on a genus parameter. -/
theorem f256GarciaStichtenothGenus_fibre_identity (i : ℕ) :
    15 * ((f256GarciaStichtenothGenus i : ℤ) - 1 +
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) +
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i)) =
        f256GarciaStichtenothLength i := by
  have hg := sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees (i + 2)
  have hn : (15 : ℤ) * (sourceGaloisWRelativeDegree (i + 2) : ℤ) =
      f256GarciaStichtenothLength i := by
    exact_mod_cast sourceGaloisWRelativeDegree_mul_fifteen (i + 2)
  change (f256GarciaStichtenothGenus i : ℤ) = 1 +
    (sourceGaloisWRelativeDegree (i + 2) : ℤ) -
    Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) -
    Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) at hg
  omega

private theorem fifteen_mul_alpha_fibre_degree (i : ℕ) :
    15 * ((f256GarciaStichtenothAlpha i : ℤ) *
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i)) =
        f256GarciaStichtenothLength i := by
  rw [f256GarciaStichtenothAlpha_mul_degree_divisorA]
  exact_mod_cast Nat.mul_div_cancel' (f256GarciaStichtenothLength_fifteen_dvd i)

theorem f256MultiplicationDivisor_degree_lower (i : ℕ) :
    5 * (f256GarciaStichtenothLength i : ℤ) ≤
      15 * Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) := by
  rw [f256MultiplicationDivisor_degree]
  have h := mul_le_mul_of_nonneg_right (f256MultiplicationCoefficient_lower i)
    (le_of_lt (f256GarciaStichtenothDivisorA_degree_pos i))
  have hA := fifteen_mul_alpha_fibre_degree i
  nlinarith

theorem f256MultiplicationDivisor_degree_upper (i : ℕ) :
    45 * Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) ≤
      16 * (f256GarciaStichtenothLength i : ℤ) := by
  rw [f256MultiplicationDivisor_degree]
  have h := mul_le_mul_of_nonneg_right (f256MultiplicationCoefficient_upper i)
    (le_of_lt (f256GarciaStichtenothDivisorA_degree_pos i))
  have hA := fifteen_mul_alpha_fibre_degree i
  have hp := f256GarciaStichtenothDivisorA_degree_pos i
  nlinarith

theorem f256MultiplicationDivisor_degree_lt_length (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) <
      f256GarciaStichtenothLength i := by
  have hu := f256MultiplicationDivisor_degree_upper i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  omega

theorem f256MultiplicationDivisor_dimension_numerator (i : ℕ) :
    (f256GarciaStichtenothLength i : ℤ) ≤
      4 * (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 1 -
        f256GarciaStichtenothGenus i) := by
  have hl := f256MultiplicationDivisor_degree_lower i
  have hg := f256GarciaStichtenothGenus_fibre_identity i
  have hA := f256GarciaStichtenothDivisorA_degree_pos i
  have hB := f256GarciaStichtenothDivisorB_degree_pos i
  omega

theorem f256MultiplicationDivisor_dual_distance_numerator (i : ℕ) :
    (f256GarciaStichtenothLength i : ℤ) ≤
      5 * (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 2 -
        2 * (f256GarciaStichtenothGenus i : ℤ)) := by
  have hl := f256MultiplicationDivisor_degree_lower i
  have hg := f256GarciaStichtenothGenus_fibre_identity i
  have hA := f256GarciaStichtenothDivisorA_degree_pos i
  have hB := f256GarciaStichtenothDivisorB_degree_pos i
  omega

theorem f256MultiplicationDivisor_large_degree (i : ℕ) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) := by
  have h := f256MultiplicationDivisor_dual_distance_numerator i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  omega

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

import QEC.Coding.FiniteAlternatingConstruction.QuantitativeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace QEC.Coding.BDL26QuantitativeBounds

open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph

/-- Fixed-scale exponential envelope base; this is not an exact growth ratio. -/
def evenGrowthEnvelope (S : OddScale) : Nat := 8 * faceGrowthFactor S ^ 2

/-- Absorb the finite prefactors at positive even depths. -/
theorem evenState_pure_power_bounds (S : OddScale) (k : Nat) (hk : 1 ≤ k) :
    4 ^ k ≤ Fintype.card (state S (2*k)).presentation.Q ∧
      Fintype.card (state S (2*k)).presentation.Q ≤ evenGrowthEnvelope S ^ k := by
  have hlo := state_qubit_card_lower S (2*k)
  have hhi := state_qubit_card_upper S (2*k)
  have h8 : 8 ≤ (8 : Nat)^k := le_self_pow (by omega) (by omega)
  constructor
  · have he : (2 : Nat)^(2*k) = 4^k := by rw [pow_mul]; norm_num
    rw [he] at hlo
    omega
  · apply hhi.trans
    unfold evenGrowthEnvelope
    rw [mul_pow,pow_mul]
    exact Nat.mul_le_mul_right _ h8

/-- Explicit real exponential bounds for the source n_(2k) relation, for fixed ell. -/
theorem evenState_exponential_bounds (S : OddScale) (k : Nat) (hk : 1 ≤ k) :
    Real.exp ((k : ℝ) * Real.log 4) ≤
        (Fintype.card (state S (2*k)).presentation.Q : ℝ) ∧
      (Fintype.card (state S (2*k)).presentation.Q : ℝ) ≤
        Real.exp ((k : ℝ) * Real.log (evenGrowthEnvelope S : ℝ)) := by
  have hs := S.three_le
  have hell : 0 < S.ell := by omega
  have hA : 0 < faceGrowthFactor S := by unfold faceGrowthFactor; positivity
  have hB : (0 : ℝ) < evenGrowthEnvelope S := by
    exact_mod_cast (show 0 < evenGrowthEnvelope S by unfold evenGrowthEnvelope; positivity)
  have hb := evenState_pure_power_bounds S k hk
  constructor
  · rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    exact_mod_cast hb.1
  · rw [Real.exp_nat_mul,Real.exp_log hB]
    exact_mod_cast hb.2

/-- A quantified exp(Theta(k)) statement with positive constants and an explicit start index.
Only the upper exponent depends on the one fixed subdivision scale. -/
theorem evenState_expTheta (S : OddScale) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k : Nat, 1 ≤ k →
      Real.exp ((k : ℝ)*c) ≤ (Fintype.card (state S (2*k)).presentation.Q : ℝ) ∧
      (Fintype.card (state S (2*k)).presentation.Q : ℝ) ≤ Real.exp ((k : ℝ)*C) := by
  have hs := S.three_le
  have hell : 0 < S.ell := by omega
  have hA : 0 < faceGrowthFactor S := by unfold faceGrowthFactor; positivity
  have hBnat : 1 < evenGrowthEnvelope S := by unfold evenGrowthEnvelope; nlinarith
  refine ⟨Real.log 4,Real.log (evenGrowthEnvelope S : ℝ),
    Real.log_pos (by norm_num),Real.log_pos (by exact_mod_cast hBnat),?_⟩
  exact fun k hk => evenState_exponential_bounds S k hk
end QEC.Coding.BDL26QuantitativeBounds

import QEC.Distillation.LowOverheadProtocol.Core.PuncturedReedMuller

/-!
# HH18 denominator-clearing parameter sequences

The exact rational witnesses used by the HH18 asymptotic construction are
realized as natural-number sequences before any asymptotic argument is used.
-/

namespace QEC.Distillation.HH18.HH18ParameterSequence

open Coding.PuncturedReedMuller

/-- The exact rational witness selected by the approved HH18 TeX contract. -/
def p0 : ℚ := 270629 / 1000000

/-- The cleared `r` parameter for the strict-bound witness. -/
def p0R (j : Nat) : Nat := 1000000 * j

/-- The cleared `w` parameter for the strict-bound witness. -/
def p0W (j : Nat) : Nat := 811887 * j

/-- The HH18 `m = 3r + 1` parameter for the strict-bound witness. -/
def p0M (j : Nat) : Nat := 3 * p0R j + 1

/-- At each positive index, the strict-bound sequence has exactly the approved
rational slope and satisfies all natural-number hypotheses of HH18 Theorem 1. -/
theorem p0_parameters_admissible (j : Nat) (hj : 0 < j) :
    p0M j = 3 * p0R j + 1 ∧
      (p0W j : ℚ) = 3 * (p0R j : ℚ) * p0 ∧
      Admissible (p0W j) (p0R j) (p0M j) := by
  constructor
  · rfl
  constructor
  · simp only [p0W, p0R, p0]
    push_cast
    norm_num
    ring
  · simp only [Admissible, p0M, p0R, p0W]
    omega

end QEC.Distillation.HH18.HH18ParameterSequence

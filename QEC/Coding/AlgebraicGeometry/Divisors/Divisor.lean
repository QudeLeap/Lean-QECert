/-
Source-level foundation. This module is deliberately limited to
finitely supported integer combinations of an actual place carrier. It does
not state any Riemann--Roch, finite-dimensionality, evaluation-code, or
canonical-divisor conclusion.
-/

import Mathlib.Data.Finsupp.Weight

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators

/-- A divisor is a finite-support integer combination of places. -/
abbrev Divisor (P : Type*) := P →₀ ℤ

namespace Divisor

variable {P : Type*}

/-- The finite support of a divisor. -/
def support (D : Divisor P) : Finset P := Finsupp.support D

/-- A divisor has a place in its support exactly when its coefficient is nonzero. -/
theorem mem_support_iff {D : Divisor P} {place : P} :
    place ∈ support D ↔ D place ≠ 0 :=
  by simpa only [support] using
    (Finsupp.mem_support_iff : place ∈ D.support ↔ D place ≠ 0)

/-- Degree is the weighted finite sum of divisor coefficients. -/
noncomputable def degreeHom (degreeOf : P → ℕ) : Divisor P →+ ℤ where
  toFun D := D.sum fun P coefficient => coefficient * (degreeOf P : ℤ)
  map_zero' := Finsupp.sum_zero_index
  map_add' D E := by
    change (D + E).sum (fun P coefficient => coefficient * (degreeOf P : ℤ)) =
      D.sum (fun P coefficient => coefficient * (degreeOf P : ℤ)) +
        E.sum (fun P coefficient => coefficient * (degreeOf P : ℤ))
    exact Finsupp.sum_add_index'
      (fun _ => by simp)
      (fun _ _ _ => by ring)

/-- The degree of a divisor with respect to the supplied place-degree function. -/
noncomputable def degree (degreeOf : P → ℕ) (D : Divisor P) : ℤ := degreeHom degreeOf D

@[simp]
theorem degree_zero (degreeOf : P → ℕ) : degree degreeOf (0 : Divisor P) = 0 := by
  simpa [degree] using (degreeHom degreeOf).map_zero

theorem degree_add (degreeOf : P → ℕ) (D E : Divisor P) :
    degree degreeOf (D + E) = degree degreeOf D + degree degreeOf E := by
  simpa [degree] using (degreeHom degreeOf).map_add D E

theorem degree_neg (degreeOf : P → ℕ) (D : Divisor P) :
    degree degreeOf (-D) = -degree degreeOf D := by
  simpa [degree] using (degreeHom degreeOf).map_neg D

theorem degree_sub (degreeOf : P → ℕ) (D E : Divisor P) :
    degree degreeOf (D - E) = degree degreeOf D - degree degreeOf E := by
  simpa [degree] using (degreeHom degreeOf).map_sub D E

/-- Positivity of a divisor is coefficientwise nonnegativity. -/
def Nonnegative (D : Divisor P) : Prop := ∀ P, 0 ≤ D P

theorem nonnegative_of_forall_coeff {D : Divisor P} (hD : ∀ P, 0 ≤ D P) :
    Nonnegative D := hD

theorem nonnegative_zero : Nonnegative (0 : Divisor P) := by
  intro P
  simp

theorem Nonnegative.add {D E : Divisor P} (hD : Nonnegative D) (hE : Nonnegative E) :
    Nonnegative (D + E) := by
  intro P
  exact add_nonneg (hD P) (hE P)

/-- A positive divisor has nonnegative degree when place degrees are natural numbers. -/
theorem degree_nonnegative (degreeOf : P → ℕ) (D : Divisor P) (hD : Nonnegative D) :
    0 ≤ degree degreeOf D := by
  change 0 ≤ D.sum fun P coefficient => coefficient * (degreeOf P : ℤ)
  exact Finsupp.sum_nonneg fun P _ => mul_nonneg (hD P) (Int.ofNat_nonneg _)

end Divisor

end QEC.Coding.AlgebraicGeometry

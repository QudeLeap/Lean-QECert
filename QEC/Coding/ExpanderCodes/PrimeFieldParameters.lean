import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega

/-!
# Odd prime-field parameters for quadratic generators

The constant field and its nonsquare are actual finite-field choices, not
inputs asserting the existence of a Cayley graph. Euclid's theorem supplies
arbitrarily large odd primes, and the finite-field squaring argument supplies
the nonsquare required in [DEL21, Section 6.2]. These statements concern the
constant-field degree only; they do not assert a cofinal quotient family or a
Ramanujan estimate.
-/

namespace QEC.Coding.ExpanderCodes

/-- A finite field of odd characteristic has a nonzero quadratic parameter. -/
theorem exists_nonsquare_parameter (F : Type*) [Field F] [Finite F]
    (hTwo : ringChar F ≠ 2) :
    ∃ epsilon : F, epsilon ≠ 0 ∧ ∀ r : F, r ^ 2 ≠ epsilon := by
  obtain ⟨epsilon, hNonSquare⟩ := FiniteField.exists_nonsquare hTwo
  refine ⟨epsilon, ?_, ?_⟩
  · rintro rfl
    exact hNonSquare ⟨0, by simp⟩
  · intro r hSquare
    exact hNonSquare ⟨r, by simpa only [pow_two] using hSquare.symm⟩

/-- Arbitrarily large odd prime fields admit the actual nonsquare parameter.
The resulting orbit degree is `p + 1`; no graph spectrum is included here. -/
theorem exists_large_prime_parameter (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N ≤ p + 1 ∧ 3 ≤ p ∧
      ∃ epsilon : ZMod p, epsilon ≠ 0 ∧ ∀ r : ZMod p, r ^ 2 ≠ epsilon := by
  obtain ⟨p, hBound, hPrime⟩ := Nat.exists_infinite_primes (max N 3)
  have hN : N ≤ p := (le_max_left N 3).trans hBound
  have hThree : 3 ≤ p := (le_max_right N 3).trans hBound
  refine ⟨p, hPrime, by omega, hThree, ?_⟩
  letI : Fact p.Prime := ⟨hPrime⟩
  apply exists_nonsquare_parameter (ZMod p)
  rw [ZMod.ringChar_zmod_n]
  omega

end QEC.Coding.ExpanderCodes

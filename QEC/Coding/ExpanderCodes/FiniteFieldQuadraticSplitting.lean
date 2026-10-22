import QEC.Coding.ExpanderCodes.FiniteFieldSpecialization
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Quadratic splitting in even-degree finite extensions

The constant quadratic field embeds in every even-degree finite extension.
Thus the square root required by the split matrix realization is obtained
from the finite-field embedding theorem, rather than assumed. Together with
a full-degree specialization parameter this realizes the algebraic part of
the congruence setting in [DEL21, Section 6.2]. It does not supply an arithmetic
surjectivity or Ramanujan theorem.
-/

namespace QEC.Coding.ExpanderCodes

open scoped QuadraticAlgebra

/-- A nonsquare constant acquires a square root in every even-degree finite extension. -/
theorem exists_square_root_of_even_finrank
    {F K : Type*} [Field F] [Field K] [Finite K] [Algebra F K]
    (epsilon : F) (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEven : 2 ∣ Module.finrank F K) :
    ∃ r : K, r ^ 2 = algebraMap F K epsilon := by
  letI : Fact (∀ r : F, r ^ 2 ≠ epsilon + 0 * r) :=
    ⟨fun r => by simpa using hNonSquare r⟩
  obtain ⟨g⟩ : Nonempty (QuadraticAlgebra F epsilon 0 →ₐ[F] K) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      simpa only [QuadraticAlgebra.finrank_eq_two] using hEven)
  let i : QuadraticAlgebra F epsilon 0 := ⟨0, 1⟩
  have hSquare : i ^ 2 = algebraMap F (QuadraticAlgebra F epsilon 0) epsilon := by
    ext <;> simp [i, pow_two]
  refine ⟨g i, ?_⟩
  calc
    (g i) ^ 2 = g (i ^ 2) := (map_pow g i 2).symm
    _ = g (algebraMap F (QuadraticAlgebra F epsilon 0) epsilon) := congrArg g hSquare
    _ = algebraMap F K epsilon := g.commutes epsilon

/-- Actual even-degree specializations simultaneously provide a nonzero
square root of the constant parameter and an irreducible full-degree point. -/
theorem exists_split_full_degree_parameter (p n : ℕ) [Fact p.Prime]
    (hPositive : 0 < n) (epsilon : ZMod p)
    (hEpsilon : epsilon ≠ 0) (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    ∃ y r : GaloisField p (2 * n), y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧
      r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n := by
  obtain ⟨y, hY, hOne, hIrreducible, hDegree, _⟩ :=
    exists_full_degree_parameter p (2 * n) (by omega)
  obtain ⟨r, hRoot⟩ := exists_square_root_of_even_finrank
    (K := GaloisField p (2 * n)) epsilon hNonSquare (by
      rw [GaloisField.finrank p (by omega)]
      exact dvd_mul_right 2 n)
  refine ⟨y, r, hY, hOne, ?_, hRoot, hIrreducible, hDegree⟩
  intro hZero
  have hImage : algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon = 0 := by
    simpa only [hZero, zero_pow (by decide : 2 ≠ 0)] using hRoot.symm
  exact hEpsilon ((algebraMap (ZMod p) (GaloisField p (2 * n))).injective
    (by simpa only [map_zero] using hImage))

end QEC.Coding.ExpanderCodes

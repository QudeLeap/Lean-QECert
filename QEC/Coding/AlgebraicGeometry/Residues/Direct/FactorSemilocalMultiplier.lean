import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A principal multiplier isolating one direct factor

For one chosen prime factor `P` above a direct polynomial prime, Dedekind
two-generator theory produces an integral multiplier whose principal ideal is
`P * J`, with `J` coprime to the whole extended base prime.  The construction
applies `IsDedekindDomain.exists_sup_span_eq` to
`P * (p B) <= P`; cancelling the nonzero ideal `P` turns the resulting sum
identity into `(p B) + J = 1`.

This is a semilocal ideal-theoretic construction only.  It does not choose a
global denominator, define a residue, sum over places, or assert duality,
genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier

open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

/-- Every chosen direct upper factor has an integral principal multiplier
whose remaining ideal factor is coprime to the extended base prime. -/
theorem exists_directFactorSemilocalMultiplier
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    ∃ t : B k F, t ≠ 0 ∧ ∃ J : Ideal (B k F),
      Ideal.span ({t} : Set (B k F)) = (P : Ideal (B k F)) * J ∧
        IsCoprime
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J := by
  classical
  let M : Ideal (B k F) :=
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal
  have hP_ne : (P : Ideal (B k F)) ≠ 0 :=
    Ideal.Factors.ne_bot p.asIdeal P
  have hM_ne : M ≠ 0 := by
    exact Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hPM_le : (P : Ideal (B k F)) * M ≤ (P : Ideal (B k F)) :=
    Ideal.mul_le_left
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_sup_span_eq hPM_le
    (mul_ne_zero hP_ne hM_ne)
  have hspan_le : Ideal.span ({t} : Set (B k F)) ≤
      (P : Ideal (B k F)) :=
    le_sup_right.trans_eq ht
  obtain ⟨J, hspan⟩ := Ideal.dvd_iff_le.mpr hspan_le
  have hsup : M ⊔ J = ⊤ := by
    apply mul_left_cancel₀ hP_ne
    rw [Ideal.mul_sup, ← hspan, ht, Ideal.mul_top]
  have hM_le : M ≤ (P : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  have hM_ne_top : M ≠ ⊤ := by
    intro hM
    exact (Ideal.Factors.isPrime p.asIdeal P).ne_top
      (top_unique (hM ▸ hM_le))
  have ht_ne : t ≠ 0 := by
    intro ht_zero
    have hPM_eq : (P : Ideal (B k F)) * M = (P : Ideal (B k F)) := by
      simpa only [ht_zero, Set.singleton_zero, Ideal.span_zero, sup_bot_eq] using ht
    have hM_top : M = ⊤ := by
      apply mul_left_cancel₀ hP_ne
      simpa only [Ideal.mul_top] using hPM_eq
    exact hM_ne_top hM_top
  exact ⟨t, ht_ne, J, hspan, Ideal.isCoprime_iff_sup_eq.mpr hsup⟩

end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalMultiplier

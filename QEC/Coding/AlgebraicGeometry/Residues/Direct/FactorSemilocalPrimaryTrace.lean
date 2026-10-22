import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorPrimaryTrace
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.CoprimeQuotientTrace
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.CRTTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Isolating one direct factor in a semilocal primary trace

Let `P` be one actual upper prime factor above a direct polynomial prime and
let `J` be an ideal coprime to the extended base prime.  Chinese remaindering
splits the quotient by `P * J`; the `P`-summand is annihilated by the base
prime, while the `J`-summand has no base-primary torsion.  Thus the whole
positive-depth primary trace is exactly the ordinary trace on `B / P`, and
therefore the established factor residue trace after canonical reduction.

This is a one-factor semilocal comparison.  It does not choose a global
denominator, sum over places, or assert a duality, genus, or Riemann--Roch
formula.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace

open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid

attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

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

open DirectFactorPrimaryTrace

/-- A coprime semilocal complement contributes no primary trace, so the
product quotient has exactly the ordinary multiplication trace on the chosen
upper factor. -/
theorem primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
          (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  have hmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤
      (P : Ideal (B k F)) := by
    exact Ideal.le_of_dvd
      (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  have hPJ : IsCoprime (P : Ideal (B k F)) J := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup_right hmap J
  rw [primaryTorsionTrace_quotientMul_eq_add p.asIdeal
    (P : Ideal (B k F)) J hPJ b depth,
    primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
      k F p P b depth hdepth,
    primaryTorsionTrace_idealQuotient_eq_zero_of_isCoprime_map
      p.asIdeal J hcop
        (Algebra.lmul (R k) (B k F ⧸ J)
          (Ideal.Quotient.mk J b)) depth,
    add_zero]

/-- Canonical base-residue transport sends the semilocal primary trace to
the established residue trace of the chosen upper factor. -/
theorem
    quotientResidueEquiv_primaryTorsionTrace_directFactorMulCoprime_eq_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
            (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  rw [primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
    k F p P J hcop b depth hdepth]
  exact Ideal.Factors.quotientTrace_to_factorResidueTrace p.asIdeal P b

end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace

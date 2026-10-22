import Mathlib.NumberTheory.FunctionField
import QEC.Coding.AlgebraicGeometry.Residues.Direct.IntegralTraceResidue
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.AnnihilatedTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Primary trace on one direct upper factor

For one actual prime factor above a finite polynomial prime, the upper ideal
quotient is annihilated by the base prime.  Its positive-depth primary trace
is therefore the ordinary multiplication trace on that quotient.  Transport
to the actual base residue field identifies this value with the established
factor residue trace.

This is a one-factor comparison only.  It does not choose a semilocal
denominator, sum over places, or assert a duality, genus, or Riemann--Roch
formula.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace

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

private theorem map_basePrime_le_directFactor
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≤
      (P : Ideal (B k F)) := by
  exact Ideal.le_of_dvd
    (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))

private theorem directFactorQuotient_annihilated
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    Module.IsTorsionBySet (R k) (B k F ⧸ (P : Ideal (B k F)))
      p.asIdeal := by
  intro x r
  have hrP : algebraMap (R k) (B k F) (r : R k) ∈
      (P : Ideal (B k F)) :=
    map_basePrime_le_directFactor k F p P
      (Ideal.mem_map_of_mem (algebraMap (R k) (B k F)) r.property)
  calc
    (r : R k) • x = algebraMap (R k) (B k F) (r : R k) • x :=
      (IsScalarTower.algebraMap_smul (B k F) (r : R k) x).symm
    _ = 0 := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk (P : Ideal (B k F))
        (algebraMap (R k) (B k F) (r : R k) * y) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        ((P : Ideal (B k F)).mul_mem_right y hrP)

/-- On one actual upper factor quotient, positive-depth primary trace of
multiplication is the ordinary quotient-field multiplication trace. -/
theorem primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
  classical
  let fP := Algebra.lmul (R k ⧸ p.asIdeal)
    (B k F ⧸ (P : Ideal (B k F)))
    (Ideal.Quotient.mk (P : Ideal (B k F)) b)
  have hrestrict : fP.restrictScalars (R k) =
      Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by
    apply LinearMap.ext
    intro x
    rfl
  calc
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth =
      primaryTorsionTrace p.asIdeal
        (fP.restrictScalars (R k)) depth := by rw [hrestrict]
    _ = LinearMap.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F))) fP :=
      primaryTorsionTrace_restrictScalars_eq_trace_of_annihilated
        p.asIdeal (directFactorQuotient_annihilated k F p P)
          fP depth hdepth
    _ = _ := (Algebra.trace_apply (R k ⧸ p.asIdeal)
      (Ideal.Quotient.mk (P : Ideal (B k F)) b)).symm

/-- After canonical quotient-to-residue transport, the primary trace on one
upper factor quotient is its actual factor residue trace. -/
theorem
    quotientResidueEquiv_primaryTorsionTrace_directFactorQuotientMul_eq_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    Ideal.Factors.quotientResidueEquiv p.asIdeal
        (primaryTorsionTrace p.asIdeal
          (Algebra.lmul (R k) (B k F ⧸ (P : Ideal (B k F)))
            (Ideal.Quotient.mk (P : Ideal (B k F)) b)) depth) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  rw [primaryTorsionTrace_directFactorQuotientMul_eq_quotientTrace
    k F p P b depth hdepth]
  exact Ideal.Factors.quotientTrace_to_factorResidueTrace p.asIdeal P b

end QEC.Coding.AlgebraicGeometry.DirectFactorPrimaryTrace

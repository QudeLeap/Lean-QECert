import QEC.Coding.AlgebraicGeometry.Places.AffineGlobalPlace
import QEC.Coding.AlgebraicGeometry.Residues.Direct.IntegralTraceResidue
import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct
import QEC.Coding.AlgebraicGeometry.Residues.Local.LogarithmicResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Direct integral differential residues

This module begins the geometric specialization of the integral
trace--residue identity.  It turns every actual prime factor over a direct
height-one polynomial prime into its affine/global place and proves that the
base-prime generator has normalized order equal to the genuine ramification
index.

No semilocal denominator, global residue sum, duality statement, genus
formula, or Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue

open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

/-- An actual prime factor over a direct height-one polynomial prime,
regarded as the corresponding affine place. -/
noncomputable def directFactorPlace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    AffinePlace.carrier k F :=
  { asIdeal := (P : Ideal (B k F))
    isPrime := Ideal.Factors.isPrime p.asIdeal P
    ne_bot := Ideal.Factors.ne_bot p.asIdeal P }

omit [Finite k] in
@[simp]
theorem directFactorPlace_asIdeal
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    (directFactorPlace k F p P).asIdeal = (P : Ideal (B k F)) :=
  rfl

/-- At an actual upper factor place, the normalized order of the chosen base
prime generator is precisely the ramification index. -/
theorem directFactorPlace_order_baseGenerator
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    GlobalPlace.order (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (R k) F (generator p.asIdeal)) =
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) : ℤ) := by
  let q : R k := generator p.asIdeal
  let x : B k F := algebraMap (R k) (B k F) q
  have hq : q ≠ 0 := by
    intro hzero
    apply p.ne_bot
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p.asIdeal).mpr hzero
  have hx : x ≠ 0 := by
    simpa only [x, q, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F).ne hq
  have hpmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hspan : Ideal.span ({x} : Set (B k F)) =
      Ideal.map (algebraMap (R k) (B k F)) p.asIdeal := by
    dsimp only [x, q]
    calc
      Ideal.span
          ({algebraMap (R k) (B k F) (generator p.asIdeal)} : Set (B k F)) =
          Ideal.map (algebraMap (R k) (B k F))
            (Ideal.span ({generator p.asIdeal} : Set (R k))) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap (R k) (B k F)) p.asIdeal := by
        rw [Ideal.span_singleton_generator p.asIdeal]
  rw [IsScalarTower.algebraMap_apply (R k) (B k F) F]
  change GlobalPlace.order
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (B k F) F x) = _
  rw [AffinePlace.globalPlace_order_of_integral_eq_multiplicity k F
    (directFactorPlace k F p P) hx, directFactorPlace_asIdeal, hspan]
  exact_mod_cast
    (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hpmap
      (Ideal.Factors.isPrime p.asIdeal P)).symm

/-- Direct integral elements map canonically into the valuation ring of an
actual upper factor place. -/
noncomputable def directIntegralToValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    B k F →+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing :=
  (algebraMap (B k F) F).codRestrict
    (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing
    fun b => by
      change AffinePlace.valuation k F (directFactorPlace k F p P)
        (algebraMap (B k F) F b) ≤ 1
      rw [AffinePlace.valuation_algebraMap_of_integral k F
        (directFactorPlace k F p P) b]
      exact (directFactorPlace k F p P).intValuation_le_one b

@[simp]
theorem coe_directIntegralToValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ((directIntegralToValuationRing k F p P b :
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing) : F) =
      algebraMap (B k F) F b :=
  rfl

private theorem directBaseGenerator_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    algebraMap (R k) F (generator p.asIdeal) ≠ 0 := by
  have hq : generator p.asIdeal ≠ 0 := by
    intro hzero
    apply p.ne_bot
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p.asIdeal).mpr hzero
  simpa only [map_zero] using
    (_root_.FunctionField.algebraMap_injective k F).ne hq

/-- The simple-pole differential obtained by multiplying the logarithmic
differential of the base-prime generator by one actual integral coefficient. -/
noncomputable def directIntegralLogarithmicDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    Differential.simplePoleDifferentialLattice
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)) :=
  directIntegralToValuationRing k F p P b •
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := F)
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
      (algebraMap (R k) F (generator p.asIdeal))
      (directBaseGenerator_ne_zero k F p)

/-- The normalized residue of the integral multiple of the base logarithmic
differential is its actual reduced coefficient times the genuine
ramification index. -/
theorem simplePoleResidue_directIntegralLogarithmicDifferential
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    Differential.simplePoleResidue (k := k) (F := F)
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (directIntegralLogarithmicDifferentialAtSimplePole k F p P b) =
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
          (directIntegralToValuationRing k F p P b) *
        (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField) := by
  unfold directIntegralLogarithmicDifferentialAtSimplePole
  rw [Differential.simplePoleResidue_smul,
    Differential.simplePoleResidue_logarithmicDifferential,
    directFactorPlace_order_baseGenerator]
  simp only [Int.cast_natCast]

end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue

import QEC.Coding.AlgebraicGeometry.Residues.Direct.FactorResidueTransport

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Trace compatibility for direct factor residues

For every actual prime factor over a direct height-one polynomial prime, this
module transports the residue-field trace to the residue field of the
packaged global place.  It then combines that transport with the normalized
residue of an integral multiple of the base logarithmic differential.  The
resulting finite sum is exactly the reduction of the integral trace.

This is a direct-chart, integral-coefficient identity.  It does not treat
semilocal denominators, inverse-chart poles, arbitrary global differentials,
duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue

open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid

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

open DirectIntegralDifferentialResidue DirectFactorResidueTransport

/-- The canonical embedding of the base-prime residue field into the residue
field of one packaged upper factor place. -/
noncomputable def directFactorBaseResidueMap
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    p.asIdeal.ResidueField →+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residueField := by
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime (P : Ideal (B k F))) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal (P : Ideal (B k F))
  exact (directFactorResidueEquiv k F p P).toRingHom.comp
    (algebraMap p.asIdeal.ResidueField (P : Ideal (B k F)).ResidueField)

/-- The actual trace from the packaged upper-place residue field to the
base-prime residue field.  Its scalar embedding is
`directFactorBaseResidueMap`. -/
noncomputable def directFactorPlaceTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (x : (AffinePlace.globalPlace k F
      (directFactorPlace k F p P)).residueField) :
    p.asIdeal.ResidueField := by
  letI : Algebra p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField :=
    (directFactorBaseResidueMap k F p P).toAlgebra
  exact Algebra.trace p.asIdeal.ResidueField
    (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residueField x

private theorem directFactorPlaceTrace_mul_baseResidue
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (x : (AffinePlace.globalPlace k F
      (directFactorPlace k F p P)).residueField)
    (r : p.asIdeal.ResidueField) :
    directFactorPlaceTrace k F p P
        (x * directFactorBaseResidueMap k F p P r) =
      r * directFactorPlaceTrace k F p P x := by
  letI : Algebra p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField :=
    (directFactorBaseResidueMap k F p P).toAlgebra
  change Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField
        (x * algebraMap p.asIdeal.ResidueField
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField r) =
    r * Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField x
  rw [mul_comm]
  exact map_smul (Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField) r x

/-- Tracing the actual reduction of an integral element at the packaged place
agrees with the canonical ideal-residue-field trace. -/
theorem directFactorPlaceTrace_residue_integral
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorPlaceTrace k F p P
        ((AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b)) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime (P : Ideal (B k F))) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal (P : Ideal (B k F))
  let e := directFactorResidueEquiv k F p P
  letI : Algebra p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField :=
    (directFactorBaseResidueMap k F p P).toAlgebra
  have he : RingHom.comp
      (algebraMap p.asIdeal.ResidueField
        (AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residueField)
      (RingEquiv.refl p.asIdeal.ResidueField) =
      RingHom.comp (e : (P : Ideal (B k F)).ResidueField →+*
        (AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residueField)
        (algebraMap p.asIdeal.ResidueField
          (P : Ideal (B k F)).ResidueField) := by
    rfl
  have htrace := Algebra.trace_eq_of_equiv_equiv
    (RingEquiv.refl p.asIdeal.ResidueField) e he
    (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b)
  change Algebra.trace p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField
        ((AffinePlace.globalPlace k F
          (directFactorPlace k F p P)).residue
            (directIntegralToValuationRing k F p P b)) =
    Algebra.trace p.asIdeal.ResidueField
      (P : Ideal (B k F)).ResidueField
        (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b)
  rw [← directFactorResidueEquiv_algebraMap]
  exact htrace.symm

/-- The base-residue-field trace of the normalized local residue of an
integral multiple of the base logarithmic differential is the upper residue
trace weighted by the genuine ramification index. -/
theorem
    directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorPlaceTrace k F p P
        (Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (directIntegralLogarithmicDifferentialAtSimplePole k F p P b)) =
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          p.asIdeal.ResidueField) *
        Ideal.Factors.factorResidueTrace p.asIdeal P b := by
  rw [simplePoleResidue_directIntegralLogarithmicDifferential]
  have hcast :
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField) =
        directFactorBaseResidueMap k F p P
          (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
            p.asIdeal.ResidueField) := by
    symm
    exact map_natCast (directFactorBaseResidueMap k F p P)
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)))
  rw [hcast, directFactorPlaceTrace_mul_baseResidue,
    directFactorPlaceTrace_residue_integral]

/-- Reduction of the direct integral trace equals the finite sum of the
actual traced normalized logarithmic residues at all upper factors. -/
theorem directIntegralTrace_residue_eq_sum_directFactorTraces
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (b : B k F) :
    algebraMap (R k) p.asIdeal.ResidueField
        (Algebra.intTrace (R k) (B k F) b) =
      ∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directIntegralLogarithmicDifferentialAtSimplePole k F p P b)) := by
  have hpmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  rw [Ideal.Factors.integralTrace_residue_eq_sum_ramificationIdx_mul
    p.asIdeal hpmap b]
  apply Finset.sum_congr rfl
  intro P _
  rw [directFactorPlaceTrace_simplePoleResidue_directIntegralLogarithmicDifferential]

end QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue

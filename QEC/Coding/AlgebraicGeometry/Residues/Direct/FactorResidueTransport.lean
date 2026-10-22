import QEC.Coding.AlgebraicGeometry.Residues.Direct.IntegralDifferentialResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Direct factor residue transport

This module identifies the ideal residue field of an actual prime factor in
the direct integral closure with the residue field of its packaged affine
global place.  The equivalence is induced by the genuine localization and
valuation-subring equivalences, and it sends the reduction of an integral
element to the actual valuation-ring residue used by local differential
residues.

No trace compatibility, global residue sum, duality statement, genus formula,
or Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport

open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

open DirectIntegralDifferentialResidue

/-- The localization at an actual upper factor is canonically the valuation
ring of its packaged affine global place. -/
noncomputable def directFactorLocalizationEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    Localization.AtPrime (P : Ideal (B k F)) ≃+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing := by
  let C : AffinePlace.carrier k F := directFactorPlace k F p P
  change Localization.AtPrime C.asIdeal ≃+* (C.valuation F).valuationSubring
  let e₁ : Localization.AtPrime C.asIdeal ≃+*
      C.valuationSubringAtPrime F :=
    (Localization.algEquiv C.asIdeal.primeCompl
      (C.valuationSubringAtPrime F)).toRingEquiv
  let hsub : (C.valuationSubringAtPrime F).toSubring =
      (C.valuation F).valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring
      C.valuationSubringAtPrime_eq_valuationSubring
  let e₂ : C.valuationSubringAtPrime F ≃+*
      (C.valuation F).valuationSubring :=
    RingEquiv.subringCongr hsub
  exact e₁.trans e₂

@[simp]
private theorem coe_directFactorLocalizationEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ((directFactorLocalizationEquiv k F p P
        (algebraMap (B k F) (Localization.AtPrime (P : Ideal (B k F))) b) :
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing) : F) =
      algebraMap (B k F) F b := by
  let C : AffinePlace.carrier k F := directFactorPlace k F p P
  change ((directFactorLocalizationEquiv k F p P
      (algebraMap (B k F) (Localization.AtPrime C.asIdeal) b) :
    (C.valuation F).valuationSubring) : F) = algebraMap (B k F) F b
  unfold directFactorLocalizationEquiv
  exact congrArg Subtype.val
    ((Localization.algEquiv C.asIdeal.primeCompl
      (C.valuationSubringAtPrime F)).commutes b)

/-- The ideal residue field of an actual upper factor is canonically
equivalent to the residue field of its packaged affine global place. -/
noncomputable def directFactorResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    (P : Ideal (B k F)).ResidueField ≃+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residueField :=
  IsLocalRing.ResidueField.mapEquiv (directFactorLocalizationEquiv k F p P)

/-- The direct-factor residue equivalence sends the reduction of an integral
element to its actual reduction in the packaged place valuation ring. -/
@[simp]
theorem directFactorResidueEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorResidueEquiv k F p P
        (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b) =
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
        (directIntegralToValuationRing k F p P b) := by
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : IsLocalHom (directFactorLocalizationEquiv k F p P).toRingHom :=
    ⟨fun _ hunit => by
      simpa using hunit.map
        (directFactorLocalizationEquiv k F p P).symm.toRingHom⟩
  unfold directFactorResidueEquiv
  change IsLocalRing.ResidueField.map
      (directFactorLocalizationEquiv k F p P).toRingHom
        ((IsLocalRing.residue (Localization.AtPrime (P : Ideal (B k F))))
          (algebraMap (B k F) (Localization.AtPrime (P : Ideal (B k F))) b)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  apply congrArg
    (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
  apply Subtype.ext
  change ((directFactorLocalizationEquiv k F p P
      (algebraMap (B k F) (Localization.AtPrime (P : Ideal (B k F))) b) :
    (AffinePlace.globalPlace k F
      (directFactorPlace k F p P)).valuationRing) : F) =
    algebraMap (B k F) F b
  exact coe_directFactorLocalizationEquiv k F p P b

end QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport

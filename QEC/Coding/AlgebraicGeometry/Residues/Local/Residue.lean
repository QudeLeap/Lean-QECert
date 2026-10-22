import QEC.Coding.AlgebraicGeometry.Differentials.LocalUniformizerDerivative

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The normalized simple-pole residue

This module normalizes the previously constructed equivalence from the local
simple-pole quotient to the place residue field.  The normalization sends the
logarithmic differential of the normalized uniformizer to `1`.  It therefore
gives an actual residue map on the simple-pole lattice, vanishing on regular
differentials and unchanged when the uniformizer is multiplied by a unit.

This is not yet a residue map on arbitrary higher-order meromorphic
differentials.  In particular, this module does not construct a Laurent
expansion, prove the global residue theorem, or state a Riemann--Roch law.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

private noncomputable def uniformizerDerivativeResidueEquiv
    (P : GlobalPlace k F) :
    localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P :=
  localResidueLineEquivResidueField_ofPrincipalCutoff (k := k) (F := F) P
    (functionFieldDerivation (k := k) (F := F)
      (P.uniformizerInValuationRing : F))
    (uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
      (k := k) (F := F) P)

private noncomputable def uniformizerResidueNormalizationUnit
    (P : GlobalPlace k F) : (GlobalPlace.residueField P)ˣ :=
  Units.mk0
    (uniformizerDerivativeResidueEquiv (k := k) (F := F) P
      (uniformizerLogDifferentialClass (k := k) (F := F) P))
    ((uniformizerDerivativeResidueEquiv (k := k) (F := F) P).map_ne_zero_iff.mpr
      (uniformizerLogDifferentialClass_ne_zero (k := k) (F := F) P))

/-- The normalized equivalence from the simple-pole quotient to the actual
place residue field. -/
noncomputable def simplePoleResidueEquiv (P : GlobalPlace k F) :
    localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P :=
  (uniformizerDerivativeResidueEquiv (k := k) (F := F) P).trans
    (Units.mulLeftLinearEquiv P.valuationRing (GlobalPlace.residueField P)
      ((uniformizerResidueNormalizationUnit (k := k) (F := F) P)⁻¹))

/-- The normalized equivalence sends the logarithmic differential of the
normalized uniformizer to `1`. -/
theorem simplePoleResidueEquiv_uniformizerLogDifferentialClass
    (P : GlobalPlace k F) :
    simplePoleResidueEquiv (k := k) (F := F) P
        (uniformizerLogDifferentialClass (k := k) (F := F) P) = 1 := by
  simp only [simplePoleResidueEquiv, LinearEquiv.trans_apply,
    Units.mulLeftLinearEquiv_apply, Units.val_inv_eq_inv_val,
    uniformizerResidueNormalizationUnit, Units.val_mk0]
  exact inv_mul_cancel₀
    ((uniformizerDerivativeResidueEquiv (k := k) (F := F) P).map_ne_zero_iff.mpr
      (uniformizerLogDifferentialClass_ne_zero (k := k) (F := F) P))

/-- The normalization on the logarithmic uniformizer class uniquely
characterizes the simple-pole residue equivalence. -/
theorem simplePoleResidueEquiv_unique
    (P : GlobalPlace k F)
    (e : localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P)
    (he : e (uniformizerLogDifferentialClass (k := k) (F := F) P) = 1) :
    e = simplePoleResidueEquiv (k := k) (F := F) P := by
  ext x
  let y : GlobalPlace.residueField P :=
    simplePoleResidueEquiv (k := k) (F := F) P x
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective y
  have hr_smul : r • (1 : GlobalPlace.residueField P) =
      simplePoleResidueEquiv (k := k) (F := F) P x := by
    rw [Algebra.smul_def, mul_one,
      IsLocalRing.ResidueField.algebraMap_eq]
    exact hr
  have hx : x = r • uniformizerLogDifferentialClass (k := k) (F := F) P := by
    apply (simplePoleResidueEquiv (k := k) (F := F) P).injective
    rw [map_smul,
      simplePoleResidueEquiv_uniformizerLogDifferentialClass
        (k := k) (F := F) P]
    exact hr_smul.symm
  calc
    e x = e (r • uniformizerLogDifferentialClass (k := k) (F := F) P) := by rw [hx]
    _ = r • e (uniformizerLogDifferentialClass (k := k) (F := F) P) := map_smul e r _
    _ = r • 1 := by rw [he]
    _ = simplePoleResidueEquiv (k := k) (F := F) P x := hr_smul

/-- The normalized residue map on differentials with at most a simple pole. -/
noncomputable def simplePoleResidue (P : GlobalPlace k F) :
    simplePoleDifferentialLattice P →ₗ[P.valuationRing]
      GlobalPlace.residueField P :=
  (simplePoleResidueEquiv (k := k) (F := F) P).toLinearMap.comp
    (regularDifferentialSubmoduleOfSimplePole P).mkQ

/-- The simple-pole residue of the normalized uniformizer's logarithmic
differential is `1`. -/
theorem simplePoleResidue_uniformizerLogDifferential (P : GlobalPlace k F) :
    simplePoleResidue (k := k) (F := F) P
        (uniformizerLogDifferential (k := k) (F := F) P) = 1 := by
  exact simplePoleResidueEquiv_uniformizerLogDifferentialClass
        (k := k) (F := F) P

/-- Regular differentials have zero simple-pole residue. -/
theorem simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
    (P : GlobalPlace k F) (omega : simplePoleDifferentialLattice P)
    (homega : (omega : Differential k F) ∈ localDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P omega = 0 := by
  have homega' : omega ∈ regularDifferentialSubmoduleOfSimplePole P := homega
  rw [simplePoleResidue, LinearMap.comp_apply]
  rw [Submodule.mkQ_apply]
  rw [(Submodule.Quotient.mk_eq_zero
    (p := regularDifferentialSubmoduleOfSimplePole P) (x := omega)).mpr homega',
    map_zero]

/-- Multiplying the normalized uniformizer by a valuation-ring unit leaves
the normalized simple-pole residue equal to `1`. -/
theorem simplePoleResidue_unitMulUniformizerLogDifferential
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    simplePoleResidue (k := k) (F := F) P
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u) = 1 := by
  change simplePoleResidueEquiv (k := k) (F := F) P
      (Submodule.Quotient.mk
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u)) = 1
  rw [unitMulUniformizerLogDifferentialClass_eq (k := k) (F := F) P u]
  exact simplePoleResidueEquiv_uniformizerLogDifferentialClass
    (k := k) (F := F) P

end Differential

end QEC.Coding.AlgebraicGeometry

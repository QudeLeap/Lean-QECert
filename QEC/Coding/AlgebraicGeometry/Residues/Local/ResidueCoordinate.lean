import QEC.Coding.AlgebraicGeometry.Residues.Local.ResidueProduct

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# A coordinate formula for the normalized local residue

This module expresses every differential with at most a simple pole as a
regular scalar multiple of the normalized uniformizer logarithmic
differential.  The scalar is constructed from the global `dX` coordinate and
the derivative of the normalized uniformizer.  Its reduction is exactly the
normalized simple-pole residue.

This is a local coordinate formula.  It does not assert compatibility with
field trace, a global residue theorem, duality, genus, or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The regular coefficient of a simple-pole differential relative to the
normalized uniformizer logarithmic differential. -/
noncomputable def simplePoleResidueCoordinate (P : GlobalPlace k F) :
    simplePoleDifferentialLattice P →ₗ[P.valuationRing] P.valuationRing := by
  classical
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let a : F := functionFieldDerivation (k := k) (F := F) (pi : F)
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  have ha := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (k := k) (F := F) P
  refine
    { toFun := fun omega => ?_
      map_add' := ?_
      map_smul' := ?_ }
  · have homega := omega.property
    change pi • (omega : Differential k F) ∈ localDifferentialLattice P at homega
    have hcoordinate :
        (pi : F) * C (omega : Differential k F) ∈
          localDerivativeLattice (k := k) (F := F) P := by
      have h := (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
        (k := k) (F := F) P (pi • (omega : Differential k F))).mp homega
      rw [LinearMap.map_smul_of_tower] at h
      exact h
    rw [ha.2.1] at hcoordinate
    let r : P.valuationRing :=
      Classical.choose (Submodule.mem_span_singleton.mp hcoordinate)
    have hr : r • a = (pi : F) * C (omega : Differential k F) :=
      Classical.choose_spec (Submodule.mem_span_singleton.mp hcoordinate)
    change (r : F) * a = (pi : F) * C (omega : Differential k F) at hr
    refine ⟨(pi : F) * C (omega : Differential k F) * a⁻¹, ?_⟩
    have hvalue :
        (pi : F) * C (omega : Differential k F) * a⁻¹ = (r : F) := by
      have ha_ne : a ≠ 0 := ha.1
      calc
        (pi : F) * C (omega : Differential k F) * a⁻¹ =
            ((r : F) * a) * a⁻¹ := by rw [← hr]
        _ = (r : F) := by
          rw [mul_assoc, mul_inv_cancel₀ ha_ne, mul_one]
    rw [hvalue]
    exact r.property
  · intro omega eta
    apply Subtype.ext
    change (pi : F) * C ((omega : Differential k F) + (eta : Differential k F)) *
        a⁻¹ =
      (pi : F) * C (omega : Differential k F) * a⁻¹ +
        (pi : F) * C (eta : Differential k F) * a⁻¹
    rw [map_add]
    ring
  · intro r omega
    apply Subtype.ext
    change (pi : F) * C ((r : F) • (omega : Differential k F)) * a⁻¹ =
      (r : F) * ((pi : F) * C (omega : Differential k F) * a⁻¹)
    rw [map_smul]
    simp only [smul_eq_mul]
    ring

/-- The ambient field value represented by the residue coordinate. -/
theorem coe_simplePoleResidueCoordinate (P : GlobalPlace k F)
    (omega : simplePoleDifferentialLattice P) :
    ((simplePoleResidueCoordinate (k := k) (F := F) P omega :
      P.valuationRing) : F) =
      (P.uniformizerInValuationRing : F) *
        functionFieldDifferentialCoordinate (k := k) (F := F)
          (omega : Differential k F) *
        (functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F))⁻¹ :=
  rfl

private theorem coordinate_uniformizerLogDifferential (P : GlobalPlace k F) :
    functionFieldDifferentialCoordinate (k := k) (F := F)
        (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) =
      (P.uniformizerInValuationRing : F)⁻¹ *
        functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F) := by
  change functionFieldDifferentialCoordinate (k := k) (F := F)
      (logarithmicDifferential (k := k) (F := F)
        (P.uniformizerInValuationRing : F)) = _
  rw [logarithmicDifferential, map_smul,
    functionFieldDifferentialCoordinate_differential]
  rfl

/-- A simple-pole differential is reconstructed from its regular residue
coordinate and the normalized uniformizer logarithmic differential. -/
theorem simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
    (P : GlobalPlace k F) (omega : simplePoleDifferentialLattice P) :
    (omega : Differential k F) =
      simplePoleResidueCoordinate (k := k) (F := F) P omega •
        (uniformizerLogDifferential (k := k) (F := F) P : Differential k F) := by
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let a : F := functionFieldDerivation (k := k) (F := F) (pi : F)
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  have hpi_ne : (pi : F) ≠ 0 := by
    change P.uniformizer ≠ 0
    apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have ha_ne : a ≠ 0 :=
    functionFieldDerivation_uniformizer_ne_zero (k := k) (F := F) P
  apply (functionFieldDifferentialEquiv (k := k) (F := F)).injective
  change C (omega : Differential k F) =
    C (simplePoleResidueCoordinate (k := k) (F := F) P omega •
      (uniformizerLogDifferential (k := k) (F := F) P : Differential k F))
  rw [C.map_smul_of_tower, coordinate_uniformizerLogDifferential]
  change C (omega : Differential k F) =
    ((simplePoleResidueCoordinate (k := k) (F := F) P omega :
      P.valuationRing) : F) * ((pi : F)⁻¹ * a)
  rw [coe_simplePoleResidueCoordinate]
  change C (omega : Differential k F) =
    ((pi : F) * C (omega : Differential k F) * a⁻¹) * ((pi : F)⁻¹ * a)
  field_simp [hpi_ne, ha_ne]

/-- The normalized simple-pole residue is reduction of the explicit regular
residue coordinate. -/
theorem simplePoleResidue_eq_residueCoordinate (P : GlobalPlace k F)
    (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P omega =
      P.residue (simplePoleResidueCoordinate (k := k) (F := F) P omega) := by
  let r : P.valuationRing :=
    simplePoleResidueCoordinate (k := k) (F := F) P omega
  have homega : omega = r •
        uniformizerLogDifferential (k := k) (F := F) P := by
    apply Subtype.ext
    exact simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
      (k := k) (F := F) P omega
  calc
    simplePoleResidue (k := k) (F := F) P omega =
        simplePoleResidue (k := k) (F := F) P
          (r • uniformizerLogDifferential (k := k) (F := F) P) :=
      congrArg (simplePoleResidue (k := k) (F := F) P) homega
    _ = P.residue r * simplePoleResidue (k := k) (F := F) P
        (uniformizerLogDifferential (k := k) (F := F) P) :=
      simplePoleResidue_smul (k := k) (F := F) P r
        (uniformizerLogDifferential (k := k) (F := F) P)
    _ = P.residue r := by
      rw [simplePoleResidue_uniformizerLogDifferential, mul_one]
    _ = P.residue
        (simplePoleResidueCoordinate (k := k) (F := F) P omega) := rfl

end Differential

end QEC.Coding.AlgebraicGeometry

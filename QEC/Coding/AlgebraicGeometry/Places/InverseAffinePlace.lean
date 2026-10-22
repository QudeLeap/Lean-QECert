/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Places.AffinePlace
import QEC.Coding.AlgebraicGeometry.Places.InverseChart
import Mathlib.FieldTheory.Separable

/-!
# Transporting the affine-place construction through `X ↦ X⁻¹`

The second chart of a function field is not an assumed family of places.  This
file constructs its coefficient algebra by composing the existing
`k⟮X⟯ → F` map with the concrete rational-function involution which sends
`X` to `X⁻¹`.  `Module.Finite.of_equiv_equiv` and
`Algebra.IsSeparable.of_equiv_equiv` then transport exactly the instances
required by `AffinePlace`.

The equality with `InverseChart.rationalMap` is kept explicit: it is the
compatibility statement which says that the two independently constructed
presentations of the inverse chart have the same map into `F`.  No valuation
extension, classification of places, product formula, or Riemann--Roch result
is assumed or asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

namespace InverseAffinePlace

open scoped IntermediateField Polynomial RatFunc

section RationalTransport

variable (k : Type*) [Field k]

/-- The reciprocal of the rational-function variable is transcendental. -/
theorem inverseVariable_transcendental :
    Transcendental k ((RatFunc.X : RatFunc k)⁻¹) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)

/-- Adjoining the reciprocal variable already recovers the whole rational
function field: the original variable is its inverse. -/
theorem adjoin_inverseVariable_eq_top :
    k⟮((RatFunc.X : RatFunc k)⁻¹)⟯ = ⊤ := by
  apply top_unique
  rw [← RatFunc.adjoin_X]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  change (RatFunc.X : RatFunc k) ∈ IntermediateField.adjoin k {(RatFunc.X : RatFunc k)⁻¹}
  simpa only [inv_inv] using
    (IntermediateField.adjoin k {((RatFunc.X : RatFunc k)⁻¹)}).inv_mem
      (IntermediateField.subset_adjoin k {((RatFunc.X : RatFunc k)⁻¹)}
        (Set.mem_singleton _))

/-- The actual rational-function coordinate involution used by the second
chart. -/
noncomputable def rationalInvolution : RatFunc k ≃ₐ[k] RatFunc k :=
  (RatFunc.algEquivOfTranscendental ((RatFunc.X : RatFunc k)⁻¹)
    (inverseVariable_transcendental k)).trans
    ((IntermediateField.equivOfEq (adjoin_inverseVariable_eq_top k)).trans
      IntermediateField.topEquiv)

/-- The rational involution sends the variable to its reciprocal. -/
theorem rationalInvolution_X :
    rationalInvolution k RatFunc.X = (RatFunc.X : RatFunc k)⁻¹ := by
  simp [rationalInvolution]

variable (F : Type*) [Field F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]

/-- The inverse-chart rational map obtained by transporting the original
coefficient map across the rational involution. -/
noncomputable def transportedRationalMap : RatFunc k →+* F :=
  (algebraMap k⟮X⟯ F).comp (rationalInvolution k).toRingEquiv.toRingHom

/-- Algebra structure on `F` induced by the transported inverse-chart map. -/
@[reducible] noncomputable def transportedRationalAlgebra : Algebra k⟮X⟯ F :=
  (transportedRationalMap k F).toAlgebra

/-- Polynomial coefficient map for the transported inverse affine chart. -/
noncomputable def transportedPolynomialMap : k[X] →+* F :=
  (transportedRationalMap (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)).comp (algebraMap k[X] k⟮X⟯)

/-- Polynomial algebra for the transported inverse affine chart. -/
@[reducible] noncomputable def transportedPolynomialAlgebra : Algebra k[X] F :=
  (transportedPolynomialMap (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)).toAlgebra

/-- The transported polynomial and rational maps form the required tower. -/
theorem transportedScalarTower :
    let : Algebra k⟮X⟯ F := transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    IsScalarTower k[X] k⟮X⟯ F := by
  let : Algebra k⟮X⟯ F := transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  let : FaithfulSMul k[X] F :=
    (faithfulSMul_iff_algebraMap_injective k[X] F).mpr <| by
      change Function.Injective (transportedPolynomialMap (k := k) (F := F)
        (oldRationalAlgebra := oldRationalAlgebra))
      exact (transportedRationalMap (k := k) (F := F)
        (oldRationalAlgebra := oldRationalAlgebra)).injective.comp
          (IsFractionRing.injective k[X] k⟮X⟯)
  let liftRationalAlgebra : Algebra k⟮X⟯ F := by
    let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    exact RatFunc.liftAlgebra k F
  have hAlgebra : transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra) = liftRationalAlgebra := by
    apply Algebra.algebra_ext
    intro x
    let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    let : Algebra k⟮X⟯ F := liftRationalAlgebra
    let : IsScalarTower k[X] k⟮X⟯ F := RatFunc.isScalarTower_liftAlgebra k F
    have hMaps : transportedRationalMap (k := k) (F := F)
        (oldRationalAlgebra := oldRationalAlgebra) = algebraMap k⟮X⟯ F := by
      apply IsFractionRing.ringHom_ext (A := k[X])
      intro p
      change transportedRationalMap (k := k) (F := F)
          (oldRationalAlgebra := oldRationalAlgebra) (algebraMap k[X] k⟮X⟯ p) =
        algebraMap k⟮X⟯ F (algebraMap k[X] k⟮X⟯ p)
      exact IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F p
    exact RingHom.congr_fun hMaps x
  rw [hAlgebra]
  exact RatFunc.isScalarTower_liftAlgebra k F

variable [oldFunctionField : _root_.FunctionField k F]

/-- Finite-dimensionality over the inverse-chart rational-function field,
transported from the original function-field structure by the involution. -/
theorem transportedFunctionField :
    @FunctionField k F _ _ (transportedRationalAlgebra k F) := by
  exact @Module.Finite.of_equiv_equiv (RatFunc k) F (RatFunc k) F
    _ _ _ _ oldRationalAlgebra (transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra))
    (rationalInvolution k).symm.toRingEquiv (RingEquiv.refl F) (by
      ext x
      change algebraMap k⟮X⟯ F
        (rationalInvolution k ((rationalInvolution k).symm x)) = algebraMap k⟮X⟯ F x
      simp) oldFunctionField

omit oldFunctionField
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

/-- Separability over the inverse-chart rational-function field, transported
from the existing separable function-field presentation by the same concrete
involution. -/
theorem transportedIsSeparable :
    @Algebra.IsSeparable k⟮X⟯ F _ _ (transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)) := by
  exact @Algebra.IsSeparable.of_equiv_equiv (RatFunc k) F (RatFunc k) F
    _ _ _ _ oldRationalAlgebra (transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra))
    (rationalInvolution k).symm.toRingEquiv (RingEquiv.refl F) (by
      ext x
      change algebraMap k⟮X⟯ F
        (rationalInvolution k ((rationalInvolution k).symm x)) = algebraMap k⟮X⟯ F x
      simp) oldSeparable

end RationalTransport

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

/-- The constant-field algebra induced by the existing rational-function
coefficient map.  It is local to this transport, avoiding a competing global
`Algebra k F` instance. -/
@[reducible] noncomputable def constantAlgebra : Algebra k F :=
  ((algebraMap k⟮X⟯ F).comp (algebraMap k k⟮X⟯)).toAlgebra

/-- The preceding constant algebra is definitionally compatible with the
given rational-function coefficient map. -/
@[reducible] noncomputable def constantScalarTower :
    letI : Algebra k F := constantAlgebra k F
    IsScalarTower k k⟮X⟯ F := by
  letI : Algebra k F := constantAlgebra k F
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

omit [Finite k] in
/-- The transported map sends the fresh chart variable to the reciprocal of
the original coordinate in `F`. -/
theorem transportedRationalMap_X :
    transportedRationalMap k F RatFunc.X = InverseChart.inverseCoordinate k F := by
  change algebraMap k⟮X⟯ F (rationalInvolution k RatFunc.X) =
    InverseChart.inverseCoordinate k F
  rw [rationalInvolution_X, map_inv₀]
  rfl

/-- The transported inverse chart supplies the same `X ↦ t⁻¹` rational map as
`InverseChart.rationalMap`.  This is proved by fraction-field extensionality:
both maps agree on constants and on the polynomial variable. -/
theorem inverseChartRationalMap_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.rationalMap k F).toRingHom = transportedRationalMap k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  apply IsFractionRing.ringHom_ext (A := k[X])
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow]
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      change InverseChart.rationalMap k F (RatFunc.C a) *
          InverseChart.rationalMap k F RatFunc.X ^ n =
        transportedRationalMap k F (RatFunc.C a) *
          transportedRationalMap k F RatFunc.X ^ n
      rw [InverseChart.rationalMap_X, transportedRationalMap_X]
      congr 1
      change ↑((InverseChart.rationalEquiv k F) (RatFunc.C a)) =
        algebraMap k⟮X⟯ F (rationalInvolution k (RatFunc.C a))
      rw [show RatFunc.C a = algebraMap k (RatFunc k) a from rfl,
        AlgEquiv.commutes, AlgEquiv.commutes]
      rfl

/-- The inverse-chart algebra specified in `InverseChart` is therefore the
same algebra as the one for which finite-dimensionality and separability were
transported above. -/
theorem inverseChartRationalAlgebra_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.rationalMap k F).toRingHom.toAlgebra = transportedRationalAlgebra k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  rw [show (InverseChart.rationalMap k F).toRingHom = transportedRationalMap k F from
    inverseChartRationalMap_eq_transported k F]

/-- The polynomial maps agree after the rational-map compatibility is made
explicit, so the inverse-chart polynomial algebra is not a second assumed
chart structure. -/
theorem inverseChartPolynomialMap_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.polynomialMap k F) = transportedPolynomialMap k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  simp only [InverseChart.polynomialMap, transportedPolynomialMap]
  rw [inverseChartRationalMap_eq_transported k F]

/-- Equality of the concrete polynomial maps gives equality of their induced
algebra structures. -/
theorem inverseChartPolynomialAlgebra_eq_transported :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.polynomialMap k F).toAlgebra = transportedPolynomialAlgebra k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  rw [show InverseChart.polynomialMap k F = transportedPolynomialMap k F from
    inverseChartPolynomialMap_eq_transported k F]

/-- The height-one-prime carrier for the inverse affine chart.  Every required
algebra, tower, finite-dimensionality, and separability instance is built
above from concrete maps and equivalences. -/
noncomputable abbrev carrier : Type _ :=
  letI : Algebra k⟮X⟯ F := transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  letI : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  letI : IsScalarTower k[X] k⟮X⟯ F := transportedScalarTower (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  letI : _root_.FunctionField k F := transportedFunctionField (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
  letI : Algebra.IsSeparable k⟮X⟯ F := transportedIsSeparable (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
  AffinePlace.carrier k F

end InverseAffinePlace

end QEC.Coding.AlgebraicGeometry

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import Mathlib.RingTheory.Kaehler.Basic
import QEC.Coding.AlgebraicGeometry.Differentials.SeparableDerivationExtension

/-!
# Function-field differentials

This module starts the #722 differential layer from Mathlib's actual module of
Kähler differentials.  It contains no canonical-divisor, residue, genus, or
Riemann--Roch conclusion: those require the local-to-global valuation theory
constructed in later valuation modules.
-/

namespace QEC.Coding.AlgebraicGeometry

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

/-- The actual `k`-linear Kähler differential module of the function field
`F`. -/
abbrev Differential : Type _ := KaehlerDifferential k F

/-- The universal `k`-derivation into the function-field differential module.
This is Mathlib's construction, not a formal symbol carrying residue or
canonical-divisor laws. -/
noncomputable def differential : F →ₗ[k] Differential k F :=
  (KaehlerDifferential.D k F).toLinearMap

@[simp]
theorem differential_zero : differential k F 0 = 0 :=
  (differential k F).map_zero

@[simp]
theorem differential_add (f g : F) :
    differential k F (f + g) = differential k F f + differential k F g :=
  (differential k F).map_add f g

/-- Leibniz's rule for the actual universal differential. -/
theorem differential_mul (f g : F) :
    differential k F (f * g) = f • differential k F g + g • differential k F f := by
  exact (KaehlerDifferential.D k F).leibniz f g

@[simp]
theorem differential_algebraMap (a : k) :
    differential k F (algebraMap k F a) = 0 := by
  exact (KaehlerDifferential.D k F).map_algebraMap a

/-- Universal differentials span the actual Kähler differential module. -/
theorem differential_span_range :
    Submodule.span F (Set.range (differential k F)) = ⊤ := by
  change Submodule.span F (Set.range (KaehlerDifferential.D k F)) = ⊤
  exact KaehlerDifferential.span_range_derivation k F

/-- Every derivation from the function field factors through its actual
universal differential module.  This is the interface later residue and
canonical-divisor constructions must use instead of carrying a residue law as
data. -/
noncomputable def Differential.lift {M : Type*} [AddCommGroup M] [Module k M]
    [Module F M] [IsScalarTower k F M] (D : Derivation k F M) :
    Differential k F →ₗ[F] M :=
  D.liftKaehlerDifferential

/-- The universal factorization recovers the original derivation on every
function-field element. -/
theorem Differential.lift_differential {M : Type*} [AddCommGroup M] [Module k M]
    [Module F M] [IsScalarTower k F M] (D : Derivation k F M) (f : F) :
    Differential.lift k F D (differential k F f) = D f :=
  D.liftKaehlerDifferential_comp_D f

end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry

namespace FunctionFieldDifferential

open scoped RatFunc

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-- The extension to `F` of the rational derivation with value `1` at `X`. -/
noncomputable def functionFieldDerivation : Derivation k F F :=
  SeparableDerivationExtension.separableDerivationExtension (k := k) (F := F)
    (RatFuncDerivation.rationalDerivation (k := k) (M := F) 1)

/-- The chosen function-field derivation evaluates to `1` on the rational
generator. -/
theorem functionFieldDerivation_apply_X :
    functionFieldDerivation (k := k) (F := F)
      (algebraMap (RatFunc k) F RatFunc.X) = 1 := by
  rw [functionFieldDerivation,
    SeparableDerivationExtension.separableDerivationExtension_apply_algebraMap]
  exact RatFuncDerivation.rationalDerivation_apply_X (k := k) (1 : F)

/-- The universal differential of the rational generator. -/
noncomputable def functionFieldDifferentialGenerator : Differential k F :=
  differential k F (algebraMap (RatFunc k) F RatFunc.X)

/-- The coordinate on differentials induced by the chosen function-field
derivation. -/
noncomputable def functionFieldDifferentialCoordinate : Differential k F →ₗ[F] F :=
  Differential.lift k F (functionFieldDerivation (k := k) (F := F))

/-- The `F`-linear map sending a scalar to that scalar times `dX`. -/
noncomputable def functionFieldDifferentialGeneratorMap : F →ₗ[F] Differential k F :=
  (LinearMap.id : F →ₗ[F] F).smulRight
    (functionFieldDifferentialGenerator (k := k) (F := F))

/-- The coordinate sends `dX` to `1`. -/
theorem functionFieldDifferentialCoordinate_generator :
    functionFieldDifferentialCoordinate (k := k) (F := F)
      (functionFieldDifferentialGenerator (k := k) (F := F)) = 1 := by
  unfold functionFieldDifferentialCoordinate functionFieldDifferentialGenerator
  rw [Differential.lift_differential]
  exact functionFieldDerivation_apply_X (k := k) (F := F)

/-- Restriction and evaluation at `X` expose the value of a derivation of the
separable function field. -/
private theorem separableDerivationValueEquiv_apply_X
    (D : Derivation k F (Differential k F)) :
    SeparableDerivationExtension.separableDerivationValueEquiv (k := k) (F := F)
      (M := Differential k F) D = D (algebraMap (RatFunc k) F RatFunc.X) :=
  rfl

/-- The coordinate and scalar-multiple maps compose to the identity on `F`. -/
theorem functionFieldDifferentialCoordinate_comp_generatorMap :
    (functionFieldDifferentialCoordinate (k := k) (F := F)).comp
      (functionFieldDifferentialGeneratorMap (k := k) (F := F)) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change functionFieldDifferentialCoordinate (k := k) (F := F)
      (a • functionFieldDifferentialGenerator (k := k) (F := F)) = a
  simpa only [map_smul, functionFieldDifferentialCoordinate_generator, smul_eq_mul, mul_one]

/-- The coordinate and scalar-multiple maps compose to the identity on the
module of Kähler differentials. -/
theorem functionFieldDifferentialGeneratorMap_comp_coordinate :
    (functionFieldDifferentialGeneratorMap (k := k) (F := F)).comp
      (functionFieldDifferentialCoordinate (k := k) (F := F)) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply (SeparableDerivationExtension.separableDerivationValueEquiv (k := k) (F := F)
    (M := Differential k F)).injective
  rw [separableDerivationValueEquiv_apply_X, separableDerivationValueEquiv_apply_X]
  change functionFieldDifferentialGeneratorMap (k := k) (F := F)
      (functionFieldDifferentialCoordinate (k := k) (F := F)
        (functionFieldDifferentialGenerator (k := k) (F := F))) =
      functionFieldDifferentialGenerator (k := k) (F := F)
  rw [functionFieldDifferentialCoordinate_generator]
  simp only [functionFieldDifferentialGeneratorMap, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul]

/-- The Kähler differential module of the separable function field is a
free rank-one `F`-module, with coordinate determined by `dX`. -/
noncomputable def functionFieldDifferentialEquiv : Differential k F ≃ₗ[F] F :=
  LinearEquiv.ofLinear
    (functionFieldDifferentialCoordinate (k := k) (F := F))
    (functionFieldDifferentialGeneratorMap (k := k) (F := F))
    (functionFieldDifferentialCoordinate_comp_generatorMap (k := k) (F := F))
    (functionFieldDifferentialGeneratorMap_comp_coordinate (k := k) (F := F))

/-- The chosen differential generator is nonzero. -/
theorem functionFieldDifferentialGenerator_ne_zero :
    functionFieldDifferentialGenerator (k := k) (F := F) ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (functionFieldDifferentialCoordinate (k := k) (F := F)) hzero
  rw [functionFieldDifferentialCoordinate_generator,
    map_zero] at hcoordinate
  exact one_ne_zero hcoordinate

/-- Every function-field differential is its coordinate times the chosen
global differential generator. -/
theorem functionFieldDifferential_eq_coordinate_smul_generator
    (omega : Differential k F) :
    omega = functionFieldDifferentialCoordinate (k := k) (F := F) omega •
      functionFieldDifferentialGenerator (k := k) (F := F) := by
  have h := congrArg (fun L : Differential k F →ₗ[F] Differential k F => L omega)
    (functionFieldDifferentialGeneratorMap_comp_coordinate (k := k) (F := F))
  simpa only [LinearMap.comp_apply, functionFieldDifferentialGeneratorMap,
    LinearMap.smulRight_apply, LinearMap.id_apply] using h.symm

/-- The differential coordinate evaluates a universal differential through the
constructed separable function-field derivation. -/
theorem functionFieldDifferentialCoordinate_differential (f : F) :
    functionFieldDifferentialCoordinate (k := k) (F := F) (differential k F f) =
      functionFieldDerivation (k := k) (F := F) f := by
  simpa only [functionFieldDifferentialCoordinate] using
    (Differential.lift_differential (k := k) (F := F)
      (functionFieldDerivation (k := k) (F := F)) f)

/-- The universal differential of a function is its function-field derivative
times the chosen global differential generator. -/
theorem differential_eq_functionFieldDerivation_smul_generator (f : F) :
    differential k F f = functionFieldDerivation (k := k) (F := F) f •
      functionFieldDifferentialGenerator (k := k) (F := F) := by
  calc
    differential k F f =
        functionFieldDifferentialCoordinate (k := k) (F := F) (differential k F f) •
          functionFieldDifferentialGenerator (k := k) (F := F) :=
      functionFieldDifferential_eq_coordinate_smul_generator (k := k) (F := F) _
    _ = functionFieldDerivation (k := k) (F := F) f •
          functionFieldDifferentialGenerator (k := k) (F := F) := by
      rw [functionFieldDifferentialCoordinate_differential]

/-- A universal differential vanishes exactly when its function-field
derivative vanishes. -/
theorem differential_ne_zero_iff_functionFieldDerivation_ne_zero (f : F) :
    differential k F f ≠ 0 ↔ functionFieldDerivation (k := k) (F := F) f ≠ 0 := by
  constructor
  · intro hdifferential hderivation
    apply hdifferential
    rw [differential_eq_functionFieldDerivation_smul_generator, hderivation, zero_smul]
  · intro hderivation hdifferential
    have hsmul : functionFieldDerivation (k := k) (F := F) f •
        functionFieldDifferentialGenerator (k := k) (F := F) = 0 := by
      rw [← differential_eq_functionFieldDerivation_smul_generator]
      exact hdifferential
    rcases smul_eq_zero.mp hsmul with hvalue | hgenerator
    · exact hderivation hvalue
    · exact functionFieldDifferentialGenerator_ne_zero (k := k) (F := F) hgenerator

end FunctionFieldDifferential

end QEC.Coding.AlgebraicGeometry

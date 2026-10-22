import QEC.Coding.AlgebraicGeometry.Differentials.DerivationTrace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Trace of function-field differentials

For a finite separable extension `F / k(X)`, this module constructs the
`k(X)`-linear trace on Kähler differentials.  In the global `dX` coordinates
it applies the field trace to the coefficient, and on exact differentials it
commutes with the universal differential.

This is the algebraic trace bridge toward residue transport.  It does not
assert local residue compatibility, a global residue theorem, duality, genus,
or Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry
namespace FunctionFieldDifferential

open scoped RatFunc

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-- The differential trace applies the field trace to the global `dX`
coordinate. -/
noncomputable def functionFieldDifferentialTrace :
    Differential k F →ₗ[RatFunc k] Differential k (RatFunc k) :=
  (functionFieldDifferentialGeneratorMap (k := k) (F := RatFunc k)).comp
    ((Algebra.trace (RatFunc k) F).comp
      ((functionFieldDifferentialCoordinate (k := k) (F := F)).restrictScalars
        (RatFunc k)))

/-- Evaluation of the differential trace in the global `dX` coordinate. -/
theorem functionFieldDifferentialTrace_apply (omega : Differential k F) :
    functionFieldDifferentialTrace (k := k) (F := F) omega =
      Algebra.trace (RatFunc k) F
          (functionFieldDifferentialCoordinate (k := k) (F := F) omega) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) :=
  rfl

private theorem rationalDerivation_eq_functionFieldDerivation :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1 =
      functionFieldDerivation (k := k) (F := RatFunc k) := by
  have h := RatFuncDerivation.rationalDerivation_eq_of_apply_X
    (k := k) (D := functionFieldDerivation (k := k) (F := RatFunc k))
  have hX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 :=
    functionFieldDerivation_apply_X (k := k) (F := RatFunc k)
  rw [hX] at h
  exact h

/-- Differential trace commutes with the universal differential. -/
theorem functionFieldDifferentialTrace_differential (x : F) :
    functionFieldDifferentialTrace (k := k) (F := F) (differential k F x) =
      differential k (RatFunc k) (Algebra.trace (RatFunc k) F x) := by
  rw [functionFieldDifferentialTrace_apply,
    functionFieldDifferentialCoordinate_differential,
    functionFieldDifferential_eq_coordinate_smul_generator
      (k := k) (F := RatFunc k)
      (differential k (RatFunc k) (Algebra.trace (RatFunc k) F x)),
    functionFieldDifferentialCoordinate_differential,
    ← rationalDerivation_eq_functionFieldDerivation]
  rw [functionFieldDerivation_trace]

end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry

import QEC.Coding.AlgebraicGeometry.Residues.Global.FunctionFieldGlobalResidue
import QEC.Coding.AlgebraicGeometry.RiemannRoch.ResidueSupportSum

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Vanishing of the one-place Riemann--Roch residue pairing

The product differential associated to `x ∈ L(G + P)` and
`y ∈ L((ω) - G)` is regular away from `P`.  Its global traced-residue sum is
therefore its coefficient at `P`; the function-field global residue theorem
forces that coefficient to vanish.

This module proves this one-place vanishing consequence only.  It does not
assert perfect duality, a genus or canonical-degree formula, or
Riemann--Roch.
-/

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry.Differential

open FunctionFieldDifferential

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

/-- The selected traced residue of the actual one-place Riemann--Roch product
differential vanishes. -/
theorem globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) P = 0 := by
  exact
    (globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected
      omega homega G P x y).symm.trans
      (globalSimplePoleResidueSum_eq_zero (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y))

end QEC.Coding.AlgebraicGeometry.Differential

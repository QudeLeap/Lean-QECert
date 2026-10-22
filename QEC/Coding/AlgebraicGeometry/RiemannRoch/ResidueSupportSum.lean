import QEC.Coding.AlgebraicGeometry.RiemannRoch.ResidueProduct

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The one-place Riemann--Roch residue sum

The finite traced-residue sum of the product differential associated to
`x ∈ L(G + P)` and `y ∈ L((ω) - G)` is its coefficient at `P`, because every
other coefficient vanishes by the local support calculation.

This support reduction does not assert that the selected coefficient is zero
and does not prove the general global residue theorem, duality, genus, or
Riemann--Roch.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The finite residue sum of a one-place product differential is its
selected-place coefficient.  This is a support identity only; no vanishing
of that coefficient is asserted. -/
theorem globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidueSum (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) =
      globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) P := by
  classical
  rw [globalSimplePoleResidueSum]
  apply Finsupp.sum_eq_single P
  · intro Q _ hQP
    exact
      globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero_of_ne
        omega homega G P Q hQP x y
  · intro _
    rfl

end Differential

end QEC.Coding.AlgebraicGeometry

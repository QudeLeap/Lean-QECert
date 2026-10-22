import QEC.Coding.AlgebraicGeometry.RiemannRoch.PlaceIncrement

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Dimension growth under one-place increments

The kernel calculation for the actual one-place leading-coefficient map gives
an injection of the quotient `L(G + P) / L(G)` into the residue field at `P`.
This module packages the embedded copy of `L(G)` as a linear equivalence and
derives the resulting residue-degree bound on dimension growth.

The leading-coefficient map need not be surjective.  No global residue
theorem, duality, genus, or Riemann--Roch identity is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace GlobalPlace

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The copy of `L(G)` inside `L(G + P)` is linearly equivalent to `L(G)`
itself. -/
noncomputable def riemannRochPlaceIncrementEquiv
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    riemannRochSubmodule G ≃ₗ[k] riemannRochPlaceIncrementSubmodule G P where
  toFun x :=
    ⟨⟨x.1, riemannRochSubmodule_le_add_placeDivisor G P x.property⟩, x.property⟩
  invFun x := ⟨x.1.1, x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Enlarging an actual all-place Riemann--Roch divisor by one place raises
its dimension by at most the residue degree of that place. -/
theorem riemannRochDimension_add_placeDivisor_le
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    [FiniteDimensional k (riemannRochSubmodule G)]
    [FiniteDimensional k (riemannRochSubmodule (G + placeDivisor P))] :
    riemannRochDimension (G + placeDivisor P) ≤
      riemannRochDimension G + residueDegree (k := k) (F := F) P := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional P
  let leadingCoefficient := riemannRochPlaceLeadingCoefficient G P
  have hrank := leadingCoefficient.finrank_range_add_finrank_ker
  have hrange :
      Module.finrank k (LinearMap.range leadingCoefficient) ≤
        Module.finrank k P.residueField :=
    (LinearMap.range leadingCoefficient).finrank_le
  have hkernel :
      Module.finrank k (LinearMap.ker leadingCoefficient) =
        Module.finrank k (riemannRochPlaceIncrementSubmodule G P) := by
    rw [riemannRochPlaceLeadingCoefficient_ker]
  have hincrement :
      Module.finrank k (riemannRochSubmodule G) =
        Module.finrank k (riemannRochPlaceIncrementSubmodule G P) :=
    LinearEquiv.finrank_eq (riemannRochPlaceIncrementEquiv G P)
  have hresidue := residueDegree_eq_finrank P
  unfold riemannRochDimension
  omega

end GlobalPlace

end QEC.Coding.AlgebraicGeometry

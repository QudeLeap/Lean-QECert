import QEC.Coding.AlgebraicGeometry.Differentials.LocalUniformizerDerivative

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Local differential orders and lattices

This module identifies the intrinsic local order of a nonzero differential
with membership in the actual regular and simple-pole differential lattices.
It uses the already-proved fact that the derivative of the normalized
uniformizer is a principal-cutoff generator of the local derivative lattice.

No residue sum, canonical-degree formula, or Riemann--Roch theorem is stated.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- A nonzero differential is regular at a place exactly when its intrinsic
local differential order is nonnegative. -/
theorem mem_localDifferentialLattice_iff_differentialOrder_nonnegative
    (P : GlobalPlace k F) (omega : Differential k F) (homega : omega ≠ 0) :
    omega ∈ localDifferentialLattice P ↔
      0 ≤ differentialOrder (k := k) (F := F) P omega homega := by
  let a : F := functionFieldDerivation (k := k) (F := F)
    (P.uniformizerInValuationRing : F)
  have ha := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (k := k) (F := F) P
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr
      homega
  rw [mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
    (k := k) (F := F) P omega, ha.2.2]
  simp only [hcoordinate, false_or]
  rw [differentialOrder_eq_coordinate_sub_generatorOrder
    (k := k) (F := F) P omega homega ha]
  omega

/-- Multiplying a nonzero differential by the normalized uniformizer raises
its intrinsic local order by one. -/
theorem differentialOrder_uniformizer_smul
    (P : GlobalPlace k F) (omega : Differential k F) (homega : omega ≠ 0) :
    differentialOrder (k := k) (F := F) P
        ((P.uniformizerInValuationRing : F) • omega)
        (smul_ne_zero
          (by
            simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
              localParameter_ne_zero (k := k) (F := F) P)
          homega) =
      differentialOrder (k := k) (F := F) P omega homega + 1 := by
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff (k := k) (F := F) omega).mpr
      homega
  simp only [differentialOrder, map_smul, smul_eq_mul]
  rw [GlobalPlace.order_mul P hpi hcoordinate]
  change P.order P.uniformizer +
      P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
        localDerivativeLatticeGeneratorOrder (k := k) (F := F) P =
    P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
        localDerivativeLatticeGeneratorOrder (k := k) (F := F) P + 1
  rw [P.order_uniformizer]
  ring

/-- A nonzero differential has at most a simple pole at a place exactly when
its intrinsic local differential order is at least `-1`. -/
theorem mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
    (P : GlobalPlace k F) (omega : Differential k F) (homega : omega ≠ 0) :
    omega ∈ simplePoleDifferentialLattice P ↔
      -1 ≤ differentialOrder (k := k) (F := F) P omega homega := by
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  change (P.uniformizerInValuationRing : F) • omega ∈
      localDifferentialLattice P ↔
    -1 ≤ differentialOrder (k := k) (F := F) P omega homega
  rw [mem_localDifferentialLattice_iff_differentialOrder_nonnegative
    (k := k) (F := F) P ((P.uniformizerInValuationRing : F) • omega)
    (smul_ne_zero hpi homega)]
  rw [differentialOrder_uniformizer_smul (k := k) (F := F) P omega homega]
  omega

end Differential

end QEC.Coding.AlgebraicGeometry

import QEC.Coding.AlgebraicGeometry.Differentials.LocalDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Residues.Local.Residue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Local product laws for normalized residues

This module proves the order and lattice-membership formulas for scaling a
nonzero differential by a nonzero function.  It also records the exact
valuation-ring linearity of the normalized simple-pole residue and its
vanishing for scalars in the maximal ideal.

These are local inputs for a later residue pairing.  No global residue,
duality, genus, or Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- Scaling a nonzero differential by a nonzero function adds their local
orders. -/
theorem differentialOrder_smul (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    differentialOrder (k := k) (F := F) P (f • omega)
        (smul_ne_zero hf homega) =
      P.order f + differentialOrder (k := k) (F := F) P omega homega := by
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega ≠ 0 :=
    (functionFieldDifferentialCoordinate_ne_zero_iff
      (k := k) (F := F) omega).mpr homega
  simp only [differentialOrder, map_smul, smul_eq_mul]
  rw [GlobalPlace.order_mul P hf hcoordinate]
  ring

/-- A function-scaled nonzero differential is regular exactly when the sum
of the function order and differential order is nonnegative. -/
theorem smul_mem_localDifferentialLattice_iff_order_add_nonnegative
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    f • omega ∈ localDifferentialLattice P ↔
      0 ≤ P.order f + differentialOrder (k := k) (F := F) P omega homega := by
  rw [mem_localDifferentialLattice_iff_differentialOrder_nonnegative
    (k := k) (F := F) P (f • omega) (smul_ne_zero hf homega)]
  rw [differentialOrder_smul (k := k) (F := F) P f hf omega homega]

/-- A function-scaled nonzero differential has at most a simple pole exactly
when its summed local order is at least `-1`. -/
theorem smul_mem_simplePoleDifferentialLattice_iff_order_add_neg_one
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    f • omega ∈ simplePoleDifferentialLattice P ↔
      -1 ≤ P.order f + differentialOrder (k := k) (F := F) P omega homega := by
  rw [mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
    (k := k) (F := F) P (f • omega) (smul_ne_zero hf homega)]
  rw [differentialOrder_smul (k := k) (F := F) P f hf omega homega]

/-- The normalized simple-pole residue is linear over the valuation ring;
the induced scalar on the residue field is the actual reduction of the
regular function. -/
theorem simplePoleResidue_smul (P : GlobalPlace k F)
    (f : P.valuationRing) (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P (f • omega) =
      P.residue f * simplePoleResidue (k := k) (F := F) P omega := by
  rw [map_smul, Algebra.smul_def,
    IsLocalRing.ResidueField.algebraMap_eq]
  rfl

/-- A regular scalar in the maximal ideal kills every normalized
simple-pole residue. -/
theorem simplePoleResidue_smul_eq_zero_of_mem_maximalIdeal
    (P : GlobalPlace k F) (f : P.valuationRing)
    (hf : f ∈ IsLocalRing.maximalIdeal P.valuationRing)
    (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P (f • omega) = 0 := by
  rw [simplePoleResidue_smul (k := k) (F := F) P f omega,
    (P.residue_eq_zero_iff f).mpr hf, zero_mul]

end Differential

end QEC.Coding.AlgebraicGeometry

import Mathlib.RingTheory.Trace.Basic
import QEC.Coding.AlgebraicGeometry.Differentials.LocalDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Residues.Local.Residue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Finite global simple-pole residue data

For a differential having at most a simple pole at every global place, this
module traces each normalized local residue from the actual place residue
field to the constant field.  The resulting coefficient family has finite
support, so it defines an honest `Finsupp` and a finite global sum.

This module does not prove that the finite sum vanishes.  It also does not
construct residues for higher-order poles, a Laurent expansion, a duality
theorem, or a Riemann--Roch formula.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace Differential

open FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

omit [IsScalarTower k (RatFunc k) F] in
private theorem residueField_finiteDimensional (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
    FiniteDimensional k P.residueField := by
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : Finite P.residueField := GlobalPlace.finite_residueField P
  exact (Module.finite_iff_finite).mpr inferInstance

/-- The constant-field trace of the normalized residue of a differential with
at most a simple pole at `P`. -/
noncomputable def simplePoleTraceResidue (P : GlobalPlace k F)
    (omega : Differential k F)
    (homega : omega ∈ simplePoleDifferentialLattice P) : k := by
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional (k := k) (F := F) P
  exact Algebra.trace k P.residueField
    (simplePoleResidue (k := k) (F := F) P ⟨omega, homega⟩)

/-- A regular differential has zero traced simple-pole residue. -/
theorem simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (P : GlobalPlace k F) (omega : Differential k F)
    (homegaSimple : omega ∈ simplePoleDifferentialLattice P)
    (homegaRegular : omega ∈ localDifferentialLattice P) :
    simplePoleTraceResidue (k := k) (F := F) P omega homegaSimple = 0 := by
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional (k := k) (F := F) P
  change Algebra.trace k P.residueField
      (simplePoleResidue (k := k) (F := F) P ⟨omega, homegaSimple⟩) = 0
  rw [simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) P ⟨omega, homegaSimple⟩ homegaRegular, map_zero]

/-- A differential has globally at most simple poles when it belongs to every
actual local simple-pole lattice. -/
def IsGlobalSimplePole (omega : Differential k F) : Prop :=
  ∀ P : GlobalPlace k F, omega ∈ simplePoleDifferentialLattice P

/-- The traced normalized residue coefficient at a global place. -/
noncomputable def globalSimplePoleResidueCoefficient
    (omega : Differential k F) (homega : IsGlobalSimplePole omega)
    (P : GlobalPlace k F) : k :=
  simplePoleTraceResidue (k := k) (F := F) P omega (homega P)

/-- The traced residue coefficients of a globally simple-pole differential
have finite support. -/
theorem globalSimplePoleResidueCoefficient_support_finite
    (omega : Differential k F) (homega : IsGlobalSimplePole omega) :
    (Function.support fun P : GlobalPlace k F =>
      globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P).Finite := by
  by_cases homegaZero : omega = 0
  · subst omega
    have hzero : (fun P : GlobalPlace k F =>
        globalSimplePoleResidueCoefficient (k := k) (F := F) 0 homega P) = 0 := by
      funext P
      exact simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P 0 (homega P) (localDifferentialLattice P).zero_mem
    rw [hzero]
    simp [Function.support]
  · refine (differentialOrder_support_finite (k := k) (F := F)
      omega homegaZero).subset ?_
    intro P hP
    simp only [Function.mem_support, ne_eq] at hP ⊢
    intro horder
    apply hP
    apply simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P omega (homega P)
    apply (mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := F) P omega homegaZero).mpr
    rw [horder]

/-- The finitely supported family of traced normalized local residues. -/
noncomputable def globalSimplePoleResidue
    (omega : Differential k F) (homega : IsGlobalSimplePole omega) :
    GlobalPlace k F →₀ k :=
  Finsupp.ofSupportFinite
    (fun P => globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P)
    (globalSimplePoleResidueCoefficient_support_finite
      (k := k) (F := F) omega homega)

/-- A coefficient of the global residue `Finsupp` is the traced normalized
local residue at that place. -/
theorem globalSimplePoleResidue_apply
    (omega : Differential k F) (homega : IsGlobalSimplePole omega)
    (P : GlobalPlace k F) :
    globalSimplePoleResidue (k := k) (F := F) omega homega P =
      globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P :=
  rfl

/-- The finite sum of the traced normalized local residues.  Its vanishing is
the separate global residue theorem and is not asserted here. -/
noncomputable def globalSimplePoleResidueSum
    (omega : Differential k F) (homega : IsGlobalSimplePole omega) : k :=
  (globalSimplePoleResidue (k := k) (F := F) omega homega).sum
    (fun _ residue => residue)

end Differential

end QEC.Coding.AlgebraicGeometry

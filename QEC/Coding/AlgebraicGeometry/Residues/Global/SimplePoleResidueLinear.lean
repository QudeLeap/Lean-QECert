import QEC.Coding.AlgebraicGeometry.Residues.Global.SimplePoleResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Additivity of global simple-pole residues

The actual local simple-pole lattices are closed under addition, and their
normalized residue maps and constant-field traces are linear.  This module
packages those facts for the finitely supported global residue family and its
finite sum.  The finite-sum theorem is the compositional interface needed to
assemble a partial-fraction decomposition.

This module does not prove that an arbitrary rational differential has at most
simple poles, does not prove the global residue theorem, and does not construct
duality, genus, or a Riemann--Roch formula.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped BigOperators Polynomial RatFunc

namespace Differential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- The zero differential has at most a simple pole at every global place. -/
theorem isGlobalSimplePole_zero :
    IsGlobalSimplePole (k := k) (F := F) (0 : Differential k F) := by
  intro P
  exact (simplePoleDifferentialLattice P).zero_mem

/-- A sum of two globally simple-pole differentials is globally simple-pole. -/
theorem IsGlobalSimplePole.add {omega eta : Differential k F}
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    IsGlobalSimplePole (k := k) (F := F) (omega + eta) := by
  intro P
  exact (simplePoleDifferentialLattice P).add_mem (homega P) (heta P)

/-- The traced residue of the zero differential is zero. -/
theorem simplePoleTraceResidue_zero (P : GlobalPlace k F) :
    simplePoleTraceResidue (k := k) (F := F) P 0
      (simplePoleDifferentialLattice P).zero_mem = 0 := by
  exact simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) P 0 (simplePoleDifferentialLattice P).zero_mem
      (localDifferentialLattice P).zero_mem

/-- The constant-field trace of the normalized simple-pole residue is
additive. -/
theorem simplePoleTraceResidue_add (P : GlobalPlace k F)
    (omega eta : Differential k F)
    (homega : omega ∈ simplePoleDifferentialLattice P)
    (heta : eta ∈ simplePoleDifferentialLattice P) :
    simplePoleTraceResidue (k := k) (F := F) P (omega + eta)
        ((simplePoleDifferentialLattice P).add_mem homega heta) =
      simplePoleTraceResidue (k := k) (F := F) P omega homega +
        simplePoleTraceResidue (k := k) (F := F) P eta heta := by
  simp only [simplePoleTraceResidue]
  rw [show
    (⟨omega + eta, (simplePoleDifferentialLattice P).add_mem homega heta⟩ :
      simplePoleDifferentialLattice P) =
        ⟨omega, homega⟩ + ⟨eta, heta⟩ by rfl]
  rw [map_add, map_add]

/-- The finitely supported global residue family of zero is zero. -/
theorem globalSimplePoleResidue_zero :
    globalSimplePoleResidue (k := k) (F := F) 0
      (isGlobalSimplePole_zero (k := k) (F := F)) = 0 := by
  ext P
  rw [globalSimplePoleResidue_apply]
  exact simplePoleTraceResidue_zero (k := k) (F := F) P

/-- The finitely supported global residue family is additive. -/
theorem globalSimplePoleResidue_add (omega eta : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    globalSimplePoleResidue (k := k) (F := F) (omega + eta)
        (homega.add heta) =
      globalSimplePoleResidue (k := k) (F := F) omega homega +
        globalSimplePoleResidue (k := k) (F := F) eta heta := by
  ext P
  rw [globalSimplePoleResidue_apply, Finsupp.add_apply,
    globalSimplePoleResidue_apply, globalSimplePoleResidue_apply]
  exact simplePoleTraceResidue_add (k := k) (F := F) P omega eta
    (homega P) (heta P)

/-- The finite global residue sum of zero is zero. -/
theorem globalSimplePoleResidueSum_zero :
    globalSimplePoleResidueSum (k := k) (F := F) 0
      (isGlobalSimplePole_zero (k := k) (F := F)) = 0 := by
  rw [globalSimplePoleResidueSum, globalSimplePoleResidue_zero]
  exact Finsupp.sum_zero_index

/-- The finite global residue sum is additive. -/
theorem globalSimplePoleResidueSum_add (omega eta : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    globalSimplePoleResidueSum (k := k) (F := F) (omega + eta)
        (homega.add heta) =
      globalSimplePoleResidueSum (k := k) (F := F) omega homega +
        globalSimplePoleResidueSum (k := k) (F := F) eta heta := by
  rw [globalSimplePoleResidueSum, globalSimplePoleResidue_add]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- A finite sum of globally simple-pole differentials is globally
simple-pole. -/
theorem IsGlobalSimplePole.finset_sum {ι : Type*} (s : Finset ι)
    (omega : ι → Differential k F)
    (homega : ∀ i, IsGlobalSimplePole (k := k) (F := F) (omega i)) :
    IsGlobalSimplePole (k := k) (F := F) (∑ i ∈ s, omega i) := by
  intro P
  exact Submodule.sum_mem (simplePoleDifferentialLattice P)
    (fun i _ => homega i P)

/-- The global residue sum of a finite sum is the finite sum of the global
residue sums. -/
theorem globalSimplePoleResidueSum_finset_sum {ι : Type*} (s : Finset ι)
    (omega : ι → Differential k F)
    (homega : ∀ i, IsGlobalSimplePole (k := k) (F := F) (omega i)) :
    globalSimplePoleResidueSum (k := k) (F := F) (∑ i ∈ s, omega i)
        (IsGlobalSimplePole.finset_sum s omega homega) =
      ∑ i ∈ s, globalSimplePoleResidueSum (k := k) (F := F)
        (omega i) (homega i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.notMem_empty, Finset.sum_empty] using
        (globalSimplePoleResidueSum_zero (k := k) (F := F))
  | @insert i s hi ih =>
      calc
        globalSimplePoleResidueSum (k := k) (F := F)
            (∑ j ∈ insert i s, omega j)
            (IsGlobalSimplePole.finset_sum (insert i s) omega homega) =
            globalSimplePoleResidueSum (k := k) (F := F)
                (omega i) (homega i) +
              globalSimplePoleResidueSum (k := k) (F := F)
                (∑ j ∈ s, omega j)
                (IsGlobalSimplePole.finset_sum s omega homega) := by
          simpa only [Finset.sum_insert hi] using
            (globalSimplePoleResidueSum_add (k := k) (F := F)
              (omega i) (∑ j ∈ s, omega j) (homega i)
              (IsGlobalSimplePole.finset_sum s omega homega))
        _ = ∑ j ∈ insert i s, globalSimplePoleResidueSum
              (k := k) (F := F) (omega j) (homega j) := by
          rw [ih, Finset.sum_insert hi]

end Differential

end QEC.Coding.AlgebraicGeometry

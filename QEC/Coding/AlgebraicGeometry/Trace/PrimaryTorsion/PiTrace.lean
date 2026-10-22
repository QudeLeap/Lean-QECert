import Mathlib.LinearAlgebra.Pi
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.TraceFunctorial

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Primary-torsion trace on a finite product

The finite-depth primary trace is additive over a finite sum of
endomorphisms.  Decomposing an endomorphism of a finite product by coordinate
inclusions and projections, then applying cyclicity, identifies its primary
trace with the sum of the primary traces of its diagonal coordinate blocks.

The proof is symbolic.  It does not enumerate a product, choose bases or a
Smith form, or assert a residue, duality, genus, or Riemann--Roch formula.
-/

namespace QEC.Coding.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R]

/-- The finite primary-torsion trace is additive over a finite sum of
endomorphisms. -/
theorem primaryTorsionTrace_sum
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (p : Ideal R) [p.IsMaximal]
    {ι : Type w} (s : Finset ι) (f : ι → M →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (∑ i ∈ s, f i) n =
      ∑ i ∈ s, primaryTorsionTrace p (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using primaryTorsionTrace_zero p n
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, primaryTorsionTrace_add, ih,
        Finset.sum_insert ha]

variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type w}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The diagonal coordinate block of an endomorphism of a finite product. -/
def piDiagonalBlock (f : (∀ i, M i) →ₗ[R] ∀ i, M i) (i : ι) :
    M i →ₗ[R] M i :=
  (LinearMap.proj i).comp
    (f.comp (LinearMap.single R M i))

private theorem piEndomorphism_eq_sum_components
    (f : (∀ i, M i) →ₗ[R] ∀ i, M i) :
    f = ∑ i, (f.comp (LinearMap.single R M i)).comp
      (LinearMap.proj i) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.single_apply]
  change f x = ∑ i, f (Pi.single i (x i))
  rw [← map_sum, LinearMap.sum_single_apply]

/-- The primary-torsion trace of an endomorphism of a finite product is the
sum of the primary traces of its diagonal coordinate blocks. -/
theorem primaryTorsionTrace_pi_eq_sum_diagonal
    [IsNoetherianRing R] [∀ i, Module.Finite R (M i)]
    [Module.Finite R (∀ i, M i)]
    (p : Ideal R) [p.IsMaximal]
    (f : (∀ i, M i) →ₗ[R] ∀ i, M i) (n : ℕ) :
    primaryTorsionTrace (M := ∀ i, M i) p f n =
      ∑ i, primaryTorsionTrace (M := M i) p
        (piDiagonalBlock f i) n := by
  let component : ι → ((∀ i, M i) →ₗ[R] ∀ i, M i) := fun i =>
    (f.comp (LinearMap.single R M i)).comp (LinearMap.proj i)
  have hdecomp : f = ∑ i, component i :=
    piEndomorphism_eq_sum_components f
  calc
    _ = primaryTorsionTrace (M := ∀ i, M i) p
        (∑ i, component i) n :=
      congrArg (fun g => primaryTorsionTrace p g n) hdecomp
    _ = ∑ i, primaryTorsionTrace (M := ∀ i, M i) p
        (component i) n := by
      simpa only using
        (primaryTorsionTrace_sum p Finset.univ component n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      change primaryTorsionTrace (M := ∀ j, M j) p
          ((f.comp (LinearMap.single R M i)).comp
            (LinearMap.proj i)) n =
        primaryTorsionTrace (M := M i) p
          ((LinearMap.proj i).comp
            (f.comp (LinearMap.single R M i))) n
      exact primaryTorsionTrace_comp_comm
        (M := ∀ j, M j) (N := M i) p
        (LinearMap.proj i) (f.comp (LinearMap.single R M i)) n

end QEC.Coding.AlgebraicGeometry

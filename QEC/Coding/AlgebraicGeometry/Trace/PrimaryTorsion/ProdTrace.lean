import Mathlib.LinearAlgebra.Prod
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.TraceFunctorial

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Primary trace on a binary product

The finite-depth primary-torsion trace of a product endomorphism is the sum
of the traces of its two coordinate endomorphisms.  The proof decomposes the
product map through the actual coordinate inclusions and projections, then
uses additivity and cyclicity of the established primary trace.

This is a symbolic module identity.  It does not enumerate quotient rings,
choose bases, compute residues, or assert a duality, genus, or
Riemann--Roch formula.
-/

namespace QEC.Coding.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Primary torsion trace is additive on a binary product endomorphism. -/
theorem primaryTorsionTrace_prodMap_eq_add
    [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (depth : ℕ) :
    primaryTorsionTrace p (f.prodMap g) depth =
      primaryTorsionTrace p f depth + primaryTorsionTrace p g depth := by
  let left : M →ₗ[R] M × N := (LinearMap.inl R M N).comp f
  let right : N →ₗ[R] M × N := (LinearMap.inr R M N).comp g
  have hdecomp : f.prodMap g =
      left.comp (LinearMap.fst R M N) +
        right.comp (LinearMap.snd R M N) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp [left, right]
  have hleft := primaryTorsionTrace_comp_comm p
    (LinearMap.fst R M N) left depth
  have hright := primaryTorsionTrace_comp_comm p
    (LinearMap.snd R M N) right depth
  have hleftMap : (LinearMap.fst R M N).comp left = f := by
    apply LinearMap.ext
    intro x
    rfl
  have hrightMap : (LinearMap.snd R M N).comp right = g := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hdecomp, primaryTorsionTrace_add]
  exact congrArg₂ (· + ·)
    (hleft.trans (congrArg (fun h ↦ primaryTorsionTrace p h depth) hleftMap))
    (hright.trans (congrArg (fun h ↦ primaryTorsionTrace p h depth) hrightMap))

end QEC.Coding.AlgebraicGeometry

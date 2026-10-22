import Mathlib.LinearAlgebra.Trace
import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.Grade

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Trace on successive grades of primary torsion

For a finite module over a Noetherian ring, every successive primary-torsion
grade is finite over the quotient ring.  This module takes the trace of the
endomorphism induced on each grade and sums those traces through a prescribed
finite depth.

The construction is additive in the endomorphism.  It does not identify the
grades with cyclic modules, compute a Smith multiplicity, enumerate a finite
carrier, or prove a residue, duality, genus, or Riemann--Roch theorem.
-/

namespace QEC.Coding.AlgebraicGeometry

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A primary torsion grade of a finite module over a Noetherian ring is
finite over the quotient ring.  This is a named non-instance so the quotient
module and its finiteness can be installed together in downstream proofs. -/
@[implicit_reducible]
noncomputable def primaryTorsionGradeFinite [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) := by
  let h := primaryTorsionGrade_annihilated (M := M) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := h.module
  letI : Module.Finite R (primaryTorsionGrade p M i) := inferInstance
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ p)
    (primaryTorsionGrade p M i)

/-- Trace of an endomorphism on one successive primary-torsion grade. -/
noncomputable def primaryTorsionGradeTrace [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (i : ℕ) : R ⧸ p := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  exact LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i)
    (primaryTorsionGradeEndomorphism p f i)

/-- Sum of the induced traces on the first `n` primary-torsion grades. -/
noncomputable def primaryTorsionTrace [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] M) (n : ℕ) : R ⧸ p :=
  ∑ i ∈ Finset.range n, primaryTorsionGradeTrace p f i

private theorem primaryTorsionGradeEndomorphism_zero (p : Ideal R) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p (0 : M →ₗ[R] M) i = 0 := by
  letI := primaryTorsionGradeModule (M := M) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeEndomorphism_mk]
      rfl

private theorem primaryTorsionGradeEndomorphism_add (p : Ideal R)
    (f g : M →ₗ[R] M) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p (f + g) i =
      primaryTorsionGradeEndomorphism p f i +
        primaryTorsionGradeEndomorphism p g i := by
  letI := primaryTorsionGradeModule (M := M) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      simp only [LinearMap.add_apply]
      rw [primaryTorsionGradeEndomorphism_mk,
        primaryTorsionGradeEndomorphism_mk,
        primaryTorsionGradeEndomorphism_mk]
      rfl

/-- The finite primary-torsion trace of the zero endomorphism is zero. -/
theorem primaryTorsionTrace_zero [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal] (n : ℕ) :
    primaryTorsionTrace p (0 : M →ₗ[R] M) n = 0 := by
  classical
  rw [primaryTorsionTrace]
  apply Finset.sum_eq_zero
  intro i hi
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  rw [primaryTorsionGradeTrace, primaryTorsionGradeEndomorphism_zero,
    map_zero]

/-- The finite primary-torsion trace is additive in the endomorphism. -/
theorem primaryTorsionTrace_add [IsNoetherianRing R]
    [Module.Finite R M] (p : Ideal R) [p.IsMaximal]
    (f g : M →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (f + g) n =
      primaryTorsionTrace p f n + primaryTorsionTrace p g n := by
  classical
  rw [primaryTorsionTrace, primaryTorsionTrace, primaryTorsionTrace,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  rw [primaryTorsionGradeTrace, primaryTorsionGradeTrace,
    primaryTorsionGradeTrace, primaryTorsionGradeEndomorphism_add, map_add]

end QEC.Coding.AlgebraicGeometry

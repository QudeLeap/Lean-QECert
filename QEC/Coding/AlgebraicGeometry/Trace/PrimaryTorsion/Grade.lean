import Mathlib.Algebra.Module.Torsion.Basic

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Successive grades of primary torsion

For an ideal `p`, this module forms the increasing filtration of a module by
elements annihilated by `p ^ i`.  Every successive quotient is annihilated by
`p`, hence carries the canonical quotient-ring scalar action.  An arbitrary
linear endomorphism preserves the filtration and descends to a linear
endomorphism of each quotient-ring grade.

These constructions are the memory-bounded algebraic substrate for a later
primary trace.  There is no trace formula, Smith multiplicity computation,
residue theorem, duality, genus, or Riemann--Roch statement here.
-/

namespace QEC.Coding.AlgebraicGeometry

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Elements annihilated by every scalar in `p ^ i`. -/
def primaryTorsionLayer (p : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (i : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M (p ^ i : Ideal R)

/-- The primary torsion layers form an increasing filtration. -/
theorem primaryTorsionLayer_mono (p : Ideal R) (i j : ℕ) (hij : i ≤ j) :
    primaryTorsionLayer p M i ≤ primaryTorsionLayer p M j := by
  exact Submodule.torsionBySet_le_torsionBySet_pow i j hij p

private def primaryTorsionPreviousLayer (p : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Submodule R (primaryTorsionLayer p M (i + 1)) :=
  (primaryTorsionLayer p M i).comap
    (primaryTorsionLayer p M (i + 1)).subtype

/-- The quotient between two consecutive primary torsion layers. -/
abbrev primaryTorsionGrade (p : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (i : ℕ) :=
  primaryTorsionLayer p M (i + 1) ⧸
    primaryTorsionPreviousLayer p M i

/-- Every consecutive primary torsion grade is annihilated by `p`. -/
theorem primaryTorsionGrade_annihilated (p : Ideal R) (i : ℕ) :
    Module.IsTorsionBySet R (primaryTorsionGrade p M i) p := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x r hr
  change (r : R) • (x : M) ∈ primaryTorsionLayer p M i
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  have har : (a : R) * (r : R) ∈ p ^ (i + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul a.property hr
  have hx : ((a : R) * (r : R)) • (x : M) = 0 :=
    (Submodule.mem_torsionBySet_iff (R := R)
      (s := (p ^ (i + 1) : Ideal R)) (x : M)).mp x.property ⟨_, har⟩
  simpa only [smul_smul] using hx

/-- The canonical quotient-ring module structure on a primary torsion grade.
It is a named non-instance so downstream proofs can install it locally. -/
@[implicit_reducible]
noncomputable def primaryTorsionGradeModule (p : Ideal R) (i : ℕ) :
    Module (R ⧸ p) (primaryTorsionGrade p M i) :=
  (primaryTorsionGrade_annihilated (M := M) p i).module

private theorem primaryTorsionLayer_invariant (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    primaryTorsionLayer p M i ≤
      (primaryTorsionLayer p M i).comap f := by
  intro x hx
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx
  change f x ∈ primaryTorsionLayer p M i
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  rw [← f.map_smul, hx a, map_zero]

/-- Restriction of an endomorphism to one primary torsion layer. -/
def primaryTorsionLayerEndomorphism (p : Ideal R) (f : M →ₗ[R] M)
    (i : ℕ) :
    primaryTorsionLayer p M i →ₗ[R] primaryTorsionLayer p M i :=
  (f.domRestrict (primaryTorsionLayer p M i)).codRestrict
    (primaryTorsionLayer p M i)
      (fun x => primaryTorsionLayer_invariant p f i x.property)

private theorem primaryTorsionPreviousLayer_invariant (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    primaryTorsionPreviousLayer p M i ≤
      (primaryTorsionPreviousLayer p M i).comap
        (primaryTorsionLayerEndomorphism p f (i + 1)) := by
  intro x hx
  change f (x : M) ∈ primaryTorsionLayer p M i
  exact primaryTorsionLayer_invariant p f i hx

private def primaryTorsionGradeEndomorphismR (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    primaryTorsionGrade p M i →ₗ[R] primaryTorsionGrade p M i :=
  (primaryTorsionPreviousLayer p M i).mapQ
    (primaryTorsionPreviousLayer p M i)
    (primaryTorsionLayerEndomorphism p f (i + 1))
    (primaryTorsionPreviousLayer_invariant p f i)

/-- The endomorphism induced on a primary torsion grade, linear over the
quotient ring `R ⧸ p`. -/
noncomputable def primaryTorsionGradeEndomorphism (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGrade p M i →ₗ[R ⧸ p] primaryTorsionGrade p M i := by
  let h := primaryTorsionGrade_annihilated (M := M) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := h.module
  let fR := primaryTorsionGradeEndomorphismR p f i
  exact
    { toFun := fR
      map_add' := fR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change fR (Ideal.Quotient.mk p r • x) =
              Ideal.Quotient.mk p r • fR x
            rw [Module.IsTorsionBySet.mk_smul h,
              Module.IsTorsionBySet.mk_smul h]
            exact fR.map_smul r x }

/-- On a quotient representative, the induced grade endomorphism is the
class of the restricted original endomorphism. -/
theorem primaryTorsionGradeEndomorphism_mk (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeEndomorphism p f i
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (primaryTorsionLayerEndomorphism p f (i + 1) x) :=
  rfl

end QEC.Coding.AlgebraicGeometry

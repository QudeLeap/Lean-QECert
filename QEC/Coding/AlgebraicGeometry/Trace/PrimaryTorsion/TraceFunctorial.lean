import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.Trace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Functoriality of primary-torsion traces

An `R`-linear map preserves every power-torsion layer and therefore induces
a map between the corresponding successive grades.  Composition is preserved.
Consequently, the trace of a composite through another finite module is
cyclic on every grade and on every prescribed finite depth.

This is a symbolic functoriality result.  It does not enumerate a finite
module, choose a Smith decomposition, compute a multiplicity, or prove a
residue, duality, genus, or Riemann--Roch statement.
-/

namespace QEC.Coding.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

private theorem primaryTorsionLayer_map_le (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionLayer p M i ≤
      (primaryTorsionLayer p N i).comap f := by
  intro x hx
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx
  change f x ∈ primaryTorsionLayer p N i
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  rw [← f.map_smul, hx a, map_zero]

/-- Restriction of a linear map to corresponding primary-torsion layers. -/
def primaryTorsionLayerMap (p : Ideal R) (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionLayer p M i →ₗ[R] primaryTorsionLayer p N i :=
  (f.domRestrict (primaryTorsionLayer p M i)).codRestrict
    (primaryTorsionLayer p N i)
      (fun x => primaryTorsionLayer_map_le p f i x.property)

private def primaryTorsionPreviousLayerAt (p : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Submodule R (primaryTorsionLayer p M (i + 1)) :=
  (primaryTorsionLayer p M i).comap
    (primaryTorsionLayer p M (i + 1)).subtype

private theorem primaryTorsionPreviousLayer_map_le (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionPreviousLayerAt p M i ≤
      (primaryTorsionPreviousLayerAt p N i).comap
        (primaryTorsionLayerMap p f (i + 1)) := by
  intro x hx
  change f (x : M) ∈ primaryTorsionLayer p N i
  exact primaryTorsionLayer_map_le p f i hx

private def primaryTorsionGradeMapR (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionGrade p M i →ₗ[R] primaryTorsionGrade p N i := by
  change
    (primaryTorsionLayer p M (i + 1) ⧸
        primaryTorsionPreviousLayerAt p M i) →ₗ[R]
      (primaryTorsionLayer p N (i + 1) ⧸
        primaryTorsionPreviousLayerAt p N i)
  exact (primaryTorsionPreviousLayerAt p M i).mapQ
    (primaryTorsionPreviousLayerAt p N i)
    (primaryTorsionLayerMap p f (i + 1))
    (primaryTorsionPreviousLayer_map_le p f i)

/-- The map induced on a primary-torsion grade by an arbitrary linear map,
linear over the residue quotient `R ⧸ p`. -/
noncomputable def primaryTorsionGradeMap (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGrade p M i →ₗ[R ⧸ p] primaryTorsionGrade p N i := by
  let hM := primaryTorsionGrade_annihilated (M := M) p i
  let hN := primaryTorsionGrade_annihilated (M := N) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := hM.module
  letI : Module (R ⧸ p) (primaryTorsionGrade p N i) := hN.module
  let fR := primaryTorsionGradeMapR p f i
  exact
    { toFun := fR
      map_add' := fR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change fR (Ideal.Quotient.mk p r • x) =
              Ideal.Quotient.mk p r • fR x
            rw [Module.IsTorsionBySet.mk_smul hM,
              Module.IsTorsionBySet.mk_smul hN]
            exact fR.map_smul r x }

/-- The induced grade map sends a quotient representative to the class of
its image in the target torsion layer. -/
theorem primaryTorsionGradeMap_mk (p : Ideal R) (f : M →ₗ[R] N)
    (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeMap p f i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (primaryTorsionLayerMap p f (i + 1) x) :=
  rfl

/-- Passing to a primary-torsion grade preserves composition. -/
theorem primaryTorsionGradeMap_comp
    {P : Type*} [AddCommGroup P] [Module R P]
    (p : Ideal R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    letI := primaryTorsionGradeModule (M := P) p i
    primaryTorsionGradeMap p (g.comp f) i =
      (primaryTorsionGradeMap p g i).comp
        (primaryTorsionGradeMap p f i) := by
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  letI := primaryTorsionGradeModule (M := P) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeMap_mk]
      simp only [LinearMap.comp_apply]
      rw [primaryTorsionGradeMap_mk, primaryTorsionGradeMap_mk]
      rfl

private theorem primaryTorsionGradeMap_self_eq_endomorphism
    (p : Ideal R) (f : M →ₗ[R] M) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGradeMap p f i =
      primaryTorsionGradeEndomorphism p f i := by
  letI := primaryTorsionGradeModule (M := M) p i
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeMap_mk,
        primaryTorsionGradeEndomorphism_mk]
      rfl

/-- The trace on one primary-torsion grade is cyclic for a composite through
another finite module. -/
theorem primaryTorsionGradeTrace_comp_comm [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (i : ℕ) :
    primaryTorsionGradeTrace p (g.comp f) i =
      primaryTorsionGradeTrace p (f.comp g) i := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p N i) :=
    primaryTorsionGradeFinite (M := N) p i
  change LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i)
      (primaryTorsionGradeEndomorphism p (g.comp f) i) =
    LinearMap.trace (R ⧸ p) (primaryTorsionGrade p N i)
      (primaryTorsionGradeEndomorphism p (f.comp g) i)
  rw [← primaryTorsionGradeMap_self_eq_endomorphism,
    ← primaryTorsionGradeMap_self_eq_endomorphism,
    primaryTorsionGradeMap_comp, primaryTorsionGradeMap_comp]
  exact LinearMap.trace_comp_comm'
    (primaryTorsionGradeMap p f i) (primaryTorsionGradeMap p g i)

/-- The finite primary-torsion trace is cyclic for a composite through
another finite module. -/
theorem primaryTorsionTrace_comp_comm [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N]
    (p : Ideal R) [p.IsMaximal]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (n : ℕ) :
    primaryTorsionTrace p (g.comp f) n =
      primaryTorsionTrace p (f.comp g) n := by
  rw [primaryTorsionTrace, primaryTorsionTrace]
  apply Finset.sum_congr rfl
  intro i hi
  exact primaryTorsionGradeTrace_comp_comm p f g i

end QEC.Coding.AlgebraicGeometry

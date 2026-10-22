import QEC.Coding.AlgebraicGeometry.Trace.PrimaryTorsion.Trace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Invariance of the primary torsion trace

An `R`-linear equivalence carries the `p`-power torsion filtration to the
corresponding filtration of the target module.  It therefore induces a
quotient-field linear equivalence on every successive grade.  Intertwining
endomorphisms are conjugate on those grades, so their finite primary torsion
traces agree.

This is a functoriality result only.  It does not compute a cyclic grade,
Smith multiplicity, residue, divisor, genus, or Riemann--Roch term.
-/

namespace QEC.Coding.AlgebraicGeometry

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private theorem primaryTorsionLayer_map_equiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    (primaryTorsionLayer p M i).map (e : M →ₗ[R] N) =
      primaryTorsionLayer p N i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ primaryTorsionLayer p M i := hx
    rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx'
    have hy' : e x ∈
        Submodule.torsionBySet R N (p ^ i : Ideal R) := by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      rw [← e.map_smul, hx' a, map_zero]
    exact hy'
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hy
    have hx' : e.symm y ∈
        Submodule.torsionBySet R M (p ^ i : Ideal R) := by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      apply e.injective
      rw [e.map_smul, e.apply_symm_apply, map_zero]
      exact hy a
    exact hx'

/-- An `R`-linear equivalence induces an equivalence between corresponding
levels of the primary-torsion filtration. -/
noncomputable def primaryTorsionLayerEquiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    primaryTorsionLayer p M i ≃ₗ[R] primaryTorsionLayer p N i :=
  e.ofSubmodules _ _ (primaryTorsionLayer_map_equiv p e i)

private def primaryTorsionPreviousLayerAt (p : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Submodule R (primaryTorsionLayer p M (i + 1)) :=
  (primaryTorsionLayer p M i).comap
    (primaryTorsionLayer p M (i + 1)).subtype

private theorem primaryTorsionPreviousLayerAt_map_equiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    (primaryTorsionPreviousLayerAt p M i).map
        (primaryTorsionLayerEquiv p e (i + 1) :
          primaryTorsionLayer p M (i + 1) →ₗ[R]
            primaryTorsionLayer p N (i + 1)) =
      primaryTorsionPreviousLayerAt p N i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e (x : M) ∈ primaryTorsionLayer p N i
    rw [← primaryTorsionLayer_map_equiv p e i]
    exact Submodule.mem_map_of_mem hx
  · intro hy
    refine ⟨(primaryTorsionLayerEquiv p e (i + 1)).symm y, ?_,
      (primaryTorsionLayerEquiv p e (i + 1)).apply_symm_apply y⟩
    change e.symm (y : N) ∈ primaryTorsionLayer p M i
    rw [← primaryTorsionLayer_map_equiv p e.symm i]
    exact Submodule.mem_map_of_mem hy

private noncomputable def primaryTorsionGradeEquivR (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    primaryTorsionGrade p M i ≃ₗ[R] primaryTorsionGrade p N i := by
  change
    (primaryTorsionLayer p M (i + 1) ⧸
        primaryTorsionPreviousLayerAt p M i) ≃ₗ[R]
      (primaryTorsionLayer p N (i + 1) ⧸
        primaryTorsionPreviousLayerAt p N i)
  exact Submodule.Quotient.equiv
    (primaryTorsionPreviousLayerAt p M i)
    (primaryTorsionPreviousLayerAt p N i)
    (primaryTorsionLayerEquiv p e (i + 1))
    (primaryTorsionPreviousLayerAt_map_equiv p e i)

/-- The equivalence induced by an `R`-linear equivalence on one successive
primary-torsion grade, linear over `R ⧸ p`. -/
noncomputable def primaryTorsionGradeEquiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGrade p M i ≃ₗ[R ⧸ p]
      primaryTorsionGrade p N i := by
  let hM := primaryTorsionGrade_annihilated (M := M) p i
  let hN := primaryTorsionGrade_annihilated (M := N) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := hM.module
  letI : Module (R ⧸ p) (primaryTorsionGrade p N i) := hN.module
  let eR := primaryTorsionGradeEquivR p e i
  exact
    { toEquiv := eR.toEquiv
      map_add' := eR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change eR (Ideal.Quotient.mk p r • x) =
              Ideal.Quotient.mk p r • eR x
            rw [Module.IsTorsionBySet.mk_smul hM,
              Module.IsTorsionBySet.mk_smul hN]
            exact eR.map_smul r x }

/-- The induced grade equivalence sends a quotient representative to the
class of its image in the target torsion layer. -/
theorem primaryTorsionGradeEquiv_mk (p : Ideal R) (e : M ≃ₗ[R] N)
    (i : ℕ) (x : primaryTorsionLayer p M (i + 1)) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeEquiv p e i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (primaryTorsionLayerEquiv p e (i + 1) x) :=
  rfl

private theorem primaryTorsionGradeEquiv_intertwines (p : Ideal R)
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (i : ℕ) (q : primaryTorsionGrade p M i) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGradeEquiv p e i
        (primaryTorsionGradeEndomorphism p f i q) =
      primaryTorsionGradeEndomorphism p g i
        (primaryTorsionGradeEquiv p e i q) := by
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      rw [primaryTorsionGradeEndomorphism_mk,
        primaryTorsionGradeEquiv_mk,
        primaryTorsionGradeEquiv_mk,
        primaryTorsionGradeEndomorphism_mk]
      congr 2
      apply Subtype.ext
      exact LinearMap.congr_fun hfg (x : M)

/-- Intertwining endomorphisms have equal traces on every successive
primary-torsion grade. -/
theorem primaryTorsionGradeTrace_eq_of_intertwining [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (p : Ideal R) [p.IsMaximal]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (i : ℕ) :
    primaryTorsionGradeTrace p f i = primaryTorsionGradeTrace p g i := by
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI := primaryTorsionGradeModule (M := M) p i
  letI := primaryTorsionGradeModule (M := N) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p M i) :=
    primaryTorsionGradeFinite (M := M) p i
  letI : Module.Finite (R ⧸ p) (primaryTorsionGrade p N i) :=
    primaryTorsionGradeFinite (M := N) p i
  let E := primaryTorsionGradeEquiv p e i
  let fgrade := primaryTorsionGradeEndomorphism p f i
  let ggrade := primaryTorsionGradeEndomorphism p g i
  have hconj : E.conj fgrade = ggrade := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := E.surjective y
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact primaryTorsionGradeEquiv_intertwines p e f g hfg i x
  change LinearMap.trace (R ⧸ p) (primaryTorsionGrade p M i) fgrade =
    LinearMap.trace (R ⧸ p) (primaryTorsionGrade p N i) ggrade
  calc
    _ = LinearMap.trace (R ⧸ p) (primaryTorsionGrade p N i)
        (E.conj fgrade) := (LinearMap.trace_conj' fgrade E).symm
    _ = _ := congrArg (LinearMap.trace (R ⧸ p) _) hconj

/-- Intertwining endomorphisms have equal finite primary-torsion traces. -/
theorem primaryTorsionTrace_eq_of_intertwining [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (p : Ideal R) [p.IsMaximal]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) (g : N →ₗ[R] N)
    (hfg : (e : M →ₗ[R] N).comp f = g.comp (e : M →ₗ[R] N))
    (n : ℕ) : primaryTorsionTrace p f n = primaryTorsionTrace p g n := by
  rw [primaryTorsionTrace, primaryTorsionTrace]
  apply Finset.sum_congr rfl
  intro i hi
  exact primaryTorsionGradeTrace_eq_of_intertwining p e f g hfg i

end QEC.Coding.AlgebraicGeometry

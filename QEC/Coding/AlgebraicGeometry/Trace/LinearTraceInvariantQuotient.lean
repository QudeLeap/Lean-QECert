import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Trace across an invariant subspace and quotient

This module records the finite-dimensional linear-algebra identity that the
trace of an endomorphism preserving a subspace is the sum of its trace on the
subspace and on the quotient.  The proof uses a complementary subspace and
cyclicity of trace; it does not enumerate a basis or a finite carrier.
-/

namespace QEC.Coding.AlgebraicGeometry

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Trace is additive across an invariant subspace and the induced quotient
endomorphism. -/
theorem trace_eq_restrict_add_quotient (f : V →ₗ[K] V) (p : Submodule K V)
    (hf : p ≤ p.comap f) :
    LinearMap.trace K V f =
      LinearMap.trace K p
          ((f.domRestrict p).codRestrict p (fun x => hf x.property)) +
        LinearMap.trace K (V ⧸ p) (p.mapQ p f hf) := by
  classical
  obtain ⟨q, hpq⟩ := p.exists_isCompl
  let fp : p →ₗ[K] p :=
    (f.domRestrict p).codRestrict p (fun x => hf x.property)
  let fq : (V ⧸ p) →ₗ[K] (V ⧸ p) := p.mapQ p f hf
  let pp : V →ₗ[K] p := p.projectionOnto q hpq
  let pq : V →ₗ[K] q := q.projectionOnto p hpq.symm
  let qblock : q →ₗ[K] q := pq.comp (f.comp q.subtype)
  have hdecomposition :
      f = p.subtype.comp (pp.comp f) + q.subtype.comp (pq.comp f) := by
    ext x
    change f x = (pp (f x) : V) + (pq (f x) : V)
    exact (Submodule.projection_add_projection_eq_self hpq (f x)).symm
  have hpblock : (pp.comp f).comp p.subtype = fp := by
    ext x
    change (pp (f (x : V)) : V) = f (x : V)
    have hprojection := Submodule.projectionOnto_apply_left hpq
      (⟨f (x : V), hf x.property⟩ : p)
    exact congrArg Subtype.val hprojection
  let e : (V ⧸ p) ≃ₗ[K] q := p.quotientEquivOfIsCompl q hpq
  have hqblock : e.conj fq = qblock := by
    ext x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have he_symm : e.symm x = Submodule.Quotient.mk (x : V) := by
      change e.symm.toLinearMap x = Submodule.Quotient.mk (x : V)
      rw [Submodule.toLinearMap_symm_quotientEquivOfIsCompl]
      rfl
    rw [he_symm]
    simp only [fq, Submodule.mapQ_apply, qblock, LinearMap.comp_apply]
    exact congrArg Subtype.val
      (Submodule.quotientEquivOfIsCompl_apply_mk hpq (f (x : V)))
  change LinearMap.trace K V f =
    LinearMap.trace K p fp + LinearMap.trace K (V ⧸ p) fq
  calc
    LinearMap.trace K V f = LinearMap.trace K V
        (p.subtype.comp (pp.comp f) + q.subtype.comp (pq.comp f)) := by
      rw [← hdecomposition]
    _ = LinearMap.trace K V (p.subtype.comp (pp.comp f)) +
        LinearMap.trace K V (q.subtype.comp (pq.comp f)) := map_add _ _ _
    _ = LinearMap.trace K p ((pp.comp f).comp p.subtype) +
        LinearMap.trace K q ((pq.comp f).comp q.subtype) := by
      rw [LinearMap.trace_comp_comm' (pp.comp f) p.subtype,
        LinearMap.trace_comp_comm' (pq.comp f) q.subtype]
    _ = LinearMap.trace K p fp + LinearMap.trace K q qblock := by
      rw [hpblock]
      rfl
    _ = LinearMap.trace K p fp + LinearMap.trace K (V ⧸ p) fq := by
      rw [← hqblock, LinearMap.trace_conj']

end LinearMap

end QEC.Coding.AlgebraicGeometry

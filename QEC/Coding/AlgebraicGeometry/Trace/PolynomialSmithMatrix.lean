import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Smith matrices for injective endomorphisms

This module packages the Smith-normal-form basis construction for an injective
endomorphism of a finite free module over a principal ideal domain.  Between a
source basis obtained from the range and the corresponding Smith top basis,
the endomorphism has an actual diagonal matrix with nonzero entries.

The result is stated for a general principal ideal domain so that it can later
be applied to multiplication endomorphisms over a polynomial ring.  There is
no quotient trace, residue, divisor, genus, or Riemann--Roch statement here.
-/

namespace QEC.Coding.AlgebraicGeometry

open Module

variable {R M : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]

/-- An injective endomorphism of a finite free module over a principal ideal
domain is diagonal between suitable source and target bases, and every
diagonal coefficient is nonzero. -/
theorem exists_smith_bases_toMatrix_eq_diagonal {n : ℕ}
    (b : Basis (Fin n) R M) (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a := by
  classical
  let N : Submodule R M := LinearMap.range f
  have hfinrank : Module.finrank R N = Module.finrank R M := by
    exact LinearMap.finrank_range_of_inj hf
  let target : Basis (Fin n) R M :=
    N.smithNormalFormTopBasis b hfinrank
  let rangeBasis : Basis (Fin n) R N :=
    N.smithNormalFormBotBasis b hfinrank
  let a : Fin n → R := N.smithNormalFormCoeffs b hfinrank
  let rangeEquiv : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  let source : Basis (Fin n) R M := rangeBasis.map rangeEquiv.symm
  have hsource (i : Fin n) : f (source i) = a i • target i := by
    calc
      f (source i) = (rangeBasis i : M) := by
        change f ((LinearEquiv.ofInjective f hf).symm (rangeBasis i)) =
          (rangeBasis i : M)
        exact LinearEquiv.ofInjective_symm_apply f (rangeBasis i)
      _ = a i • target i := by
        exact N.smithNormalFormBotBasis_def b hfinrank i
  refine ⟨source, target, a, ?_, ?_⟩
  · intro i
    exact N.smithNormalFormCoeffs_ne_zero b hfinrank i
  · ext i j
    rw [LinearMap.toMatrix_apply, hsource, map_smul, Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]

/-- The Smith bases can be chosen so that every endomorphism commuting with
the injective endomorphism has the same diagonal entries in the source and
target bases. -/
theorem exists_smith_bases_toMatrix_eq_diagonal_of_commute {n : ℕ}
    (b : Basis (Fin n) R M) (f g : M →ₗ[R] M)
    (hf : Function.Injective f) (hcomm : f.comp g = g.comp f) :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
          ∀ i, LinearMap.toMatrix source source g i i =
            LinearMap.toMatrix target target g i i := by
  classical
  obtain ⟨source, target, a, ha, hfdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal b f hf
  refine ⟨source, target, a, ha, hfdiag, ?_⟩
  intro i
  have hmatrix := congrArg (LinearMap.toMatrix source target) hcomm
  rw [LinearMap.toMatrix_comp source source target,
    LinearMap.toMatrix_comp source target target, hfdiag] at hmatrix
  have hii := congrFun (congrFun hmatrix i) i
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hii
  exact mul_left_cancel₀ (ha i) (by simpa only [mul_comm] using hii)

end QEC.Coding.AlgebraicGeometry

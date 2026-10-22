import QEC.Coding.AlgebraicGeometry.RiemannRoch.Dimension

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Principal shifts of all-place Riemann--Roch spaces

Multiplication by a nonzero function identifies the actual all-place
Riemann--Roch spaces whose divisors differ by its principal divisor.  The
resulting linear equivalence proves that the finite-dimensional
Riemann--Roch dimension is invariant under this principal shift.

This is a divisor-equivalence interface.  It does not prove a global residue
theorem, define genus, identify the degree of a canonical divisor, or state
the Riemann--Roch correction formula.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

namespace GlobalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

omit [Algebra k[X] F] [Algebra k⟮X⟯ F]
  [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
  [Algebra.IsSeparable k⟮X⟯ F] in
/-- For a nonzero function, membership in the all-place Riemann--Roch
submodule is exactly coefficientwise nonnegativity of its principal divisor
plus the prescribed divisor. -/
theorem mem_riemannRochSubmodule_iff_order_add_nonnegative
    (G : Divisor (GlobalPlace k F)) {f : F} (hf : f ≠ 0) :
    f ∈ riemannRochSubmodule G ↔
      ∀ P : GlobalPlace k F, 0 ≤ P.order f + G P := by
  rw [mem_riemannRochSubmodule_iff]
  constructor
  · intro h P
    have hlog : WithZero.log (P.valuation f) ≤ G P :=
      (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf)).mpr (h P)
    change 0 ≤ -WithZero.log (P.valuation f) + G P
    omega
  · intro h P
    apply (WithZero.log_le_iff_le_exp
      ((P.valuation).ne_zero_iff.mpr hf)).mp
    have hP := h P
    change 0 ≤ -WithZero.log (P.valuation f) + G P at hP
    omega

/-- Multiplication by `u` identifies the Riemann--Roch space of
`div(u) + G` with the Riemann--Roch space of `G`. -/
noncomputable def riemannRochSubmodule_principal_add_equiv
    (u : Fˣ) (G : Divisor (GlobalPlace k F)) :
    riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) ≃ₗ[k]
      riemannRochSubmodule G where
  toFun x := ⟨(u : F) * (x : F), by
    by_cases hx : (x : F) = 0
    · simpa only [hx, mul_zero] using (riemannRochSubmodule G).zero_mem
    · apply (mem_riemannRochSubmodule_iff_order_add_nonnegative G
        (mul_ne_zero u.ne_zero hx)).mpr
      have hxOrder :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative
          (GlobalPlace.principalDivisor (k := k) (F := F) u + G) hx).mp x.property
      intro P
      have hP := hxOrder P
      rw [Finsupp.add_apply, GlobalPlace.principalDivisor_apply] at hP
      rw [GlobalPlace.order_mul P u.ne_zero hx]
      omega⟩
  invFun x := ⟨((u⁻¹ : Fˣ) : F) * (x : F), by
    by_cases hx : (x : F) = 0
    · simpa only [hx, mul_zero] using
        (riemannRochSubmodule
          (GlobalPlace.principalDivisor (k := k) (F := F) u + G)).zero_mem
    · apply (mem_riemannRochSubmodule_iff_order_add_nonnegative
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G)
        (mul_ne_zero (Units.ne_zero _) hx)).mpr
      have hxOrder :=
        (mem_riemannRochSubmodule_iff_order_add_nonnegative G hx).mp x.property
      intro P
      have hP := hxOrder P
      rw [GlobalPlace.order_mul P (Units.ne_zero _) hx,
        show P.order ((u⁻¹ : Fˣ) : F) = -P.order (u : F) by
          simpa only [Units.val_inv_eq_inv_val] using
            (GlobalPlace.order_inv P (u : F)),
        Finsupp.add_apply, GlobalPlace.principalDivisor_apply]
      omega⟩
  left_inv x := by
    apply Subtype.ext
    change ((u⁻¹ : Fˣ) : F) * ((u : F) * (x : F)) = (x : F)
    simp
  right_inv x := by
    apply Subtype.ext
    change (u : F) * (((u⁻¹ : Fˣ) : F) * (x : F)) = (x : F)
    simp
  map_add' x y := by
    apply Subtype.ext
    change (u : F) * ((x : F) + (y : F)) =
      (u : F) * (x : F) + (u : F) * (y : F)
    exact mul_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    change (u : F) * (c • (x : F)) = c • ((u : F) * (x : F))
    simp only [Algebra.smul_def]
    ring

/-- The finite-dimensional Riemann--Roch dimension is invariant when the
divisor is shifted by an actual principal divisor. -/
theorem riemannRochDimension_principal_add
    (u : Fˣ) (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k
      (riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G))]
    [FiniteDimensional k (riemannRochSubmodule G)] :
    riemannRochDimension
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) =
      riemannRochDimension G := by
  unfold riemannRochDimension
  exact LinearEquiv.finrank_eq
    (riemannRochSubmodule_principal_add_equiv (k := k) (F := F) u G)

end GlobalPlace

end QEC.Coding.AlgebraicGeometry

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Divisors.GlobalPrincipalDegree
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Space

/-!
# Negative-degree Riemann--Roch vanishing

This elementary consequence uses the constructed finite-support product formula
for global principal divisors.  It introduces no Riemann--Roch dimension or
duality assumption.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]

/-- A nonzero Riemann--Roch member gives the coefficientwise nonnegative
divisor required by the degree argument. -/
theorem GlobalPlace.order_add_coefficient_nonnegative_of_mem
    (G : Divisor (GlobalPlace k F)) {f : F}
    (hmem : f ∈ GlobalPlace.riemannRochSubmodule G) (hf : f ≠ 0)
    (P : GlobalPlace k F) :
    0 ≤ GlobalPlace.order P f + G P := by
  have hbound : P.valuation f ≤ WithZero.exp (G P) :=
    (GlobalPlace.mem_riemannRochSubmodule_iff G f).mp hmem P
  have hlog : WithZero.log (P.valuation f) ≤ G P :=
    (WithZero.log_le_iff_le_exp ((P.valuation).ne_zero_iff.mpr hf)).mpr hbound
  change 0 ≤ -WithZero.log (P.valuation f) + G P
  omega

/-- A divisor with a nonzero Riemann--Roch member has nonnegative weighted
degree, because its principal-divisor correction is coefficientwise
nonnegative. -/
theorem GlobalPlace.divisorDegree_nonnegative_of_mem_nonzero
    (G : Divisor (GlobalPlace k F)) {f : F}
    (hmem : f ∈ GlobalPlace.riemannRochSubmodule G) (hf : f ≠ 0) :
    0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G := by
  let u : Fˣ := Units.mk0 f hf
  have hpositive : Divisor.Nonnegative
      (GlobalPlace.principalDivisor (k := k) (F := F) u + G) := by
    intro P
    rw [Finsupp.add_apply, GlobalPlace.principalDivisor_apply]
    exact
      (GlobalPlace.order_add_coefficient_nonnegative_of_mem k F G hmem hf P)
  have hdegree :
      0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) :=
    Divisor.degree_nonnegative (GlobalPlace.residueDegree (k := k) (F := F))
      (GlobalPlace.principalDivisor (k := k) (F := F) u + G) hpositive
  rw [Divisor.degree_add, GlobalPlace.principalDivisor_degree_zero] at hdegree
  simpa using hdegree

/-- A divisor of negative constructed degree has only zero in its actual
all-place Riemann--Roch submodule. -/
theorem GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
    (G : Divisor (GlobalPlace k F))
    (hdegree : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G < 0) :
    GlobalPlace.riemannRochSubmodule G = ⊥ := by
  apply le_antisymm
  · intro f hmem
    change f = 0
    by_contra hf
    have hnonnegative :=
      GlobalPlace.divisorDegree_nonnegative_of_mem_nonzero k F G hmem hf
    exact (not_lt_of_ge hnonnegative) hdegree
  · exact bot_le

end QEC.Coding.AlgebraicGeometry

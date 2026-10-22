/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import QEC.Coding.AlgebraicGeometry.Divisors.DirectPrincipalDegree
import QEC.Coding.AlgebraicGeometry.Divisors.InverseFibrePrincipalDegree
import QEC.Coding.AlgebraicGeometry.Divisors.RationalBaseInfinityCancellation
import QEC.Coding.AlgebraicGeometry.Places.TwoChartGlobalPlace

/-!
# The principal-divisor degree formula

This layer composes the two proven chart degree computations with the
finite-support all-place divisor boundary.  It introduces neither a second
global carrier nor a new divisor construction.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]

private theorem fieldNorm_ne_zero (f : Fˣ) :
    Algebra.norm k⟮X⟯ (f : F) ≠ 0 :=
  Algebra.norm_ne_zero_iff.mpr f.ne_zero

/-- The weighted degree of the finite-support all-place principal divisor is
zero.  Its direct and inverse chart contributions are computed from actual
Dedekind factorization and the finite inverse fibre, then cancel at the
rational-base infinity place. -/
theorem GlobalPlace.principalDivisor_degree_zero (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
      (GlobalPlace.principalDivisor (k := k) (F := F) f) = 0 := by
  rw [GlobalPlace.principalDivisor_degree_eq_chartContributions,
    DirectPrincipalDegree.direct_chart_degree_eq_fieldNorm_intDegree,
    _root_.QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree.inverse_fibre_degree_eq_fieldNorm_rationalInfinity_order]
  rw [add_comm]
  exact
    RationalBaseInfinityCancellation.rationalInfinity_order_add_normalizedDegree k
      (Algebra.norm k⟮X⟯ (f : F)) (fieldNorm_ne_zero k F f)

/-- The same product formula, displayed as the finite weighted support sum
consumed by divisor calculations. -/
theorem GlobalPlace.principalOrder_weighted_sum_eq_zero (f : Fˣ) :
    (GlobalPlace.principalDivisor (k := k) (F := F) f).sum
        (fun P coefficient => coefficient *
          (GlobalPlace.residueDegree (k := k) (F := F) P : Int)) = 0 :=
  GlobalPlace.principalDivisor_degree_zero k F f

end QEC.Coding.AlgebraicGeometry

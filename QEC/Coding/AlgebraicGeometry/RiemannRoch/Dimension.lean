import QEC.Coding.AlgebraicGeometry.RiemannRoch.NegativeDegreeVanishing
import QEC.Coding.AlgebraicGeometry.RiemannRoch.FiniteDimensional

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The dimension of an all-place Riemann--Roch space

This module packages the finrank of the already-constructed all-place
Riemann--Roch submodule and proves the source-backed negative-degree case.
The imported two-chart theorem proves that this finrank is the dimension of a
finite-dimensional space in the function-field setting below.

No genus, canonical-degree identity, residue theorem, or Riemann--Roch
correction formula is assumed or proved here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace GlobalPlace

variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

/-- The dimension `ℓ(G)` of the actual finite-dimensional all-place
Riemann--Roch submodule.  Requiring finite-dimensionality prevents
`Module.finrank` from silently truncating an infinite rank to zero. -/
noncomputable def riemannRochDimension (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (riemannRochSubmodule G)] : ℕ :=
  Module.finrank k (riemannRochSubmodule G)

variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

/-- The Riemann--Roch dimension is zero for a divisor of negative degree.

This is the final clause of the source-facing Riemann--Roch statement.  It is
proved from the constructed principal-divisor product formula and the actual
valuation-bound submodule, not from a supplied Riemann--Roch theorem. -/
theorem riemannRochDimension_eq_zero_of_negative_degree
    (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (riemannRochSubmodule G)]
    (hdegree : Divisor.degree (residueDegree (k := k) (F := F)) G < 0) :
    riemannRochDimension G = 0 := by
  rw [riemannRochDimension,
    riemannRochSubmodule_eq_bot_of_negative_degree k F G hdegree]
  exact finrank_bot k F

end GlobalPlace

end QEC.Coding.AlgebraicGeometry

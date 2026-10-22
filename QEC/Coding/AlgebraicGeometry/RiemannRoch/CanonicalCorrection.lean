import QEC.Coding.AlgebraicGeometry.Differentials.CanonicalDifferential
import QEC.Coding.AlgebraicGeometry.RiemannRoch.PrincipalShift

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Representative independence of the canonical Riemann--Roch correction

Any two actual canonical divisors differ by a principal divisor.  Combining
that fact with the proved principal-shift equivalence of all-place
Riemann--Roch spaces shows that the finite-dimensional correction term
`ℓ(K - G)` is independent of the chosen canonical representative.

This module does not state the Riemann--Roch identity, define genus, prove a
canonical-degree formula, or prove a global residue theorem.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

namespace FunctionFieldDifferential

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
variable [Algebra (Polynomial k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]

/-- The finite-dimensional correction term `ℓ(K - G)` is independent of the
actual canonical divisor representative `K`. -/
theorem canonicalRiemannRochCorrectionDimension_eq
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L)
    (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (GlobalPlace.riemannRochSubmodule (K - G))]
    [FiniteDimensional k (GlobalPlace.riemannRochSubmodule (L - G))] :
    GlobalPlace.riemannRochDimension (K - G) =
      GlobalPlace.riemannRochDimension (L - G) := by
  rcases canonicalDivisors_differ_by_principal (k := k) (F := F) hK hL with
    ⟨u, hL⟩
  have hshift :
      L - G =
        GlobalPlace.principalDivisor (k := k) (F := F) u + (K - G) := by
    rw [hL]
    abel
  letI : FiniteDimensional k
      (GlobalPlace.riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + (K - G))) := by
    rw [← hshift]
    infer_instance
  have hdimension :=
    GlobalPlace.riemannRochDimension_principal_add
      (k := k) (F := F) u (K - G)
  simpa only [← hshift] using hdimension.symm

end FunctionFieldDifferential

end QEC.Coding.AlgebraicGeometry

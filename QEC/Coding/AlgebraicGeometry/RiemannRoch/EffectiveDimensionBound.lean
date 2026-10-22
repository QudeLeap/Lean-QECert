import QEC.Coding.AlgebraicGeometry.RiemannRoch.Constants
import QEC.Coding.AlgebraicGeometry.RiemannRoch.EffectiveIncrement

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The elementary upper bound for effective Riemann--Roch divisors

For a full constant field, `L(0)` has dimension one.  Combining this with the
finite effective increment bound gives `ℓ(E) ≤ deg(E) + 1` for every effective
divisor `E`.

No genus, specialty, duality, canonical-degree, or Riemann--Roch identity is
assumed here.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance riemannRochEffectiveDimensionBoundAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance riemannRochEffectiveDimensionBoundScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

local instance riemannRochEffectiveDimensionBoundFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

/-- Over the full constant field, the dimension of an effective
Riemann--Roch divisor is at most its weighted degree plus one. -/
theorem riemannRochDimension_le_degree_add_one [IsFullConstantField k F]
    (E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    riemannRochDimension E ≤
      (Divisor.degree (residueDegree (k := k) (F := F)) E).toNat + 1 := by
  have hbound := riemannRochDimension_add_nonnegative_le
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (0 : Divisor (GlobalPlace k F)) E hE
  have hzero :
      riemannRochDimension (0 : Divisor (GlobalPlace k F)) = 1 :=
    riemannRochDimension_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  simpa only [zero_add, hzero, Nat.add_comm] using hbound

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry

import QEC.Coding.AlgebraicGeometry.Adeles.AdeleDifferentialDuality

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Riemann--Roch for finite global function fields

The converse adelic duality theorem identifies the specialty index of `D`
with the actual Riemann--Roch dimension at `(omega) - D`.  Combining this
with the intrinsic definition of genus proves the full correction identity.
Evaluating the identity at zero and at a canonical divisor gives canonical
degree `2g - 2`; negative complementary degree then gives the usual
large-degree equality.

This is the source-facing Riemann--Roch theorem layer.  It uses the actual
all-place divisor and Riemann--Roch submodule constructed in this repository;
none of the displayed conclusions is supplied as an assumption.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc

noncomputable section

variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance riemannRochTheoremAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance riemannRochTheoremScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

local instance riemannRochTheoremFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

variable [IsFullConstantField k F]

namespace GlobalPlace

/-- The Riemann--Roch correction identity for the intrinsic divisor of an
actual nonzero function-field differential. -/
theorem riemannRoch_correction_term
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) :
    (riemannRochDimension G : ℤ) -
        (riemannRochDimension
          (FunctionFieldDifferential.differentialDivisor
            (k := k) (F := F) omega homega - G) : ℤ) =
      Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by
  have hduality := differentialDivisor_duality
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F omega homega G
  have hdualityInt := congrArg (fun n : ℕ => (n : ℤ)) hduality
  change
    (riemannRochDimension
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega - G) : ℤ) =
      (riemannRochIndexOfSpecialty
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G : ℤ)
    at hdualityInt
  have hindex := riemannRochIndexOfSpecialty_eq
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
  rw [hindex] at hdualityInt
  omega

/-- Riemann's lower bound on the actual all-place Riemann--Roch space. -/
theorem riemannRoch_lower_bound (G : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) ≤
      (riemannRochDimension G : ℤ) :=
  riemannRochDimension_lower_bound
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

end GlobalPlace

namespace CanonicalDivisor

/-- Every actual canonical divisor has degree `2g - 2`. -/
theorem degree_eq_two_mul_genus_sub_two
    {K : Divisor (GlobalPlace k F)}
    (hK : FunctionFieldDifferential.IsCanonicalDivisor
      (k := k) (F := F) K) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) K =
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 2 := by
  rcases hK with ⟨omega, homega, rfl⟩
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  have hzero := GlobalPlace.riemannRoch_correction_term
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F omega homega (0 : Divisor (GlobalPlace k F))
  have hself := GlobalPlace.riemannRoch_correction_term
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F omega homega K
  have hdimensionZero : GlobalPlace.riemannRochDimension
      (0 : Divisor (GlobalPlace k F)) = 1 :=
    GlobalPlace.riemannRochDimension_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  simp only [K, sub_zero, sub_self, Divisor.degree_zero,
    hdimensionZero, Nat.cast_one] at hzero hself
  omega

end CanonicalDivisor

namespace GlobalPlace

/-- When `deg(G) ≥ 2g - 1`, the complementary canonical space has negative
degree and the Riemann--Roch dimension is exactly `deg(G) + 1 - g`. -/
theorem riemannRoch_eq_of_large_degree
    (G : Divisor (GlobalPlace k F))
    (hdegree :
      2 * (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree (residueDegree (k := k) (F := F)) G) :
    (riemannRochDimension G : ℤ) =
      Divisor.degree (residueDegree (k := k) (F := F)) G + 1 -
        (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
          (φ := φ) (s := s) k F : ℤ) := by
  let omega := FunctionFieldDifferential.functionFieldDifferentialGenerator
    (k := k) (F := F)
  have homega : omega ≠ 0 :=
    FunctionFieldDifferential.functionFieldDifferentialGenerator_ne_zero
      (k := k) (F := F)
  let K := FunctionFieldDifferential.differentialDivisor
    (k := k) (F := F) omega homega
  have hKcanonical : FunctionFieldDifferential.IsCanonicalDivisor
      (k := k) (F := F) K := by
    exact FunctionFieldDifferential.differentialDivisor_isCanonical
      (k := k) (F := F) omega homega
  have hKdegree := CanonicalDivisor.degree_eq_two_mul_genus_sub_two
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hKcanonical
  have hcomplementDegree :
      Divisor.degree (residueDegree (k := k) (F := F)) (K - G) < 0 := by
    rw [Divisor.degree_sub, hKdegree]
    omega
  have hcomplementZero : riemannRochDimension (K - G) = 0 :=
    riemannRochDimension_eq_zero_of_negative_degree
      (k := k) (F := F) (K - G) hcomplementDegree
  have hcorrection := riemannRoch_correction_term
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s)
    k F omega homega G
  rw [hcomplementZero] at hcorrection
  omega

/-- A divisor of negative degree has the zero all-place Riemann--Roch
submodule. -/
theorem riemannRoch_eq_bot_of_negative_degree
    (G : Divisor (GlobalPlace k F))
    (hdegree : Divisor.degree (residueDegree (k := k) (F := F)) G < 0) :
    riemannRochSubmodule G = ⊥ :=
  riemannRochSubmodule_eq_bot_of_negative_degree k F G hdegree

end GlobalPlace

end


end QEC.Coding.AlgebraicGeometry

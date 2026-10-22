import QEC.Coding.AlgebraicGeometry.RiemannRoch.PlaceIncrementDimension

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Dimension growth under finite effective divisor increments

The one-place residue-degree bound on Riemann--Roch dimension growth extends
over the finite support of an effective divisor.  This file proves that
finite effective increment bound and its comparable-divisor form.

No specialty, duality, genus, canonical-degree, or Riemann--Roch identity is
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

noncomputable local instance riemannRochEffectiveIncrementAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π

local instance riemannRochEffectiveIncrementScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F

namespace GlobalPlace

local instance finiteDimensionalRiemannRochSubmodule
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G

private theorem riemannRochDimension_add_placeDivisor_le'
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    riemannRochDimension (G + placeDivisor P) ≤
      riemannRochDimension G + residueDegree (k := k) (F := F) P := by
  exact riemannRochDimension_add_placeDivisor_le G P

private theorem riemannRochDimension_add_single_nat_le
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) (n : ℕ) :
    riemannRochDimension (D + Finsupp.single P (n : ℤ)) ≤
      riemannRochDimension D +
        n * residueDegree (k := k) (F := F) P := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      let M := D + Finsupp.single P (n : ℤ)
      have heq : D + Finsupp.single P ((n + 1 : ℕ) : ℤ) =
          M + placeDivisor P := by
        dsimp only [M]
        ext Q
        simp only [Finsupp.add_apply, Finsupp.single_apply, placeDivisor]
        split <;> omega
      calc
        riemannRochDimension
            (D + Finsupp.single P ((n + 1 : ℕ) : ℤ)) =
            riemannRochDimension (M + placeDivisor P) := by rw [heq]
        _ ≤ riemannRochDimension M +
            residueDegree (k := k) (F := F) P :=
          riemannRochDimension_add_placeDivisor_le'
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F M P
        _ ≤ (riemannRochDimension D +
              n * residueDegree (k := k) (F := F) P) +
            residueDegree (k := k) (F := F) P :=
          Nat.add_le_add_right ih _
        _ = riemannRochDimension D +
            (n + 1) * residueDegree (k := k) (F := F) P := by
          rw [Nat.add_mul, one_mul, add_assoc]

/-- Enlarging a divisor by an effective finite divisor raises its actual
Riemann--Roch dimension by at most the weighted degree of that increment. -/
theorem riemannRochDimension_add_nonnegative_le
    (D E : Divisor (GlobalPlace k F)) (hE : Divisor.Nonnegative E) :
    riemannRochDimension (D + E) ≤
      riemannRochDimension D +
        (Divisor.degree (residueDegree (k := k) (F := F)) E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      simp
  | single_add P coefficient tail hPtail hcoefficient ih =>
      have htailP : tail P = 0 := Finsupp.notMem_support_iff.mp hPtail
      have htail : Divisor.Nonnegative tail := by
        intro Q
        by_cases hQP : Q = P
        · subst Q
          rw [htailP]
        · simpa [Finsupp.single_apply, hQP] using hE Q
      have hcoefficient_nonnegative : 0 ≤ coefficient := by
        simpa [Finsupp.single_apply, htailP] using hE P
      let M := D + tail
      let N := M + Finsupp.single P (coefficient.toNat : ℤ)
      have hfirst := ih D htail
      have hsecond : riemannRochDimension N ≤
          riemannRochDimension M +
            coefficient.toNat * residueDegree (k := k) (F := F) P := by
        exact riemannRochDimension_add_single_nat_le
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F M P coefficient.toNat
      have hdegree_tail : 0 ≤
          Divisor.degree (residueDegree (k := k) (F := F)) tail :=
        Divisor.degree_nonnegative _ tail htail
      have hdegree_total : 0 ≤
          Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail) :=
        Divisor.degree_nonnegative _ _ hE
      have hdegree :
          Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail) =
            coefficient * (residueDegree (k := k) (F := F) P : ℤ) +
              Divisor.degree (residueDegree (k := k) (F := F)) tail := by
        rw [Divisor.degree_add]
        simp [Divisor.degree, Divisor.degreeHom]
      have hdegree_nat :
          (Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat =
            coefficient.toNat * residueDegree (k := k) (F := F) P +
              (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat := by
        have htail_cast :
            ((Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat : ℤ) =
              Divisor.degree (residueDegree (k := k) (F := F)) tail :=
          Int.toNat_of_nonneg hdegree_tail
        have htotal_cast :
            ((Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat : ℤ) =
                Divisor.degree (residueDegree (k := k) (F := F))
                  (Finsupp.single P coefficient + tail) :=
          Int.toNat_of_nonneg hdegree_total
        apply Int.ofNat_injective
        change ((Divisor.degree (residueDegree (k := k) (F := F))
            (Finsupp.single P coefficient + tail)).toNat : ℤ) =
          ((coefficient.toNat * residueDegree (k := k) (F := F) P +
            (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat : ℕ) : ℤ)
        rw [htotal_cast, Nat.cast_add, Nat.cast_mul,
          Int.toNat_of_nonneg hcoefficient_nonnegative, htail_cast]
        exact hdegree
      have htotal : riemannRochDimension N ≤
          riemannRochDimension D +
            (Divisor.degree (residueDegree (k := k) (F := F))
              (Finsupp.single P coefficient + tail)).toNat := by
        calc
          riemannRochDimension N ≤
              riemannRochDimension M +
                coefficient.toNat * residueDegree (k := k) (F := F) P := hsecond
          _ ≤ (riemannRochDimension D +
                (Divisor.degree (residueDegree (k := k) (F := F)) tail).toNat) +
              coefficient.toNat * residueDegree (k := k) (F := F) P :=
            Nat.add_le_add_right hfirst _
          _ = riemannRochDimension D +
              (Divisor.degree (residueDegree (k := k) (F := F))
                (Finsupp.single P coefficient + tail)).toNat := by
            rw [hdegree_nat]
            ac_rfl
      have heq : D + (Finsupp.single P coefficient + tail) = N := by
        dsimp only [N, M]
        rw [Int.toNat_of_nonneg hcoefficient_nonnegative]
        abel
      rw [heq]
      exact htotal

/-- For comparable divisors, the dimension growth is bounded by the weighted
degree of their effective difference. -/
theorem riemannRochDimension_le_add_degree_of_le
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    riemannRochDimension E ≤
      riemannRochDimension D +
        (Divisor.degree (residueDegree (k := k) (F := F)) (E - D)).toNat := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hbound := riemannRochDimension_add_nonnegative_le
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D (E - D) hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [heq] at hbound
  exact hbound

end GlobalPlace

end

end QEC.Coding.AlgebraicGeometry

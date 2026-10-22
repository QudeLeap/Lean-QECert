import QEC.Coding.AlgebraicGeometry.RiemannRoch.AffineCountBridge
import QEC.Coding.AlgebraicGeometry.Places.InverseAffinePlace
import QEC.Coding.AlgebraicGeometry.RiemannRoch.Space

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Chart containment for the all-place Riemann--Roch submodule

The declarations here restrict an already-existing all-place divisor to the
two actual affine charts and prove the resulting lattice containments.  They
do not expose the private corrected two-chart carrier and do not construct a
second all-place divisor.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc WithZero

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
variable [τ : IsScalarTower k[X] k⟮X⟯ F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable k⟮X⟯ F]

private theorem affineGlobalPlace_injective :
    Function.Injective (AffinePlace.globalPlace k F) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  intro P Q h
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
  exact Valuation.IsEquiv.of_eq (congrArg (fun V : GlobalPlace k F => V.valuation) h)

/-- Restrict an existing global divisor to the direct affine chart. -/
noncomputable def GlobalPlace.directChartDivisor
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    Divisor (AffinePlace.carrier k F) :=
  Finsupp.comapDomain (AffinePlace.globalPlace k F) G
    (affineGlobalPlace_injective k F).injOn

/-- The direct-chart restriction preserves the coefficient at the associated
global place. -/
theorem GlobalPlace.directChartDivisor_apply
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π)))
    (P : AffinePlace.carrier k F) :
    GlobalPlace.directChartDivisor k F G P = G (AffinePlace.globalPlace k F P) := by
  simp [GlobalPlace.directChartDivisor]

/-- A Riemann--Roch member is contained in the fractional lattice obtained by
restricting its all-place divisor to the direct affine chart. -/
theorem GlobalPlace.riemannRoch_mem_directChartFractionalLattice :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ (G : Divisor (GlobalPlace k F)) (x : GlobalPlace.riemannRochSubmodule G),
      (x : F) ∈ AffinePlace.chartFractionalLattice k F
        (GlobalPlace.directChartDivisor k F G) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  intro G x
  rw [AffinePlace.mem_chartFractionalLattice_iff]
  intro P
  have hx := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp x.property
  calc
    AffinePlace.valuation k F P (x : F) =
        (AffinePlace.globalPlace k F P).valuation (x : F) := rfl
    _ ≤ WithZero.exp (G (AffinePlace.globalPlace k F P)) :=
      hx (AffinePlace.globalPlace k F P)
    _ = WithZero.exp (GlobalPlace.directChartDivisor k F G P) := by
      rw [GlobalPlace.directChartDivisor_apply]

/-- Package an actual inverse-chart affine prime as a global place with the
same normalized valuation.  The target uses the direct chart's explicit
constant algebra, so it can be evaluated against the existing all-place
divisor. -/
noncomputable def InverseAffinePlace.asGlobalPlace
    (P : InverseAffinePlace.carrier k F) :
    let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    @GlobalPlace k F _ _ _ directConstantAlgebra := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  exact ⟨P.valuation F, P.valuation_surjective F⟩

private theorem inverseAffineAsGlobalPlace_injective :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    Function.Injective (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ)
      (φ := φ) (s := s) k F) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  intro P Q h
  apply IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
  exact Valuation.IsEquiv.of_eq (congrArg (fun V : GlobalPlace k F => V.valuation) h)

/-- Restrict an existing all-place divisor to all inverse-chart affine primes.
The target is elaborated in the transported chart; no global carrier is
redefined. -/
noncomputable def GlobalPlace.inverseChartDivisor
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    Divisor (AffinePlace.carrier k F) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  exact Finsupp.comapDomain (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ)
    (φ := φ) (s := s) k F) G
    (inverseAffineAsGlobalPlace_injective (π := π) (ρ := ρ) (φ := φ) (s := s) k F).injOn

/-- The inverse-chart restriction preserves the coefficient at the packaged
global valuation of that inverse-chart prime. -/
theorem GlobalPlace.inverseChartDivisor_apply
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    ∀ P : AffinePlace.carrier k F,
      GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G P =
        G (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ) (φ := φ) (s := s) k F P) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  intro P
  simp [GlobalPlace.inverseChartDivisor]

/-- A Riemann--Roch member is contained in the fractional lattice obtained by
restricting the same all-place divisor to the transported inverse chart. -/
theorem GlobalPlace.riemannRoch_mem_inverseChartFractionalLattice :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ (G : Divisor (GlobalPlace k F)) (x : GlobalPlace.riemannRochSubmodule G),
      letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
      letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
      letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
        (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
      (x : F) ∈ AffinePlace.chartFractionalLattice k F
        (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  intro G x
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  rw [AffinePlace.mem_chartFractionalLattice_iff]
  intro P
  have hx := (GlobalPlace.mem_riemannRochSubmodule_iff G (x : F)).mp x.property
  calc
    AffinePlace.valuation k F P (x : F) =
        (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ) (φ := φ) (s := s) k F P).valuation
          (x : F) := rfl
    _ ≤ WithZero.exp (G (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ)
        (φ := φ) (s := s) k F P)) :=
      hx (InverseAffinePlace.asGlobalPlace (π := π) (ρ := ρ) (φ := φ) (s := s) k F P)
    _ = WithZero.exp (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ)
        (φ := φ) (s := s) k F G P) := by
      rw [GlobalPlace.inverseChartDivisor_apply (π := π) (ρ := ρ) (φ := φ) (s := s)]

end QEC.Coding.AlgebraicGeometry

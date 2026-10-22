import QEC.Coding.AlgebraicGeometry.RiemannRoch.ChartContainment
import QEC.Coding.AlgebraicGeometry.RiemannRoch.TwoChartFiniteDimensionalBridge
import QEC.Coding.AlgebraicGeometry.Places.AffinePlaceDegree

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Finite-dimensionality of the all-place Riemann--Roch submodule

The proof uses the two concrete chart-lattice containments and the existing
two-chart denominator bridge.  No finite-dimensionality hypothesis, duality
statement, or Riemann--Roch dimension formula is accepted as an input.
-/

namespace QEC.Coding.AlgebraicGeometry

open scoped Polynomial RatFunc nonZeroDivisors

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

/-- The direct chart's constant map agrees with restriction of the direct
rational-function coefficient map. -/
private theorem directConstantAlgebra_map_eq_rationalRestriction
    : letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    algebraMap k F = (algebraMap (RatFunc k) F).comp (algebraMap k (RatFunc k)) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  ext c
  change algebraMap (Polynomial k) F (Polynomial.C c) =
    algebraMap (RatFunc k) F
      (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c))
  exact IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F (Polynomial.C c)

/-- The direct Laurent-coordinate scalar tower is induced by the same
constant algebra used by the all-place Riemann--Roch submodule. -/
@[reducible] noncomputable def directConstantScalarTower :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    IsScalarTower k (RatFunc k) F := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  exact IsScalarTower.of_algebraMap_eq fun c => by
    simpa only [RingHom.comp_apply] using
      DFunLike.congr_fun
        (directConstantAlgebra_map_eq_rationalRestriction (π := π) (ρ := ρ)
          (τ := τ) (φ := φ) (s := s) k F) c

/-- The direct chart lattice, viewed as a genuine `k[X]` submodule. -/
noncomputable def GlobalPlace.directChartModule
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    Submodule (Polynomial k) F :=
  (AffinePlace.chartFractionalLattice k F
    (GlobalPlace.directChartDivisor (π := π) k F G)).coeToSubmodule.restrictScalars (Polynomial k)

private theorem directChartModule_finite
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    Module.Finite (Polynomial k) (GlobalPlace.directChartModule (π := π) k F G) := by
  letI : Module.Finite (Polynomial k) (AffinePlace.affineRing k F) :=
    AffinePlace.finite_ringOfIntegers k F
  rw [Module.Finite.iff_fg]
  change ((AffinePlace.chartFractionalLattice k F
    (GlobalPlace.directChartDivisor (π := π) k F G)).coeToSubmodule.restrictScalars
      (Polynomial k)).FG
  exact (FractionalIdeal.fg_of_isNoetherianRing
    (S := (AffinePlace.affineRing k F)⁰) le_rfl
    (AffinePlace.chartFractionalLattice k F
      (GlobalPlace.directChartDivisor (π := π) k F G))).restrictScalars

private theorem inverseChartModule_finite
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    letI : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    Module.Finite (Polynomial k)
      (((AffinePlace.chartFractionalLattice k F
        (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G)).coeToSubmodule).restrictScalars
          (Polynomial k)) := by
  let directConstantAlgebra : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : Algebra k F := directConstantAlgebra
  letI : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
    (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    InverseAffinePlace.transportedScalarTower
      (k := k) (F := F) (oldRationalAlgebra := ρ)
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
  letI : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
    (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
  letI : Module.Finite (Polynomial k) (AffinePlace.affineRing k F) :=
    AffinePlace.finite_ringOfIntegers k F
  rw [Module.Finite.iff_fg]
  change (((AffinePlace.chartFractionalLattice k F
    (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G)).coeToSubmodule).restrictScalars
      (Polynomial k)).FG
  exact (FractionalIdeal.fg_of_isNoetherianRing
    (S := (AffinePlace.affineRing k F)⁰) le_rfl
    (AffinePlace.chartFractionalLattice k F
      (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G))).restrictScalars

/-- The actual all-place valuation-bound Riemann--Roch submodule is finite
dimensional over the finite constant field.  The direct and inverse lattice
containments are constructed from `G`; no global dimension result is an input.
-/
theorem GlobalPlace.finiteDimensional_riemannRochSubmodule
    : letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ G : Divisor (GlobalPlace k F),
      FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  letI : IsScalarTower k (RatFunc k) F :=
    directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  intro G
  let b : Module.Basis (Fin (Module.finrank (RatFunc k) F)) (RatFunc k) F :=
    Module.finBasis (RatFunc k) F
  let Λdirect := GlobalPlace.directChartModule (π := π) k F G
  letI : Module.Finite (Polynomial k) Λdirect :=
    directChartModule_finite (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
  refine TwoChartFiniteDimensionalBridge.finiteDimensional_of_twoChart_denominator_certificates
      (ρ := ρ) (π := π) (τ := τ) (φ := φ) (s := s)
      (b := b) (L := GlobalPlace.riemannRochSubmodule G) Λdirect ?_ ?_
  · intro x
    exact GlobalPlace.riemannRoch_mem_directChartFractionalLattice
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G x
  · letI : Algebra (RatFunc k) F := InverseAffinePlace.transportedRationalAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : Algebra (Polynomial k) F := InverseAffinePlace.transportedPolynomialAlgebra
      (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
      InverseAffinePlace.transportedScalarTower
        (k := k) (F := F) (oldRationalAlgebra := ρ)
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldFunctionField := φ)
    letI : Algebra.IsSeparable (RatFunc k) F := InverseAffinePlace.transportedIsSeparable
      (k := k) (F := F) (oldRationalAlgebra := ρ) (oldSeparable := s)
    let Λinverse := ((AffinePlace.chartFractionalLattice k F
      (GlobalPlace.inverseChartDivisor (π := π) (ρ := ρ) (φ := φ) (s := s) k F G)).coeToSubmodule).restrictScalars
        (Polynomial k)
    refine ⟨Λinverse, inverseChartModule_finite (π := π) (ρ := ρ)
      (τ := τ) (φ := φ) (s := s) k F G, ?_⟩
    intro x
    exact GlobalPlace.riemannRoch_mem_inverseChartFractionalLattice
      (π := π) (ρ := ρ) (φ := φ) (s := s) k F G x

end QEC.Coding.AlgebraicGeometry

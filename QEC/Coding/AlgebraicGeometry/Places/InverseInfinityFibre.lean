/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import QEC.Coding.AlgebraicGeometry.Places.AffineGlobalPlace
import QEC.Coding.AlgebraicGeometry.Places.InverseAffinePlace

/-!
# The raw inverse-chart fibre above `(X)`

This module isolates the finite, nonempty family of height-one primes of the
inverse-chart integral closure which lie over the polynomial ideal `(X)`.
The coefficient algebra on the integral closure is explicitly the transported
inverse-chart algebra from `InverseAffinePlace`; it is not the original affine
chart's algebra by accident.

The result is intentionally only a raw fibre.  It does not state that this
fibre is disjoint from the first chart, covers every global place, supplies a
product formula, or has rational residue degree.  Those statements require
additional comparison and global-duality work.

-/

namespace QEC.Coding.AlgebraicGeometry

namespace InverseAffinePlace

open scoped Polynomial RatFunc

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

local notation3 "inverseRationalAlgebra" =>
  transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inversePolynomialAlgebra" =>
  transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseScalarTower" =>
  transportedScalarTower (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseFunctionField" =>
  transportedFunctionField (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
local notation3 "inverseIsSeparable" =>
  transportedIsSeparable (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
local notation3 "inverseCarrier" =>
  carrier (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)

/-- The actual height-one polynomial prime `(X)` used as the base of the
inverse-chart fibre. -/
noncomputable abbrev infinityBasePrime : Ideal k[X] :=
  (Polynomial.idealX k).asIdeal

/-- The polynomial prime `(X)` is nonzero, so its inverse-chart lift is a
nonzero ideal of the corresponding integral closure. -/
theorem infinityBasePrime_ne_zero : infinityBasePrime k ≠ 0 := by
  rw [Ideal.zero_eq_bot]
  exact (Polynomial.idealX k).ne_bot

/-- Height-one primes in the concrete inverse-chart carrier that divide the
lift of `(X)`.  The displayed `algebraMap` is the one induced by
`transportedPolynomialAlgebra`; all surrounding local instances are listed so
the ideal map cannot silently use the old affine-coordinate algebra. -/
noncomputable abbrev infinityFibre : Type _ :=
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  {v : IsDedekindDomain.HeightOneSpectrum
      (_root_.FunctionField.ringOfIntegers k F) //
    v.asIdeal ∣ Ideal.map
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (infinityBasePrime k)}

/-- The raw height-one-prime fibre is exactly the set of prime ideals of the
inverse-chart integral closure lying over `(X)`.  This is Mathlib's
`equivPrimesOver` bridge; it records both the height-one and the lying-over
conditions without choosing a prime. -/
noncomputable def infinityFibreEquivPrimesOver :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra) ≃
      (infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Module.IsTorsionFree k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isTorsionFree k[X] F
  letI : Algebra.IsIntegral k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  exact IsDedekindDomain.HeightOneSpectrum.equivPrimesOver
    (_root_.FunctionField.ringOfIntegers k F) (infinityBasePrime_ne_zero k)

/-- Finiteness of the inverse-chart fibre is derived from the finite
`primesOver` API, rather than recorded as a field of a place structure. -/
noncomputable instance infinityFibreFintype :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Fintype (infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Module.IsTorsionFree k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isTorsionFree k[X] F
  letI : Algebra.IsIntegral k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  letI : Fintype
      ((infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F)) :=
    (IsDedekindDomain.primesOver_finite (infinityBasePrime k)
      (_root_.FunctionField.ringOfIntegers k F)).fintype
  exact Fintype.ofEquiv
    ((infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F))
    (infinityFibreEquivPrimesOver (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)).symm

/-- Lying-over supplies an actual inverse-chart prime above `(X)`, so the raw
fibre is nonempty without storing a selected infinity place. -/
theorem infinityFibre_nonempty :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Nonempty (infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Module.IsTorsionFree k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isTorsionFree k[X] F
  letI : Algebra.IsIntegral k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  rcases (inferInstance : Nonempty
    ((infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F))) with ⟨P⟩
  exact ⟨(infinityFibreEquivPrimesOver (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)).symm P⟩

omit [Finite k] in
/-- Each raw fibre point carries the explicit divisibility condition defining
its lying-over relation for the transported inverse-chart coefficient map. -/
theorem infinityFibre_dvd (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    v.1.asIdeal ∣ Ideal.map
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (infinityBasePrime k) := by
  exact v.2

omit [Finite k] in
/-- The transported inverse-chart coordinate, as an element of its integral
closure, belongs to every prime in the raw fibre.  This is the local zero
condition above `(X)`; it does not identify the resulting global place with
any place from the original affine chart. -/
theorem coordinate_mem_definingPrime (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X ∈ v.1.asIdeal := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  apply Ideal.dvd_iff_le.mp v.2
  apply Ideal.mem_map_of_mem
  change Polynomial.X ∈ (Polynomial.idealX k).asIdeal
  rw [Polynomial.idealX_span]
  exact Ideal.subset_span (Set.mem_singleton Polynomial.X)

/-- The existing affine-to-global construction applied to the actual
inverse-chart carrier point.  Its constant algebra is the affine bridge's
explicit composite for the transported polynomial algebra. -/
noncomputable def globalPlace (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  exact @AffinePlace.globalPlace k F _ _ _ inversePolynomialAlgebra inverseRationalAlgebra
    inverseScalarTower inverseFunctionField inverseIsSeparable v.1

/-- The global place constructed from an inverse-chart fibre point retains
exactly that point's normalized affine adic valuation. -/
theorem globalPlace_valuation (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    (globalPlace (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) v).valuation =
      AffinePlace.valuation k F v.1 := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  exact @AffinePlace.globalPlace_valuation k F _ _ _ inversePolynomialAlgebra
    inverseRationalAlgebra inverseScalarTower inverseFunctionField inverseIsSeparable v.1

/-- The inverse-chart fibre's global valuation is surjective onto the
normalized integer value group, inherited from the existing height-one-prime
adic valuation rather than assumed for a new place structure. -/
theorem globalPlace_surjective (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    Function.Surjective
      (globalPlace (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)
        (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) v).valuation := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  exact @AffinePlace.globalPlace_surjective k F _ _ _ inversePolynomialAlgebra
    inverseRationalAlgebra inverseScalarTower inverseFunctionField inverseIsSeparable v.1

/-- The transported chart coordinate has valuation strictly below one at each
fibre point.  This is the exact adic form of its local zero condition; no
global place classification or comparison with the original coordinate is
asserted. -/
theorem globalPlace_coordinate_valuation_lt_one
    (v : infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    (globalPlace (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) v).valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) < 1 := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  rw [@globalPlace_valuation k F _ _ _ oldPolynomialAlgebra oldRationalAlgebra oldScalarTower
    oldFunctionField oldSeparable v,
    @AffinePlace.valuation_algebraMap_of_integral k F _ _ _ inversePolynomialAlgebra inverseRationalAlgebra
      inverseScalarTower inverseFunctionField inverseIsSeparable]
  exact (v.1.intValuation_lt_one_iff_mem
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)).mpr
      (@coordinate_mem_definingPrime k F _ _ oldPolynomialAlgebra oldRationalAlgebra
        oldScalarTower oldFunctionField oldSeparable v)

end InverseAffinePlace

end QEC.Coding.AlgebraicGeometry

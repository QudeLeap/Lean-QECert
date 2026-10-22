import QEC.Coding.AlgebraicGeometry.Residues.Direct.IntegralDifferentialResidue
import QEC.Coding.AlgebraicGeometry.Places.InverseInfinityFibre

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# The inverse fibre as the direct factor family over `(X)`

For the transported inverse chart, the existing finite fibre above `(X)` and
the factor subtype used by the direct trace--residue theorem are the same
actual height-one primes.  This module records the explicit equivalence and
its compatibility with the affine and global place constructors.

No differential trace, residue sum, duality statement, genus formula, or
Riemann--Roch theorem is asserted here.
-/

namespace QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor

open scoped Polynomial RatFunc

open UniqueFactorizationMonoid

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]

local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inversePolynomialAlgebra" =>
  InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseScalarTower" =>
  InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F

/-- The raw inverse fibre and the direct factor subtype over `(X)` are the
same finite family of actual prime ideals. -/
noncomputable def infinityFibreEquivDirectFactors :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    InverseAffinePlace.infinityFibre
        (oldRationalAlgebra := oldRationalAlgebra) k F ≃
      (factors (Ideal.map
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
        (Polynomial.idealX k).asIdeal)).toFinset := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
  let e := InverseAffinePlace.infinityFibreEquivPrimesOver
    (oldRationalAlgebra := oldRationalAlgebra) k F
  let hs :
      (↑(IsDedekindDomain.primesOverFinset
        (InverseAffinePlace.infinityBasePrime k) B) : Set (Ideal B)) =
        (InverseAffinePlace.infinityBasePrime k).primesOver B :=
    IsDedekindDomain.coe_primesOverFinset
      (InverseAffinePlace.infinityBasePrime_ne_zero k) B
  exact e.trans (Equiv.setCongr hs.symm)

omit oldPolynomialAlgebra oldScalarTower in
@[simp]
theorem infinityFibreEquivDirectFactors_apply_asIdeal
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    ((infinityFibreEquivDirectFactors
      (oldRationalAlgebra := oldRationalAlgebra) k F D :
        (factors (Ideal.map
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
          (Polynomial.idealX k).asIdeal)).toFinset) :
      Ideal (_root_.FunctionField.ringOfIntegers k F)) = D.1.asIdeal := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
  change
    ((InverseAffinePlace.infinityFibreEquivPrimesOver
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable) k F D :
        (InverseAffinePlace.infinityBasePrime k).primesOver B) : Ideal B) =
      D.1.asIdeal
  rfl

omit oldPolynomialAlgebra oldScalarTower in
/-- Reinterpreting an inverse-fibre point through the direct factor subtype
recovers the original height-one prime. -/
theorem directFactorPlace_infinityFibreEquiv
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    DirectIntegralDifferentialResidue.directFactorPlace k F
        (Polynomial.idealX k)
        (infinityFibreEquivDirectFactors
          (oldRationalAlgebra := oldRationalAlgebra) k F D) = D.1 := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact infinityFibreEquivDirectFactors_apply_asIdeal
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable) k F D

omit oldPolynomialAlgebra oldScalarTower in
/-- The direct global-place constructor at the corresponding factor is the
raw inverse-fibre global place itself. -/
theorem directFactorGlobalPlace_infinityFibreEquiv
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    AffinePlace.globalPlace k F
        (DirectIntegralDifferentialResidue.directFactorPlace k F
          (Polynomial.idealX k)
          (infinityFibreEquivDirectFactors
            (oldRationalAlgebra := oldRationalAlgebra) k F D)) =
      InverseAffinePlace.globalPlace
        (oldRationalAlgebra := oldRationalAlgebra) k F D := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  rw [directFactorPlace_infinityFibreEquiv
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField)
    (oldSeparable := oldSeparable)]
  rfl

end QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor

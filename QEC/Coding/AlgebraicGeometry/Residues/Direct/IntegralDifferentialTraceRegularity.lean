import QEC.Coding.AlgebraicGeometry.Residues.Direct.SmithDifferentialTrace
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicPolynomialDifferential

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Regularity of traces of direct integral differentials

For two elements of the direct integral closure, the differential trace of
`b dt` is a polynomial multiple of `dX`.  The proof differentiates the actual
integral multiplication matrix of `t`; the connection terms cancel under the
weighted matrix trace.  Consequently this traced differential is regular at
every finite normalized rational place.

This is the regular-integral part of the local trace--residue comparison.  It
does not clear a semilocal differential denominator, sum over upper places,
or prove a global residue theorem, duality, genus, or Riemann--Roch.
-/

open scoped Polynomial RatFunc nonZeroDivisors

namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity

open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential

variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]

noncomputable local instance : Algebra k F := AffinePlace.constantAlgebra k F

noncomputable local instance : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))

abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

local instance : Module.Finite (R k) (B k F) :=
  AffinePlace.finite_ringOfIntegers k F

local instance : IsLocalization
    (Algebra.algebraMapSubmonoid (B k F) (R k)⁰) F :=
  IsIntegralClosure.isLocalization_of_isSeparable
    (R k) (RatFunc k) F (B k F)

omit [Finite k] in
private theorem functionFieldDerivation_extends_rationalDerivation
    (c : RatFunc k) :
    functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F c) =
      algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1 c) := by
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  rw [functionFieldDerivation,
    SeparableDerivationExtension.separableDerivationExtension_apply_algebraMap]
  let Dmap : Derivation k (RatFunc k) F :=
    (Algebra.ofId (RatFunc k) F).toLinearMap.compDer D₀
  have hmap :
      RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 = Dmap := by
    have hX : Dmap RatFunc.X = (1 : F) := by
      change algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1 RatFunc.X) = 1
      rw [RatFuncDerivation.rationalDerivation_apply_X, map_one]
    rw [← hX]
    exact RatFuncDerivation.rationalDerivation_eq_of_apply_X (k := k)
  have hc := Derivation.congr_fun hmap c
  change RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 c =
    algebraMap (RatFunc k) F (D₀ c) at hc
  exact hc

omit [Finite k] in
private theorem derivation_weighted_trace_eq_matrix_trace
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι K L)
    (r t : L) :
    Algebra.trace K L (r * D t) =
      Matrix.trace
        (LinearMap.toMatrix basis basis (Algebra.lmul K L r) *
          entrywiseMatrixDerivation D₀
            (LinearMap.toMatrix basis basis (Algebra.lmul K L t))) := by
  classical
  by_cases ht : t = 0
  · subst t
    have hzeroDerivative :
        entrywiseMatrixDerivation D₀ (0 : Matrix ι ι K) = 0 := by
      ext i j
      simp [entrywiseMatrixDerivation_apply]
    simp only [map_zero, mul_zero, hzeroDerivative, Matrix.trace_zero]
  · have hlog :=
      FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
        D₀ D hD basis (r * t) t ht
    have hleft : (r * t) * D t * t⁻¹ = r * D t := by
      field_simp [ht]
    have hmatrix :
        LinearMap.toMatrix basis basis (Algebra.lmul K L (r * t)) *
            LinearMap.toMatrix basis basis (Algebra.lmul K L t⁻¹) =
          LinearMap.toMatrix basis basis (Algebra.lmul K L r) := by
      rw [← LinearMap.toMatrix_mul, ← map_mul]
      congr 1
      field_simp [ht]
    rw [hleft] at hlog
    simpa only [hmatrix] using hlog

/-- The polynomial coefficient obtained by differentiating the integral
multiplication matrix of `t` and weighting it by multiplication by `b`. -/
noncomputable def directIntegralDifferentialTracePolynomial
    (b t : B k F) : R k := by
  let basis := Module.finBasis (R k) (B k F)
  exact Matrix.trace
    (LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) b) *
      entrywisePolynomialDerivative
        (LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) t)))

/-- The differential trace of `b dt` for direct integral `b,t` is the image
of an actual polynomial times the rational differential generator. -/
theorem
    functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
    (b t : B k F) :
    functionFieldDifferentialTrace (k := k) (F := F)
        ((algebraMap (B k F) F b) •
          differential k F (algebraMap (B k F) F t)) =
      algebraMap (R k) (RatFunc k)
          (directIntegralDifferentialTracePolynomial k F b t) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  classical
  let basis := Module.finBasis (R k) (B k F)
  let basisF := basis.localizationLocalization
    (RatFunc k) (R k)⁰ F
  let m := algebraMap (R k) (RatFunc k)
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  let D := functionFieldDerivation (k := k) (F := F)
  let Bmat : Matrix _ _ (R k) :=
    LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) b)
  let Tmat : Matrix _ _ (R k) :=
    LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) t)
  let BF : Matrix _ _ (RatFunc k) := m.mapMatrix Bmat
  let TF : Matrix _ _ (RatFunc k) := m.mapMatrix Tmat
  have hBF :
      LinearMap.toMatrix basisF basisF
          (Algebra.lmul (RatFunc k) F (algebraMap (B k F) F b)) = BF := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) (R k) (R k)⁰ basis b
  have hTF :
      LinearMap.toMatrix basisF basisF
          (Algebra.lmul (RatFunc k) F (algebraMap (B k F) F t)) = TF := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) (R k) (R k)⁰ basis t
  have htrace := derivation_weighted_trace_eq_matrix_trace (k := k)
    D₀ D (functionFieldDerivation_extends_rationalDerivation (k := k) (F := F))
    basisF (algebraMap (B k F) F b) (algebraMap (B k F) F t)
  have hentrywise :
      entrywiseMatrixDerivation D₀ TF =
        m.mapMatrix (entrywisePolynomialDerivative Tmat) := by
    change entrywiseMatrixDerivation
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1)
        (m.mapMatrix Tmat) = _
    exact entrywiseMatrixDerivation_map_polynomial Tmat
  have hmatrix :
      Matrix.trace (BF * entrywiseMatrixDerivation D₀ TF) =
        m (Matrix.trace (Bmat * entrywisePolynomialDerivative Tmat)) := by
    rw [hentrywise]
    rw [← m.mapMatrix.map_mul]
    exact (AddMonoidHom.map_trace m.toAddMonoidHom
      (Bmat * entrywisePolynomialDerivative Tmat)).symm
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F)
          ((algebraMap (B k F) F b) •
            differential k F (algebraMap (B k F) F t)) =
        algebraMap (B k F) F b * D (algebraMap (B k F) F t) := by
    rw [map_smul,
      functionFieldDifferentialCoordinate_differential]
    simp only [smul_eq_mul, D]
  rw [functionFieldDifferentialTrace_apply, hcoordinate, htrace, hBF, hTF,
    hmatrix]
  rfl

/-- Tracing `b dt` for direct integral `b,t` gives a differential regular at
every finite normalized rational place. -/
theorem
    functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (b t : B k F) :
    functionFieldDifferentialTrace (k := k) (F := F)
        ((algebraMap (B k F) F b) •
          differential k F (algebraMap (B k F) F t)) ∈
      Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  rw [functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
    k F b t]
  simpa only [Differential.coe_rationalAdicPolynomialDifferential] using
    (Differential.rationalAdicPolynomialDifferential p
      (directIntegralDifferentialTracePolynomial k F b t)).property

end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity

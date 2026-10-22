import Mathlib.RingTheory.Localization.NormTrace
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialTrace
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicSmithMatrixResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Direct Smith matrices and differential trace

An integral basis of the direct ring of integers localizes to a basis of the
function field over `k(X)`.  In that localized basis, the Smith logarithmic
matrix differential is the actual differential trace of an integral multiple
of a logarithmic differential upstairs.

This is a trace-side matrix identity.  It does not yet identify the resulting
rational residue with a sum of upper-place residues, or prove a global residue
theorem, duality, genus, canonical degree, or Riemann--Roch.
-/

open scoped Polynomial RatFunc nonZeroDivisors

namespace QEC.Coding.AlgebraicGeometry

namespace Differential

variable {k F : Type*} [Field k] [Finite k] [Field F]
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

private abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F

local instance : Module.IsTorsionFree k[X] (B (k := k) (F := F)) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)

local instance : Module.Finite k[X] (B (k := k) (F := F)) :=
  AffinePlace.finite_ringOfIntegers k F

local instance : IsLocalization
    (Algebra.algebraMapSubmonoid (B (k := k) (F := F)) k[X]⁰) F :=
  IsIntegralClosure.isLocalization_of_isSeparable
    k[X] (RatFunc k) F (B (k := k) (F := F))

private theorem functionFieldDerivation_extends_rationalDerivation
    (c : RatFunc k) :
    FunctionFieldDifferential.functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F c) =
      algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1 c) := by
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  rw [FunctionFieldDifferential.functionFieldDerivation,
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

private theorem rationalDiagonalMatrixInverse_mul_map_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : n → k[X]) (ha : ∀ i, a i ≠ 0) :
    rationalDiagonalMatrixInverse a *
        (algebraMap k[X] (RatFunc k)).mapMatrix (Matrix.diagonal a) = 1 := by
  classical
  unfold rationalDiagonalMatrixInverse
  simp only [RingHom.mapMatrix_apply]
  rw [Matrix.diagonal_map (map_zero (algebraMap k[X] (RatFunc k))),
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hai : algebraMap k[X] (RatFunc k) (a i) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (ha i)
    simp [Matrix.one_apply, hai]
  · simp [Matrix.one_apply, hij]

private theorem smith_target_matrix_eq_diagonal_mul_change
    {n : ℕ}
    (source target : Module.Basis (Fin n) k[X] (B (k := k) (F := F)))
    (a : Fin n → k[X])
    (t : B (k := k) (F := F))
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul k[X] (B (k := k) (F := F)) t) = Matrix.diagonal a) :
    LinearMap.toMatrix target target
        (Algebra.lmul k[X] (B (k := k) (F := F)) t) =
      Matrix.diagonal a * source.toMatrix target := by
  rw [← hdiag]
  symm
  exact linearMap_toMatrix_mul_basis_toMatrix target source target
    (Algebra.lmul k[X] (B (k := k) (F := F)) t)

/-- The ambient Smith logarithmic differential is the actual differential
trace of the integral coefficient times the logarithmic differential of the
Smith multiplier.  The proof localizes the integral target basis and derives
the inverse multiplication matrix from the Smith diagonalization. -/
theorem
    coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
    {n : ℕ}
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X]
      (_root_.FunctionField.ringOfIntegers k F))
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (t b : _root_.FunctionField.ringOfIntegers k F) (ht : t ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul k[X]
        (_root_.FunctionField.ringOfIntegers k F) t) = Matrix.diagonal a) :
    ((rationalAdicSmithLogarithmicDifferentialAtSimplePole p
        source target a ha
        (Algebra.lmul k[X]
          (_root_.FunctionField.ringOfIntegers k F) b) :
          simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      FunctionFieldDifferential.functionFieldDifferentialTrace
        (k := k) (F := F)
        ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F b) •
          logarithmicDifferential (k := k) (F := F)
            (algebraMap (_root_.FunctionField.ringOfIntegers k F) F t)) := by
  classical
  let m := algebraMap k[X] (RatFunc k)
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  let D := FunctionFieldDifferential.functionFieldDerivation (k := k) (F := F)
  let targetF := target.localizationLocalization
    (RatFunc k) k[X]⁰ F
  let T : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (LinearMap.toMatrix target target
      (Algebra.lmul k[X] (B (k := k) (F := F)) t))
  let G : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (LinearMap.toMatrix target target
      (Algebra.lmul k[X] (B (k := k) (F := F)) b))
  let P : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (target.toMatrix source)
  let Q : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (source.toMatrix target)
  let A : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (Matrix.diagonal a)
  let Ainv : Matrix (Fin n) (Fin n) (RatFunc k) :=
    rationalDiagonalMatrixInverse a
  let TF : Matrix (Fin n) (Fin n) (RatFunc k) :=
    LinearMap.toMatrix targetF targetF
      (Algebra.lmul (RatFunc k) F
        (algebraMap (B (k := k) (F := F)) F t))
  let UF : Matrix (Fin n) (Fin n) (RatFunc k) :=
    LinearMap.toMatrix targetF targetF
      (Algebra.lmul (RatFunc k) F
        (algebraMap (B (k := k) (F := F)) F t)⁻¹)
  have htF_ne : algebraMap (B (k := k) (F := F)) F t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective
      (B (k := k) (F := F)) F)).mpr ht
  have hTF : TF = T := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) k[X] k[X]⁰ target t
  have hGF :
      LinearMap.toMatrix targetF targetF
          (Algebra.lmul (RatFunc k) F
            (algebraMap (B (k := k) (F := F)) F b)) = G := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) k[X] k[X]⁰ target b
  have hT : T = A * Q := by
    have h := congrArg m.mapMatrix
      (smith_target_matrix_eq_diagonal_mul_change source target a t hdiag)
    simpa only [T, A, Q, map_mul] using h
  have hAinvA : Ainv * A = 1 := by
    exact rationalDiagonalMatrixInverse_mul_map_diagonal a ha
  have hPQ : P * Q = 1 := by
    have h := congrArg m.mapMatrix
      (Module.Basis.toMatrix_mul_toMatrix_flip target source)
    simpa only [P, Q, map_mul, map_one] using h
  have hcandidateT : (P * Ainv) * T = 1 := by
    rw [hT]
    calc
      (P * Ainv) * (A * Q) = P * (Ainv * A) * Q := by
        simp only [Matrix.mul_assoc]
      _ = P * Q := by rw [hAinvA, mul_one]
      _ = 1 := hPQ
  have hTFUF : TF * UF = 1 := by
    dsimp only [TF, UF]
    rw [← LinearMap.toMatrix_mul, ← map_mul,
      mul_inv_cancel₀ htF_ne, map_one, LinearMap.toMatrix_one]
  have hcandidateUF : P * Ainv = UF := by
    calc
      P * Ainv = (P * Ainv) * 1 := by rw [mul_one]
      _ = (P * Ainv) * (TF * UF) := by rw [hTFUF]
      _ = ((P * Ainv) * TF) * UF := by
        simp only [Matrix.mul_assoc]
      _ = UF := by rw [hTF, hcandidateT, one_mul]
  have htrace :=
    FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
      D₀ D
      (functionFieldDerivation_extends_rationalDerivation
        (k := k) (F := F)) targetF
      (algebraMap (B (k := k) (F := F)) F b)
      (algebraMap (B (k := k) (F := F)) F t) htF_ne
  have hcoordinate :
      FunctionFieldDifferential.functionFieldDifferentialCoordinate
          (k := k) (F := F)
          ((algebraMap (B (k := k) (F := F)) F b) •
            logarithmicDifferential (k := k) (F := F)
              (algebraMap (B (k := k) (F := F)) F t)) =
        algebraMap (B (k := k) (F := F)) F b *
          D (algebraMap (B (k := k) (F := F)) F t) *
            (algebraMap (B (k := k) (F := F)) F t)⁻¹ := by
    rw [logarithmicDifferential, map_smul, map_smul,
      FunctionFieldDifferential.functionFieldDifferentialCoordinate_differential]
    simp only [smul_eq_mul, D]
    ring
  rw [coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
      (p := p) source target a ha
      (Algebra.lmul k[X] (B (k := k) (F := F)) t)
      (Algebra.lmul k[X] (B (k := k) (F := F)) b) hdiag,
    FunctionFieldDifferential.functionFieldDifferentialTrace_apply,
    hcoordinate, htrace]
  rw [hGF]
  change Matrix.trace
      (G * P * Ainv * entrywiseMatrixDerivation D₀ T) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) =
    Matrix.trace
      (G * UF * entrywiseMatrixDerivation D₀ TF) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k)
  rw [show G * P * Ainv = G * (P * Ainv) from
      Matrix.mul_assoc G P Ainv,
    hcandidateUF, hTF]

end Differential

end QEC.Coding.AlgebraicGeometry

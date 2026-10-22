/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

import Mathlib.RingTheory.Trace.Basic
import QEC.Coding.AlgebraicGeometry.Differentials.Differential
import QEC.Coding.AlgebraicGeometry.Trace.MatrixDerivation

/-!
# Derivations and field trace

This module proves that the chosen derivation of a finite separable function
field commutes with the field trace to the rational function field.  The proof
uses a finite basis: differentiating a multiplication matrix introduces a
commutator with the matrix of the differentiated basis, and the trace of that
commutator vanishes.

This is an internal local-to-rational bridge for #722.  It contains no residue
sum, duality, genus, or Riemann--Roch conclusion.
-/

namespace QEC.Coding.AlgebraicGeometry

namespace FunctionFieldDifferential

open scoped RatFunc

section ConnectionTrace

variable {k K L : Type*} [Field k] [Field K] [Field L]
variable [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
variable [FiniteDimensional K L]

/-- A derivation of `L` applied to a scalar from `K` agrees with the chosen
derivation of `K`. -/
private abbrev DerivationExtends (D₀ : Derivation k K K) (D : Derivation k L L) : Prop :=
  ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c)

private theorem derivation_smul_of_extends
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (c : K) (x : L) :
    D (c • x) = D₀ c • x + c • D x := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
  rw [D.leibniz, hD]
  ring

/-- The connection induced by `D` on `K`-linear endomorphisms of `L`. -/
private noncomputable def derivationConnection
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (T : Module.End K L) : Module.End K L where
  toFun x := D (T x) - T (D x)
  map_add' x y := by
    simp only [map_add]
    abel
  map_smul' c x := by
    rw [T.map_smul, derivation_smul_of_extends D₀ D hD,
      derivation_smul_of_extends D₀ D hD, T.map_add, T.map_smul, T.map_smul]
    simp only [smul_sub]
    change
      D₀ c • T x + c • D (T x) - (D₀ c • T x + c • T (D x)) =
        c • D (T x) - c • T (D x)
    abel

private theorem derivation_repr
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K L) (x : L) (i : ι) :
    b.repr (D x) i =
      D₀ (b.repr x i) +
        ∑ j : ι, b.repr x j * b.repr (D (b j)) i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  simp_rw [derivation_smul_of_extends D₀ D hD]
  simp only [map_sum, map_add, map_smul, b.repr_self]
  rw [Finset.sum_add_distrib]
  simp [Finsupp.single_apply]

private theorem derivationConnection_repr
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K L) (T : Module.End K L) (i j : ι) :
    b.repr (derivationConnection D₀ D hD T (b j)) i =
      D₀ (b.repr (T (b j)) i) +
        ∑ r : ι, b.repr (D (b r)) i * b.repr (T (b j)) r -
          ∑ r : ι, b.repr (T (b r)) i * b.repr (D (b j)) r := by
  rw [derivationConnection]
  change b.repr (D (T (b j)) - T (D (b j))) i = _
  rw [map_sub, Finsupp.sub_apply, derivation_repr D₀ D hD b]
  have hTD :
      b.repr (T (D (b j))) i =
        ∑ r : ι, b.repr (T (b r)) i * b.repr (D (b j)) r := by
    change ((b.coord i).comp T) (D (b j)) = _
    conv_lhs => rw [← b.sum_repr (D (b j))]
    rw [map_sum]
    simp only [map_smul, LinearMap.comp_apply, b.coord_apply]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hTD]
  congr 2
  · apply Finset.sum_congr rfl
    intro r _
    ring

private theorem derivation_trace_connection
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (T : Module.End K L) :
    D₀ (LinearMap.trace K L T) =
      LinearMap.trace K L (derivationConnection D₀ D hD T) := by
  classical
  let b := Module.finBasis K L
  let A : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
    LinearMap.toMatrix b b T
  let B : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
    fun i j => b.repr (D (b j)) i
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b]
  simp only [Matrix.trace, map_sum]
  symm
  calc
    (∑ i, LinearMap.toMatrix b b (derivationConnection D₀ D hD T) i i) =
        ∑ i, (D₀ (A i i) + (B * A) i i - (A * B) i i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.toMatrix_apply, derivationConnection_repr D₀ D hD b]
      simp only [Matrix.mul_apply]
      simp only [A, B, LinearMap.toMatrix_apply]
    _ = (∑ i, D₀ (A i i)) + Matrix.trace (B * A) - Matrix.trace (A * B) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Matrix.trace,
        Matrix.diag_apply]
    _ = ∑ i, D₀ (A i i) := by
      rw [Matrix.trace_mul_comm]
      abel
    _ = ∑ i, D₀ (LinearMap.toMatrix b b T i i) := rfl

private theorem derivationConnection_lmul
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : DerivationExtends D₀ D) (x : L) :
    derivationConnection D₀ D hD (Algebra.lmul K L x) =
      Algebra.lmul K L (D x) := by
  ext y
  change D (x * y) - x * D y = D x * y
  rw [D.leibniz]
  ring

/-- The trace of a logarithmic derivative can be computed from the
entrywise derivative of one multiplication matrix.  The connection terms
introduced by differentiating the chosen basis cancel by cyclicity of matrix
trace.  This weighted form is the matrix bridge used by the wild-ramification
local residue argument. -/
theorem derivation_logarithmic_trace_eq_matrix_trace
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (r t : L) (ht : t ≠ 0) :
    Algebra.trace K L (r * D t * t⁻¹) =
      Matrix.trace
        (LinearMap.toMatrix b b (Algebra.lmul K L r) *
          LinearMap.toMatrix b b (Algebra.lmul K L t⁻¹) *
            entrywiseMatrixDerivation D₀
              (LinearMap.toMatrix b b (Algebra.lmul K L t))) := by
  classical
  let A := LinearMap.toMatrix b b (Algebra.lmul K L t)
  let U := LinearMap.toMatrix b b (Algebra.lmul K L t⁻¹)
  let R := LinearMap.toMatrix b b (Algebra.lmul K L r)
  let B : Matrix ι ι K := fun i j => b.repr (D (b j)) i
  let E : Matrix ι ι K := entrywiseMatrixDerivation D₀ A
  have hconnection :
      LinearMap.toMatrix b b (Algebra.lmul K L (D t)) =
        E + B * A - A * B := by
    rw [← derivationConnection_lmul D₀ D hD t]
    ext i j
    rw [LinearMap.toMatrix_apply,
      derivationConnection_repr D₀ D hD b]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
    simp only [E, B, A, LinearMap.toMatrix_apply,
      entrywiseMatrixDerivation_apply]
  have hAU : A * U = 1 := by
    dsimp only [A, U]
    rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel₀ ht,
      map_one, LinearMap.toMatrix_one]
  have hUA : U * A = 1 := by
    dsimp only [A, U]
    rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel₀ ht,
      map_one, LinearMap.toMatrix_one]
  have hUR : U * R = R * U := by
    calc
      U * R = LinearMap.toMatrix b b (Algebra.lmul K L (t⁻¹ * r)) := by
        rw [map_mul, LinearMap.toMatrix_mul]
      _ = LinearMap.toMatrix b b (Algebra.lmul K L (r * t⁻¹)) := by
        rw [mul_comm]
      _ = R * U := by
        rw [map_mul, LinearMap.toMatrix_mul]
  have hURA : U * (R * A) = R := by
    calc
      U * (R * A) = (U * R) * A := by rw [Matrix.mul_assoc]
      _ = (R * U) * A := by rw [hUR]
      _ = R * (U * A) := by rw [Matrix.mul_assoc]
      _ = R := by rw [hUA, mul_one]
  have htrace_E : Matrix.trace (R * E * U) = Matrix.trace (R * U * E) := by
    calc
      Matrix.trace (R * E * U) = Matrix.trace (U * R * E) :=
        Matrix.trace_mul_cycle R E U
      _ = Matrix.trace (R * U * E) := by rw [hUR]
  have htrace_BA : Matrix.trace (R * B * A * U) = Matrix.trace (R * B) := by
    rw [Matrix.mul_assoc (R * B) A U, hAU, mul_one]
  have htrace_AB : Matrix.trace (R * A * B * U) = Matrix.trace (R * B) := by
    calc
      Matrix.trace (R * A * B * U) = Matrix.trace (U * (R * A * B)) :=
        Matrix.trace_mul_comm (R * A * B) U
      _ = Matrix.trace ((U * (R * A)) * B) := by
        rw [Matrix.mul_assoc U (R * A) B]
      _ = Matrix.trace (R * B) := by rw [hURA]
  have hlmul : Algebra.lmul K L (r * D t * t⁻¹) =
      Algebra.lmul K L r * Algebra.lmul K L (D t) * Algebra.lmul K L t⁻¹ := by
    ext x
    change (r * D t * t⁻¹) * x = r * (D t * (t⁻¹ * x))
    ring
  rw [show Algebra.trace K L (r * D t * t⁻¹) =
      LinearMap.trace K L (Algebra.lmul K L (r * D t * t⁻¹)) from rfl,
    LinearMap.trace_eq_matrix_trace K b]
  change Matrix.trace
      (LinearMap.toMatrix b b (Algebra.lmul K L (r * D t * t⁻¹))) = _
  calc
    _ = Matrix.trace (R * (E + B * A - A * B) * U) := by
      congr 1
      rw [hlmul, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hconnection]
    _ = Matrix.trace (R * E * U) + Matrix.trace (R * B * A * U) -
        Matrix.trace (R * A * B * U) := by
      simp only [mul_sub, mul_add, sub_mul, add_mul, Matrix.trace_sub,
        Matrix.trace_add, Matrix.mul_assoc]
    _ = Matrix.trace (R * E * U) := by rw [htrace_BA, htrace_AB, add_sub_cancel_right]
    _ = Matrix.trace (R * U * E) := htrace_E
    _ = _ := by rfl

end ConnectionTrace

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]

/-- The chosen function-field derivation commutes with the field trace to the
rational function field. -/
theorem functionFieldDerivation_trace (x : F) :
    RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
        (Algebra.trace (RatFunc k) F x) =
      Algebra.trace (RatFunc k) F
        (functionFieldDerivation (k := k) (F := F) x) := by
  let D₀ := RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1
  let D := functionFieldDerivation (k := k) (F := F)
  have hD : DerivationExtends D₀ D := by
    intro c
    change functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F c) =
      algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1 c)
    rw [functionFieldDerivation,
      SeparableDerivationExtension.separableDerivationExtension_apply_algebraMap]
    let Dmap : Derivation k (RatFunc k) F :=
      (Algebra.ofId (RatFunc k) F).toLinearMap.compDer D₀
    have hmap :
        RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 = Dmap := by
      have hX : Dmap RatFunc.X = (1 : F) := by
        change algebraMap (RatFunc k) F
          (RatFuncDerivation.rationalDerivation (k := k) (M := RatFunc k) 1 RatFunc.X) = 1
        rw [RatFuncDerivation.rationalDerivation_apply_X, map_one]
      rw [← hX]
      exact RatFuncDerivation.rationalDerivation_eq_of_apply_X (k := k)
    have hc := Derivation.congr_fun hmap c
    change RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 c =
      algebraMap (RatFunc k) F (D₀ c) at hc
    exact hc
  rw [show Algebra.trace (RatFunc k) F x =
      LinearMap.trace (RatFunc k) F (Algebra.lmul (RatFunc k) F x) from rfl,
    show Algebra.trace (RatFunc k) F (D x) =
      LinearMap.trace (RatFunc k) F (Algebra.lmul (RatFunc k) F (D x)) from rfl,
    ← derivationConnection_lmul D₀ D hD x]
  exact derivation_trace_connection D₀ D hD (Algebra.lmul (RatFunc k) F x)

end FunctionFieldDifferential

end QEC.Coding.AlgebraicGeometry

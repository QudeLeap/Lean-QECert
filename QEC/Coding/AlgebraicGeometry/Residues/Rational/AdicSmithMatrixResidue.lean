import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicPolynomialMatrixResidue
import QEC.Coding.AlgebraicGeometry.Residues.Rational.AdicSmithTraceResidue

/-
Copyright (c) 2026 Lean-QEC contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean-QEC contributors
-/

/-!
# Weighted Smith matrix residues at finite rational places

For a Smith diagonal matrix followed by the polynomial change from a target
basis to a source basis, this module splits a weighted logarithmic matrix
trace into its diagonal term and one polynomial change-of-basis term.  The
polynomial term has zero finite residue, while the diagonal term is the
primary trace of the Smith cokernel.

This is still a polynomial-matrix calculation over `k[X]` and `k(X)`.  It
does not identify a traced differential in a finite extension with the sum of
upper-place residues, or prove a global residue theorem, duality, genus,
canonical degree, or Riemann--Roch.
-/

open scoped Polynomial RatFunc

namespace QEC.Coding.AlgebraicGeometry

variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]

/-- The weighted logarithmic derivative of a diagonal matrix followed by a
change-of-basis matrix splits into a diagonal term and a change-of-basis
term.  The conjugated weight on the diagonal side is supplied explicitly. -/
theorem entrywiseMatrixDerivation_trace_weighted_diagonal_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k₀ K K)
    (Gt Gs P A Ainv Q : Matrix n n K)
    (hAinvA : Ainv * A = 1)
    (hconj : Q * Gt * P = Gs) :
    Matrix.trace
        (Gt * P * Ainv * entrywiseMatrixDerivation D (A * Q)) =
      Matrix.trace (Gs * Ainv * entrywiseMatrixDerivation D A) +
        Matrix.trace ((Gt * P) * entrywiseMatrixDerivation D Q) := by
  let DA := entrywiseMatrixDerivation D A
  let DQ := entrywiseMatrixDerivation D Q
  rw [entrywiseMatrixDerivation_mul]
  change Matrix.trace (Gt * P * Ainv * (DA * Q + A * DQ)) = _
  rw [mul_add, Matrix.trace_add]
  congr 1
  · calc
      Matrix.trace (Gt * P * Ainv * (DA * Q)) =
          Matrix.trace ((Gt * P * Ainv * DA) * Q) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * (Gt * P * Ainv * DA)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Q * Gt * P) * Ainv * DA) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Gs * Ainv * DA) := by rw [hconj]
  · congr 1
    calc
      Gt * P * Ainv * (A * DQ) =
          (Gt * P) * (Ainv * A) * DQ := by
            simp only [Matrix.mul_assoc]
      _ = (Gt * P) * DQ := by rw [hAinvA, mul_one]

namespace Differential

variable {k : Type*} [Field k] [Finite k]

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
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (f : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    LinearMap.toMatrix target target f =
      Matrix.diagonal a * source.toMatrix target := by
  rw [← hdiag]
  symm
  exact linearMap_toMatrix_mul_basis_toMatrix target source target f

private theorem smith_change_conjugates_target_matrix
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (g : N →ₗ[k[X]] N) :
    source.toMatrix target * LinearMap.toMatrix target target g *
        target.toMatrix source =
      LinearMap.toMatrix source source g := by
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    source target source target g

private theorem smith_commuting_diagonal_eq
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f) (i : Fin n) :
    LinearMap.toMatrix source source g i i =
      LinearMap.toMatrix target target g i i := by
  have hmatrix := congrArg (LinearMap.toMatrix source target) hcomm
  rw [LinearMap.toMatrix_comp source source target,
    LinearMap.toMatrix_comp source target target, hdiag] at hmatrix
  have hii := congrFun (congrFun hmatrix i) i
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hii
  exact mul_left_cancel₀ (ha i) (by simpa only [mul_comm] using hii)

/-- The simple-pole differential represented by the Smith diagonal term and
the polynomial target-to-source change-of-basis term. -/
noncomputable def rationalAdicSmithLogarithmicDifferentialAtSimplePole
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (g : N →ₗ[k[X]] N) :
    simplePoleDifferentialLattice (GlobalPlace.rationalAdic p) :=
  rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
      (LinearMap.toMatrix source source g) a ha +
    polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p
      (LinearMap.toMatrix target target g * target.toMatrix source)
      (source.toMatrix target)

/-- The ambient coefficient of the Smith logarithmic differential is the
weighted logarithmic derivative of the multiplication matrix in the target
basis. -/
theorem coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    ((rationalAdicSmithLogarithmicDifferentialAtSimplePole p
      source target a ha g :
        simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
          Differential k (RatFunc k)) =
      Matrix.trace
          (((algebraMap k[X] (RatFunc k)).mapMatrix
                (LinearMap.toMatrix target target g) *
              (algebraMap k[X] (RatFunc k)).mapMatrix
                (target.toMatrix source)) *
            rationalDiagonalMatrixInverse a *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix
                (LinearMap.toMatrix target target f))) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) := by
  classical
  let m := algebraMap k[X] (RatFunc k)
  let Gt := m.mapMatrix (LinearMap.toMatrix target target g)
  let Gs := m.mapMatrix (LinearMap.toMatrix source source g)
  let P := m.mapMatrix (target.toMatrix source)
  let A := m.mapMatrix (Matrix.diagonal a)
  let Ainv := rationalDiagonalMatrixInverse a
  let Q := m.mapMatrix (source.toMatrix target)
  let D := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  have hAinvA : Ainv * A = 1 := by
    exact rationalDiagonalMatrixInverse_mul_map_diagonal a ha
  have hconj : Q * Gt * P = Gs := by
    have h := congrArg m.mapMatrix
      (smith_change_conjugates_target_matrix source target g)
    simpa only [map_mul] using h
  have hfmatrix : m.mapMatrix (LinearMap.toMatrix target target f) = A * Q := by
    have h := congrArg m.mapMatrix
      (smith_target_matrix_eq_diagonal_mul_change source target a f hdiag)
    simpa only [map_mul] using h
  unfold rationalAdicSmithLogarithmicDifferentialAtSimplePole
  change (simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)).subtype
      (_ + _) = _
  rw [map_add]
  have hdiagCoe :=
    coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
      (LinearMap.toMatrix source source g) a ha
  have hpolyCoe :=
    coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p
      (LinearMap.toMatrix target target g * target.toMatrix source)
      (source.toMatrix target)
  change (simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p)).subtype
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
          (LinearMap.toMatrix source source g) a ha) = _ at hdiagCoe
  change (simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p)).subtype
        (polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p
          (LinearMap.toMatrix target target g * target.toMatrix source)
          (source.toMatrix target)) = _ at hpolyCoe
  rw [hdiagCoe, hpolyCoe]
  rw [← add_smul]
  congr 1
  rw [map_mul]
  change Matrix.trace (Gs * Ainv * entrywiseMatrixDerivation D A) +
      Matrix.trace ((Gt * P) * entrywiseMatrixDerivation D Q) =
    Matrix.trace (Gt * P * Ainv *
      entrywiseMatrixDerivation D
        (m.mapMatrix (LinearMap.toMatrix target target f)))
  rw [hfmatrix]
  exact (entrywiseMatrixDerivation_trace_weighted_diagonal_mul
    D Gt Gs P A Ainv Q hAinvA hconj).symm

/-- The normalized residue of the Smith logarithmic differential is the
transported primary trace of the actual Smith cokernel. -/
theorem simplePoleResidue_rationalAdicSmithLogarithmicDifferential
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha g) =
      GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism f g hcomm) depth) := by
  have hgdiag : ∀ i, LinearMap.toMatrix source source g i i =
      LinearMap.toMatrix target target g i i :=
    smith_commuting_diagonal_eq source target a ha f g hdiag hcomm
  have hdiagonal :
      simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix source source g) a ha) =
        simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix target target g) a ha) := by
    rw [simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential,
      simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential]
    apply Finset.sum_congr rfl
    intro i _
    rw [hgdiag i]
  calc
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha g) =
        simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix source source g) a ha) := by
      unfold rationalAdicSmithLogarithmicDifferentialAtSimplePole
      rw [map_add,
        simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential,
        add_zero]
    _ = simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix target target g) a ha) := hdiagonal
    _ = GlobalPlace.rationalAdicIdealResidueEquiv p
          (primaryTorsionTrace p.asIdeal
            (cokernelEndomorphism f g hcomm) depth) :=
      (rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
        source target a ha f g hdiag hcomm p depth hdepth).symm

end Differential

end QEC.Coding.AlgebraicGeometry

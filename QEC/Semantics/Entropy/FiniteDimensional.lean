import QEC.Semantics.Core.Definitions
/-!
# Finite-dimensional von Neumann entropy

This module defines the base-two von Neumann entropy of a finite-dimensional
density operator through the multiset of roots of its characteristic
polynomial. `FiniteQuantumSystem` supplies finite complex dimension, while
the `DensityOperator` fields supply positivity and trace one. Positivity
supplies Hermitian spectral diagonalization, so the roots are precisely the
nonnegative real eigenvalues counted with multiplicity.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

namespace DensityOperator

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- The base-two entropy contribution, with the exact convention `0 log 0 = 0`. -/
def entropyTerm (x : Real) : Real :=
  if x = 0 then 0 else -x * Real.logb 2 x

@[simp]
theorem entropyTerm_zero : entropyTerm 0 = 0 := by
  simp [entropyTerm]

@[simp]
theorem entropyTerm_one : entropyTerm 1 = 0 := by
  simp [entropyTerm]

@[simp]
theorem entropyTerm_half : entropyTerm (1 / 2 : Real) = 1 / 2 := by
  rw [entropyTerm, if_neg (by norm_num)]
  have hhalf : (1 / 2 : Real) = (2 : Real)⁻¹ := by norm_num
  rw [hhalf, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- The finite spectrum, including algebraic multiplicities, of a density operator. -/
def finiteSpectrum (rho : DensityOperator H) : Multiset Real :=
  rho.toOperator.charpoly.roots.map Complex.re

/-- Base-two von Neumann entropy from the finite Hermitian spectrum. -/
def vonNeumannEntropy (rho : DensityOperator H) : Real :=
  (rho.finiteSpectrum.map entropyTerm).sum

/-- Mathlib's canonical decreasing enumeration of the Hermitian spectrum. -/
def spectralEigenvalues (rho : DensityOperator H) :
    Fin (Module.finrank Complex H) -> Real :=
  rho.positive.isSymmetric.eigenvalues rfl

theorem spectralEigenvalues_nonnegative (rho : DensityOperator H)
    (i : Fin (Module.finrank Complex H)) :
    0 <= rho.spectralEigenvalues i := by
  exact rho.positive.nonneg_eigenvalues rfl i

theorem spectralEigenvalues_sum_eq_one (rho : DensityOperator H) :
    (∑ i, rho.spectralEigenvalues i : Real) = 1 := by
  have htrace := rho.positive.isSymmetric.re_trace_eq_sum_eigenvalues rfl
  rw [rho.trace_one] at htrace
  simpa [spectralEigenvalues] using htrace.symm

/-- The characteristic-polynomial definition agrees with the finite eigenvalue sum. -/
theorem vonNeumannEntropy_eq_sum_spectralEigenvalues (rho : DensityOperator H) :
    rho.vonNeumannEntropy = ∑ i, entropyTerm (rho.spectralEigenvalues i) := by
  unfold vonNeumannEntropy finiteSpectrum spectralEigenvalues
  rw [rho.positive.isSymmetric.roots_charpoly_eq_eigenvalues rfl]
  simp [Function.comp_def, List.sum_ofFn]

/-- Reindexing a finite spectral enumeration does not change the entropy sum. -/
theorem spectralEntropy_sum_reindex {ι : Type*} [Fintype ι]
    (rho : DensityOperator H) (e : ι ≃ Fin (Module.finrank Complex H)) :
    (∑ i, entropyTerm (rho.spectralEigenvalues (e i))) = rho.vonNeumannEntropy := by
  rw [rho.vonNeumannEntropy_eq_sum_spectralEigenvalues]
  exact Fintype.sum_equiv e _ _ (by intro i; rfl)

/-- Equality of finite characteristic-polynomial spectra implies equal entropy. -/
theorem vonNeumannEntropy_eq_of_charpoly_eq {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K)
    (hcharpoly : rho.toOperator.charpoly = sigma.toOperator.charpoly) :
    rho.vonNeumannEntropy = sigma.vonNeumannEntropy := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [hcharpoly]

/-- The entropy is independent of the coordinate basis used for its matrix spectrum. -/
theorem vonNeumannEntropy_eq_basisMatrixSpectrum
    (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    rho.vonNeumannEntropy =
      (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [LinearMap.charpoly_toMatrix]

/-- Two orthonormal coordinate bases give the same finite spectral entropy. -/
theorem basisMatrixSpectralEntropy_independent
    (rho : DensityOperator H)
    (b c : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (((rho.toOperator.toMatrix b.toBasis b.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum =
      (((rho.toOperator.toMatrix c.toBasis c.toBasis).charpoly.roots.map Complex.re).map
        entropyTerm).sum := by
  rw [<- rho.vonNeumannEntropy_eq_basisMatrixSpectrum b,
    <- rho.vonNeumannEntropy_eq_basisMatrixSpectrum c]

/-- Hermitian coordinate matrix for use with Mathlib's finite functional calculus. -/
def spectralMatrix (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    Matrix (Fin (Module.finrank Complex H)) (Fin (Module.finrank Complex H)) Complex :=
  rho.toOperator.toMatrix b.toBasis b.toBasis

theorem spectralMatrix_isHermitian (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (rho.spectralMatrix b).IsHermitian := by
  exact (LinearMap.isHermitian_toMatrix_iff b).2 rho.positive.isSymmetric

/-- The entropy is the real trace of Mathlib's finite Hermitian functional calculus. -/
theorem vonNeumannEntropy_eq_trace_entropyFunctionalCalculus
    (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (rho.vonNeumannEntropy : Complex) =
      Matrix.trace ((rho.spectralMatrix_isHermitian b).cfc entropyTerm) := by
  let A := rho.spectralMatrix b
  let hA : A.IsHermitian := rho.spectralMatrix_isHermitian b
  change (rho.vonNeumannEntropy : Complex) = Matrix.trace (hA.cfc entropyTerm)
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rw [rho.vonNeumannEntropy_eq_basisMatrixSpectrum b]
  change
    (((A.charpoly.roots.map Complex.re).map entropyTerm).sum : Complex) =
      ∑ i, (entropyTerm (hA.eigenvalues i) : Complex)
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp [Function.comp_def, List.sum_ofFn]

/-- Unitary conjugation preserves the finite-dimensional von Neumann entropy. -/
theorem vonNeumannEntropy_conjDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (U : UnitaryTransport H K) (rho : DensityOperator H) :
    (U.conjDensity rho).vonNeumannEntropy = rho.vonNeumannEntropy := by
  apply vonNeumannEntropy_eq_of_charpoly_eq
  simp [UnitaryTransport.conjDensity_toOperator,
    UnitaryTransport.conjOperator_eq_linearEquiv_conj]

/-- A diagonal finite-dimensional density operator from nonnegative weights summing to one. -/
noncomputable def diagonalDensity (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    DensityOperator (EuclideanSpace Complex (Fin n)) where
  toOperator := Matrix.toEuclideanLin (Matrix.diagonal fun i => (p i : Complex))
  positive := by
    apply Matrix.isPositive_toEuclideanLin_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · apply Matrix.isHermitian_diagonal_iff.mpr
      intro i
      change star (p i : Complex) = (p i : Complex)
      simp
    · intro x
      have hquadratic :
          dotProduct (star x) (Matrix.mulVec (Matrix.diagonal fun i => (p i : Complex)) x) =
            ((∑ i, p i * Complex.normSq (x i) : Real) : Complex) := by
        simp [dotProduct, Matrix.mulVec_diagonal, Complex.normSq_eq_conj_mul_self,
          mul_comm, mul_left_comm, mul_assoc]
      rw [hquadratic]
      exact (RCLike.ofReal_nonneg (K := Complex)).mpr
        (Fintype.sum_nonneg fun i => mul_nonneg (hp i) (Complex.normSq_nonneg _))
  trace_one := by
    change LinearMap.trace Complex _
      (Matrix.toLin (EuclideanSpace.basisFun (Fin n) Complex).toBasis
        (EuclideanSpace.basisFun (Fin n) Complex).toBasis
        (Matrix.diagonal fun i => (p i : Complex))) = 1
    rw [Matrix.trace_toLin_eq]
    simp only [Matrix.trace_diagonal]
    exact_mod_cast hsum

theorem diagonalDensity_charpoly (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).toOperator.charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly := by
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin n) Complex).toBasis
    (EuclideanSpace.basisFun (Fin n) Complex).toBasis
    (Matrix.diagonal fun i => (p i : Complex))).charpoly =
      (Matrix.diagonal fun i => (p i : Complex)).charpoly
  rw [Matrix.charpoly_toLin]

/-- The entropy of a diagonal density operator is the corresponding finite weight sum. -/
theorem vonNeumannEntropy_diagonalDensity (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    (diagonalDensity n p hp hsum).vonNeumannEntropy = ∑ i, entropyTerm (p i) := by
  unfold vonNeumannEntropy finiteSpectrum
  rw [diagonalDensity_charpoly]
  rw [Matrix.charpoly_diagonal]
  rw [Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp [Function.comp_def, List.sum_ofFn]

/-- The two-level diagonal state with spectrum `(1, 0)`. -/
noncomputable def diagOneZero : DensityOperator (EuclideanSpace Complex (Fin 2)) :=
  diagonalDensity 2 (fun i => if i = 0 then 1 else 0)
    (by intro i; by_cases h : i = 0 <;> simp [h])
    (by rw [Fin.sum_univ_two]; simp)

/-- The maximally mixed two-level diagonal state with spectrum `(1/2, 1/2)`. -/
noncomputable def diagHalfHalf : DensityOperator (EuclideanSpace Complex (Fin 2)) :=
  diagonalDensity 2 (fun _ => 1 / 2)
    (by intro i; norm_num)
    (by rw [Fin.sum_univ_two]; norm_num)

theorem vonNeumannEntropy_diagOneZero : diagOneZero.vonNeumannEntropy = 0 := by
  rw [diagOneZero, vonNeumannEntropy_diagonalDensity]
  rw [Fin.sum_univ_two]
  simp

theorem vonNeumannEntropy_diagHalfHalf : diagHalfHalf.vonNeumannEntropy = 1 := by
  rw [diagHalfHalf, vonNeumannEntropy_diagonalDensity]
  rw [Fin.sum_univ_two]
  change entropyTerm (1 / 2 : Real) + entropyTerm (1 / 2 : Real) = 1
  rw [entropyTerm_half]
  norm_num

end DensityOperator

end
end Semantics
end QEC

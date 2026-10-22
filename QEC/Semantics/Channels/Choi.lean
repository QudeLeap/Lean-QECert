import QEC.Semantics.Channels.Core
/-!
# Project-local Choi matrices

This module defines a concrete Choi matrix for project operator-space maps by
choosing finite orthonormal bases.  The positivity theorem is proved from the
project `CompletelyPositive` predicate by applying it to the matrix-unit block
and then scalarizing the resulting positive operator block matrix.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

namespace OperatorMatrix

variable {n : Nat} {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

/-- The rank-one matrix unit `|b i><b j|` associated to an orthonormal basis. -/
noncomputable def matrixUnit (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) :
    Operator H :=
  (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap

@[simp]
theorem matrixUnit_apply (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) (x : H) :
    matrixUnit b i j x = inner Complex (b j) x • b i :=
  rfl

/-- Matrix units are adjoint-transposes. -/
theorem matrixUnit_adjoint (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) :
    LinearMap.adjoint (matrixUnit b i j) = matrixUnit b j i := by
  haveI := FiniteDimensional.complete Complex H
  change LinearMap.adjoint ((InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap) =
    (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap
  rw [LinearMap.adjoint_eq_toCLM_adjoint]
  exact congrArg ContinuousLinearMap.toLinearMap
    (InnerProductSpace.adjoint_rankOne (𝕜 := Complex) (b i) (b j))

/-- The operator-valued block matrix whose entries are matrix units. -/
noncomputable def matrixUnitBlock (b : OrthonormalBasis (Fin n) Complex H) :
    OperatorMatrix n H :=
  fun i j => matrixUnit b i j

/--
The matrix-unit block is positive for the project block-positivity predicate.

Its quadratic form is the squared norm of the scalar
`∑ i, inner (b i) (x i)`.
-/
theorem matrixUnitBlock_isPositive (b : OrthonormalBasis (Fin n) Complex H) :
    IsPositive (matrixUnitBlock b) := by
  classical
  constructor
  · intro i j
    change matrixUnit b j i = LinearMap.adjoint (matrixUnit b i j)
    rw [matrixUnit_adjoint]
  · intro x
    let coeff : Fin n → Complex := fun i => inner Complex (b i) (x i)
    have hQuadratic :
        (∑ i : Fin n, ∑ j : Fin n,
          inner Complex ((matrixUnitBlock b) i j (x j)) (x i)) =
          (∑ i : Fin n, coeff i) * star (∑ i : Fin n, coeff i) := by
      calc
        (∑ i : Fin n, ∑ j : Fin n,
            inner Complex ((matrixUnitBlock b) i j (x j)) (x i))
            = ∑ i : Fin n, ∑ j : Fin n, coeff i * star (coeff j) := by
              simp [matrixUnitBlock, matrixUnit, coeff]
        _ = (∑ i : Fin n, coeff i) * (∑ j : Fin n, star (coeff j)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _hi
              simp [Finset.mul_sum]
        _ = (∑ i : Fin n, coeff i) * star (∑ i : Fin n, coeff i) := by
              rw [star_sum]
    rw [hQuadratic]
    simpa [Complex.mul_conj, Complex.normSq_apply] using
      Complex.normSq_nonneg (∑ i : Fin n, coeff i)

/--
Every operator expands in the matrix units associated to a finite
orthonormal basis.
-/
theorem matrixUnit_expansion
    (b : OrthonormalBasis (Fin n) Complex H) (A : Operator H) :
    A = ∑ i : Fin n, ∑ j : Fin n,
      (b.repr (A (b j)) i) • matrixUnit b i j := by
  classical
  apply (Module.Basis.ext b.toBasis)
  intro k
  change A (b k) = (∑ i : Fin n, ∑ j : Fin n,
    (b.repr (A (b j)) i) • matrixUnit b i j) (b k)
  have hinner : ∀ j : Fin n, inner Complex (b j) (b k) = if j = k then 1 else 0 := by
    intro j
    exact (orthonormal_iff_ite.mp b.orthonormal) j k
  rw [← OrthonormalBasis.sum_repr' b (A (b k))]
  simp [matrixUnit_apply, hinner, OrthonormalBasis.repr_apply_apply]

end OperatorMatrix

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/--
The project-local Choi matrix of an operator-space map, relative to chosen
orthonormal bases of the input and output systems.
-/
noncomputable def choiMatrix {n : Nat} {βK : Type*} [Fintype βK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K) :
    Matrix (Fin n × βK) (Fin n × βK) Complex :=
  OperatorMatrix.scalarMatrix
    (OperatorMatrix.map Φ (OperatorMatrix.matrixUnitBlock bH)) bK

/--
The project-local Choi matrix determines an operator-space linear map once
finite orthonormal bases are fixed.
-/
theorem choiMatrix_ext {n : Nat} {βK : Type*} [Fintype βK]
    (Φ Ψ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K)
    (h : choiMatrix Φ bH bK = choiMatrix Ψ bH bK) :
    Φ = Ψ := by
  classical
  have hUnit : ∀ i j : Fin n,
      Φ (OperatorMatrix.matrixUnit bH i j) =
        Ψ (OperatorMatrix.matrixUnit bH i j) := by
    intro i j
    apply (Module.Basis.ext bK.toBasis)
    intro q
    change Φ (OperatorMatrix.matrixUnit bH i j) (bK q) =
      Ψ (OperatorMatrix.matrixUnit bH i j) (bK q)
    apply (ext_iff_inner_right Complex).2
    intro v
    rw [← OrthonormalBasis.sum_repr' bK v]
    simp only [inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro p _hp
    have hentry :
        inner Complex (Φ (OperatorMatrix.matrixUnit bH i j) (bK q)) (bK p) =
          inner Complex (Ψ (OperatorMatrix.matrixUnit bH i j) (bK q)) (bK p) := by
      have hentry := congrFun (congrFun h (i, p)) (j, q)
      simpa [choiMatrix, OperatorMatrix.scalarMatrix, OperatorMatrix.map,
        OperatorMatrix.matrixUnitBlock] using hentry
    rw [hentry]
  apply LinearMap.ext
  intro A
  calc
    Φ A = Φ (∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • OperatorMatrix.matrixUnit bH i j) := by
      rw [← OperatorMatrix.matrixUnit_expansion bH A]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • Φ (OperatorMatrix.matrixUnit bH i j) := by
      simp
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • Ψ (OperatorMatrix.matrixUnit bH i j) := by
      simp [hUnit]
    _ = Ψ (∑ i : Fin n, ∑ j : Fin n,
        (bH.repr (A (bH j)) i) • OperatorMatrix.matrixUnit bH i j) := by
      simp
    _ = Ψ A := by
      rw [← OperatorMatrix.matrixUnit_expansion bH A]

/--
Complete positivity in the project matrix-amplification sense makes the
project-local Choi matrix positive semidefinite.
-/
theorem choiMatrix_posSemidef_of_completelyPositive {n : Nat} {βK : Type*}
    [Fintype βK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hΦ : CompletelyPositive Φ)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K) :
    (choiMatrix Φ bH bK).PosSemidef := by
  classical
  exact OperatorMatrix.isPositive_to_scalar_posSemidef
    (OperatorMatrix.map Φ (OperatorMatrix.matrixUnitBlock bH))
    (hΦ n (OperatorMatrix.matrixUnitBlock bH)
      (OperatorMatrix.matrixUnitBlock_isPositive bH))
    bK

/-- The Choi matrix using Mathlib's standard orthonormal bases on both systems. -/
noncomputable def stdChoiMatrix (Φ : Operator H →ₗ[Complex] Operator K) :
    Matrix
      (Fin (Module.finrank Complex H) × Fin (Module.finrank Complex K))
      (Fin (Module.finrank Complex H) × Fin (Module.finrank Complex K)) Complex :=
  choiMatrix Φ (stdOrthonormalBasis Complex H) (stdOrthonormalBasis Complex K)

/-- Standard-basis Choi positivity from project complete positivity. -/
theorem stdChoiMatrix_posSemidef_of_completelyPositive
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hΦ : CompletelyPositive Φ) :
    (stdChoiMatrix Φ).PosSemidef := by
  exact choiMatrix_posSemidef_of_completelyPositive Φ hΦ
    (stdOrthonormalBasis Complex H) (stdOrthonormalBasis Complex K)

end Semantics
end QEC

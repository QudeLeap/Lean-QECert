import QEC.Semantics.Channels.Choi
import QEC.Semantics.Channels.Kraus
/-!
# Choi-coordinate vectors as finite Kraus branches

This module constructs project Kraus operators from Choi-coordinate vectors and
computes the Choi matrix of the induced finite Kraus map as the corresponding
sum of rank-one vector outer products.
-/

universe u

namespace QEC
namespace Semantics

open scoped BigOperators ComplexOrder

noncomputable section

variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

/--
The Kraus operator whose Choi-coordinate coefficients are the vector `v`.

The matrix uses conjugated entries because Mathlib's inner product is linear in
the second argument, while the Choi coordinate below is stated as
`inner (R (bH i)) (bK p)`.
-/
noncomputable def krausOperatorOfChoiVector {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) :
    KrausOperator H K :=
  Matrix.toLin bH.toBasis bK.toBasis (fun p i => star (v (i, p)))

theorem krausOperatorOfChoiVector_toMatrix {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) :
    LinearMap.toMatrix bH.toBasis bK.toBasis (krausOperatorOfChoiVector bH bK v) =
      fun p i => star (v (i, p)) := by
  classical
  unfold krausOperatorOfChoiVector
  exact LinearMap.toMatrix_toLin bH.toBasis bK.toBasis _

/-- The constructed branch has the requested Choi-coordinate coefficients. -/
theorem krausOperatorOfChoiVector_inner_basis {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p) = v (i, p) := by
  have hmatrix := congrFun (congrFun
    (krausOperatorOfChoiVector_toMatrix bH bK v) p) i
  rw [LinearMap.toMatrix_apply] at hmatrix
  have hrepr :
      bK.repr ((krausOperatorOfChoiVector bH bK v) (bH i)) p =
        star (v (i, p)) := by
    simpa [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply] using hmatrix
  calc
    inner Complex ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p)
        = star (inner Complex (bK p) ((krausOperatorOfChoiVector bH bK v) (bH i))) := by
          exact (inner_conj_symm ((krausOperatorOfChoiVector bH bK v) (bH i)) (bK p)).symm
    _ = star (bK.repr ((krausOperatorOfChoiVector bH bK v) (bH i)) p) := by
          rw [OrthonormalBasis.repr_apply_apply]
    _ = v (i, p) := by
          simp [hrepr]

theorem krausOperatorOfChoiVector_adjoint_inner_basis {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex (bH i)
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p)) =
      v (i, p) := by
  rw [LinearMap.adjoint_inner_right]
  exact krausOperatorOfChoiVector_inner_basis bH bK v i p

theorem krausOperatorOfChoiVector_adjoint_inner_basis_conj {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
      (bH i) =
      star (v (i, p)) := by
  calc
    inner Complex
        ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
        (bH i)
        = star (inner Complex (bH i)
            ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))) := by
          exact (inner_conj_symm
            ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
            (bH i)).symm
    _ = star (v (i, p)) := by
          rw [krausOperatorOfChoiVector_adjoint_inner_basis]

/-- The finite Kraus family whose branches are built from Choi-coordinate vectors. -/
noncomputable def finiteKrausFamilyOfChoiVectors {m n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin m → (Fin n × betaK → Complex)) :
    FiniteKrausFamily (Fin m) H K where
  operator a := krausOperatorOfChoiVector bH bK (v a)

private theorem krausOperatorOfChoiVector_matrixUnit_apply_inner {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i j : Fin n) (p q : betaK) :
    inner Complex
      (((krausOperatorOfChoiVector bH bK v).comp
          ((OperatorMatrix.matrixUnit bH i j).comp
            (LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)))) (bK q))
      (bK p) =
      v (i, p) * star (v (j, q)) := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rw [← LinearMap.adjoint_inner_right (𝕜 := Complex)
    (krausOperatorOfChoiVector bH bK v)
    ((OperatorMatrix.matrixUnit bH i j)
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK q)))
    (bK p)]
  rw [OperatorMatrix.matrixUnit_apply]
  rw [inner_smul_left]
  rw [krausOperatorOfChoiVector_adjoint_inner_basis bH bK v j q]
  rw [krausOperatorOfChoiVector_adjoint_inner_basis bH bK v i p]
  rw [mul_comm]
  rw [starRingEnd_apply]

/--
The Choi matrix of the induced map from Choi-coordinate Kraus branches is the
sum of the rank-one outer products of those coordinate vectors.
-/
theorem choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap {m n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin m → (Fin n × betaK → Complex)) :
    choiMatrix ((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap) bH bK =
      ∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a)) := by
  classical
  ext ip jq
  rcases ip with ⟨i, p⟩
  rcases jq with ⟨j, q⟩
  change inner Complex
      (((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap
        (OperatorMatrix.matrixUnit bH i j)) (bK q)) (bK p) =
      (∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a))) (i, p) (j, q)
  calc
    inner Complex
        (((finiteKrausFamilyOfChoiVectors bH bK v).inducedMap
          (OperatorMatrix.matrixUnit bH i j)) (bK q)) (bK p)
        = ∑ a : Fin m,
            inner Complex
              (((krausOperatorOfChoiVector bH bK (v a)).comp
                ((OperatorMatrix.matrixUnit bH i j).comp
                  (LinearMap.adjoint (krausOperatorOfChoiVector bH bK (v a))))) (bK q))
              (bK p) := by
          rw [FiniteKrausFamily.inducedMap_apply]
          simp only [finiteKrausFamilyOfChoiVectors, LinearMap.sum_apply, sum_inner]
    _ = ∑ a : Fin m, v a (i, p) * star (v a (j, q)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact krausOperatorOfChoiVector_matrixUnit_apply_inner bH bK (v a) i j p q
    _ = (∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a))) (i, p) (j, q) := by
          rw [Matrix.sum_apply]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Matrix.vecMulVec_apply, Pi.star_apply]

/--
A positive semidefinite project-local Choi matrix yields a finite Kraus family
whose induced operator-space map is the original map.
-/
theorem exists_finiteKrausFamily_of_choiMatrix_posSemidef {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (hchoi : (choiMatrix Φ bH bK).PosSemidef) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.inducedMap = Φ := by
  classical
  rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hchoi) with ⟨m, v, hv⟩
  let R : FiniteKrausFamily (Fin m) H K := finiteKrausFamilyOfChoiVectors bH bK v
  refine ⟨m, R, ?_⟩
  exact choiMatrix_ext R.inducedMap Φ bH bK (by
    calc
      choiMatrix R.inducedMap bH bK
          = ∑ a : Fin m, Matrix.vecMulVec (v a) (star (v a)) := by
            simpa [R] using choiMatrix_finiteKrausFamilyOfChoiVectors_inducedMap bH bK v
      _ = choiMatrix Φ bH bK := hv.symm)

/--
Standard-basis wrapper for finite-dimensional systems.
-/
theorem exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hchoi : (stdChoiMatrix Φ).PosSemidef) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.inducedMap = Φ := by
  exact exists_finiteKrausFamily_of_choiMatrix_posSemidef Φ
    (stdOrthonormalBasis Complex H) (stdOrthonormalBasis Complex K) hchoi

namespace QuantumChannel

/--
Every project quantum channel admits a complete finite Kraus representation
whose induced operator-space map is the channel map.
-/
theorem exists_finiteKrausFamily_representation (Φ : QuantumChannel H K) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.Complete ∧ R.inducedMap = Φ.toLinearMap := by
  classical
  rcases exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef Φ.toLinearMap
      (stdChoiMatrix_posSemidef_of_completelyPositive Φ.toLinearMap Φ.completely_positive) with
    ⟨m, R, hRmap⟩
  refine ⟨m, R, ?_, hRmap⟩
  apply FiniteKrausFamily.complete_of_inducedMap_trace_preserving
  intro A
  rw [hRmap]
  simpa using Φ.trace_map A

end QuantumChannel

end

end Semantics
end QEC

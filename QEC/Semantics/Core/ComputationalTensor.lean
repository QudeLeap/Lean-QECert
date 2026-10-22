import QEC.Semantics.Core.Definitions

/-!
# Computational coordinates of a literal three-factor tensor product

This is the basis-preserving transport from `H tensor (H tensor H)` to
three computational labels. Transporting the literal tensor product of
linear maps gives its matrix coefficients as a product of three entries.
-/

noncomputable section

namespace QEC.Semantics.ComputationalTensor

open scoped TensorProduct

variable (A B : Type) [Fintype A] [Fintype B]

def tripleBasis : OrthonormalBasis (A × A × A) Complex
    (EuclideanSpace Complex A ⊗[Complex]
      (EuclideanSpace Complex A ⊗[Complex] EuclideanSpace Complex A)) :=
  (EuclideanSpace.basisFun A Complex).tensorProduct
    ((EuclideanSpace.basisFun A Complex).tensorProduct (EuclideanSpace.basisFun A Complex))

/-- The transport is fixed by the actual tensor-product computational basis. -/
def tripleTransport : UnitaryTransport
    (EuclideanSpace Complex A ⊗[Complex]
      (EuclideanSpace Complex A ⊗[Complex] EuclideanSpace Complex A))
    (EuclideanSpace Complex (A × A × A)) := by
  let U := (tripleBasis A).equiv (EuclideanSpace.basisFun (A × A × A) Complex) (Equiv.refl _)
  exact ⟨U.toLinearEquiv, U.inner_map_map⟩

theorem tripleTransport_basis (a : A × A × A) :
    tripleTransport A (tripleBasis A a) = EuclideanSpace.basisFun _ Complex a :=
  OrthonormalBasis.equiv_apply_basis _ _ _ _

/-- Arbitrary pure tensors, not just basis tensors, have the expected product amplitudes. -/
theorem tripleTransport_tmul (x y z : EuclideanSpace Complex A) (a : A × A × A) :
    tripleTransport A (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z)) a = x a.1 * y a.2.1 * z a.2.2 := by
  calc
    _ = inner Complex (EuclideanSpace.basisFun _ Complex a)
        (tripleTransport A (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z))) :=
      (EuclideanSpace.basisFun_inner _ _ _ _).symm
    _ = inner Complex (tripleBasis A a) (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z)) := by
      rw [← tripleTransport_basis, (tripleTransport A).map_inner]
    _ = _ := by
      simp only [tripleBasis, OrthonormalBasis.tensorProduct_apply', TensorProduct.inner_tmul,
        EuclideanSpace.basisFun_inner]
      ring

/-- The literal three-fold tensor product of a map, expressed in computational coordinates. -/
def tripleMap (f : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B) :
    EuclideanSpace Complex (A × A × A) →ₗ[Complex] EuclideanSpace Complex (B × B × B) :=
  (tripleTransport B).toLinearEquiv.toLinearMap.comp
    ((TensorProduct.map f (TensorProduct.map f f)).comp
      (tripleTransport A).toLinearEquiv.symm.toLinearMap)

theorem tripleMap_basis_apply
    (f : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B)
    (a : A × A × A) (b : B × B × B) :
    tripleMap A B f (EuclideanSpace.basisFun _ Complex a) b =
      f (EuclideanSpace.basisFun _ Complex a.1) b.1 *
        f (EuclideanSpace.basisFun _ Complex a.2.1) b.2.1 *
        f (EuclideanSpace.basisFun _ Complex a.2.2) b.2.2 := by
  have hinv : (tripleTransport A).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex a) =
      tripleBasis A a := by
    apply (tripleTransport A).toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, tripleTransport_basis]
  change tripleTransport B (TensorProduct.map f (TensorProduct.map f f)
    ((tripleTransport A).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex a))) b = _
  rw [hinv]
  simp only [tripleBasis, OrthonormalBasis.tensorProduct_apply', TensorProduct.map_tmul]
  exact tripleTransport_tmul B _ _ _ b

end QEC.Semantics.ComputationalTensor

import QEC.Semantics.Core.Definitions

/-!
# Computational-basis embeddings

An injective label map is extended by the explicit finite basis sum. Its
orthonormal images prove isometry; composition and compression are derived
from the same map, not supplied as witnesses.
-/

noncomputable section

namespace QEC.Semantics.ComputationalEmbedding

open scoped BigOperators

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

/-- Extend an actual injective label map by its computational-basis action. -/
def linearMap (e : A ↪ B) : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B where
  toFun psi := ∑ a, psi a • EuclideanSpace.basisFun B Complex (e a)
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]

theorem linearMap_basis (e : A ↪ B) (a : A) :
    linearMap e (EuclideanSpace.basisFun A Complex a) = EuclideanSpace.basisFun B Complex (e a) := by
  classical
  change (∑ b, EuclideanSpace.basisFun A Complex a b •
    EuclideanSpace.basisFun B Complex (e b)) = _
  simp [EuclideanSpace.basisFun_apply]

theorem linearMap_inner (e : A ↪ B) (psi chi : EuclideanSpace Complex A) :
    inner Complex (linearMap e psi) (linearMap e chi) = inner Complex psi chi := by
  have ho : Orthonormal Complex (fun a : A => EuclideanSpace.basisFun B Complex (e a)) :=
    (EuclideanSpace.basisFun B Complex).orthonormal.comp e e.injective
  change inner Complex (∑ a, psi a • EuclideanSpace.basisFun B Complex (e a))
    (∑ a, chi a • EuclideanSpace.basisFun B Complex (e a)) = _
  rw [ho.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]

/-- The explicitly constructed basis extension is an isometry. -/
def isometry (e : A ↪ B) : EuclideanSpace Complex A →ₗᵢ[Complex] EuclideanSpace Complex B :=
  (linearMap e).isometryOfInner (linearMap_inner e)

theorem isometry_basis (e : A ↪ B) (a : A) :
    isometry e (EuclideanSpace.basisFun A Complex a) = EuclideanSpace.basisFun B Complex (e a) :=
  linearMap_basis e a

theorem linearMap_comp (e : A ↪ B) (f : B ↪ C) :
    linearMap (e.trans f) = (linearMap f).comp (linearMap e) := by
  apply (EuclideanSpace.basisFun A Complex).toBasis.ext
  intro a
  change linearMap (e.trans f) (EuclideanSpace.basisFun A Complex a) =
    linearMap f (linearMap e (EuclideanSpace.basisFun A Complex a))
  simp only [linearMap_basis, Function.Embedding.trans_apply]

/-- Compression of an arbitrary ambient operator through the explicit embedding. -/
def compress (e : A ↪ B) (E : Operator (EuclideanSpace Complex B)) :
    Operator (EuclideanSpace Complex A) :=
  (LinearMap.adjoint (linearMap e)).comp (E.comp (linearMap e))

theorem compress_inner (e : A ↪ B) (E : Operator (EuclideanSpace Complex B))
    (x y : EuclideanSpace Complex A) :
    inner Complex x (compress e E y) = inner Complex (linearMap e x) (E (linearMap e y)) := by
  change inner Complex x (LinearMap.adjoint (linearMap e) (E (linearMap e y))) = _
  rw [LinearMap.adjoint_inner_right]

theorem compress_basis_inner (e : A ↪ B) (E : Operator (EuclideanSpace Complex B))
    (a b : A) :
    inner Complex (EuclideanSpace.basisFun A Complex a)
        (compress e E (EuclideanSpace.basisFun A Complex b)) =
      inner Complex (EuclideanSpace.basisFun B Complex (e a))
        (E (EuclideanSpace.basisFun B Complex (e b))) := by
  rw [compress_inner, linearMap_basis, linearMap_basis]

end QEC.Semantics.ComputationalEmbedding

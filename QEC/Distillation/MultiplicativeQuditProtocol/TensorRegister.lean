import QEC.Distillation.MultiplicativeQuditProtocol.Register
import QEC.Semantics.Core.ComputationalTensor

/-!
# Literal three-factor tensor products and the three-tag register

The tags are a coordinate presentation of three independent factors. The
transport below is fixed by the computational basis, and the transported
tensor product of a linear map is characterized by its actual matrix entries.
-/

noncomputable section

namespace QEC.Distillation

open Semantics
open scoped TensorProduct BigOperators

def threeTagEquiv (A : Type) : (A × A × A) ≃ (ThreeCopyTag → A) where
  toFun a tag := match tag with
    | .first => a.1
    | .second => a.2.1
    | .third => a.2.2
  invFun f := (f .first, f .second, f .third)
  left_inv _ := rfl
  right_inv f := by funext tag; cases tag <;> rfl

def threeWordEquiv (F J : Type) :
    ((J → F) × (J → F) × (J → F)) ≃ TaggedThreeCopyRegisterLabel F J :=
  (threeTagEquiv (J → F)).trans (Equiv.curry ThreeCopyTag J F).symm

theorem sum_threeTag {A R : Type} [Fintype A] [AddCommMonoid R]
    (f : (ThreeCopyTag → A) → R) :
    (∑ h, f h) = ∑ a, ∑ b, ∑ c, f (threeTagEquiv A (a, b, c)) := by
  rw [← Fintype.sum_equiv (threeTagEquiv A) (fun t => f (threeTagEquiv A t)) f (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]

variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

/-- A tagged computational ket is exactly the product of its three block kets. -/
theorem taggedBasis_apply_eq_product (u v : TaggedThreeCopyRegisterLabel F J) :
    EuclideanSpace.basisFun _ Complex u v =
      EuclideanSpace.basisFun (J → F) Complex (extractBlock u .first) (extractBlock v .first) *
        EuclideanSpace.basisFun (J → F) Complex (extractBlock u .second) (extractBlock v .second) *
        EuclideanSpace.basisFun (J → F) Complex (extractBlock u .third) (extractBlock v .third) := by
  classical
  have heq : v = u ↔ extractBlock v .first = extractBlock u .first ∧
      extractBlock v .second = extractBlock u .second ∧
      extractBlock v .third = extractBlock u .third := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨h₁, h₂, h₃⟩
      funext x
      rcases x with ⟨tag, j⟩
      cases tag with
      | first => exact congrFun h₁ j
      | second => exact congrFun h₂ j
      | third => exact congrFun h₃ j
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp only [heq]
  split_ifs <;> simp_all

/-- The concrete basis-preserving relabelling of three whole words by their tags. -/
def threeWordTransport : UnitaryTransport
    (EuclideanSpace Complex ((J → F) × (J → F) × (J → F))) (TaggedThreeCopyRegister F J) := by
  let U := (EuclideanSpace.basisFun _ Complex).equiv (EuclideanSpace.basisFun _ Complex)
    (threeWordEquiv F J)
  exact ⟨U.toLinearEquiv, U.inner_map_map⟩

theorem threeWordTransport_basis (a : (J → F) × (J → F) × (J → F)) :
    threeWordTransport F J (EuclideanSpace.basisFun _ Complex a) =
      EuclideanSpace.basisFun _ Complex (threeWordEquiv F J a) :=
  OrthonormalBasis.equiv_apply_basis _ _ _ _

theorem threeWordTransport_apply
    (psi : EuclideanSpace Complex ((J → F) × (J → F) × (J → F)))
    (a : (J → F) × (J → F) × (J → F)) :
    threeWordTransport F J psi (threeWordEquiv F J a) = psi a := by
  calc
    _ = inner Complex (EuclideanSpace.basisFun _ Complex (threeWordEquiv F J a))
      (threeWordTransport F J psi) := (EuclideanSpace.basisFun_inner _ _ _ _).symm
    _ = inner Complex (EuclideanSpace.basisFun _ Complex a) psi := by
      rw [← threeWordTransport_basis, (threeWordTransport F J).map_inner]
    _ = _ := EuclideanSpace.basisFun_inner _ _ _ _

/-- The exact literal tensor product `f tensor (f tensor f)`, in tagged coordinates. -/
def taggedTensorCube (f : ComputationalBasisRegister F J →ₗ[Complex] ComputationalBasisRegister F K) :
    TaggedThreeCopyRegister F J →ₗ[Complex] TaggedThreeCopyRegister F K :=
  (threeWordTransport F K).toLinearEquiv.toLinearMap.comp
    ((ComputationalTensor.tripleMap (J → F) (K → F) f).comp
      (threeWordTransport F J).toLinearEquiv.symm.toLinearMap)

theorem taggedTensorCube_basis_apply
    (f : ComputationalBasisRegister F J →ₗ[Complex] ComputationalBasisRegister F K)
    (u : TaggedThreeCopyRegisterLabel F J) (v : TaggedThreeCopyRegisterLabel F K) :
    taggedTensorCube F J K f (EuclideanSpace.basisFun _ Complex u) v =
      f (EuclideanSpace.basisFun _ Complex (extractBlock u .first)) (extractBlock v .first) *
        f (EuclideanSpace.basisFun _ Complex (extractBlock u .second)) (extractBlock v .second) *
        f (EuclideanSpace.basisFun _ Complex (extractBlock u .third)) (extractBlock v .third) := by
  let a := (threeWordEquiv F J).symm u
  let b := (threeWordEquiv F K).symm v
  have ha : (threeWordTransport F J).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex u) =
      EuclideanSpace.basisFun _ Complex a := by
    apply (threeWordTransport F J).toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, threeWordTransport_basis]
    rw [show threeWordEquiv F J a = u from (threeWordEquiv F J).apply_symm_apply u]
  change threeWordTransport F K (ComputationalTensor.tripleMap _ _ f
    ((threeWordTransport F J).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex u))) v = _
  rw [ha, ← (threeWordEquiv F K).apply_symm_apply v, threeWordTransport_apply]
  exact ComputationalTensor.tripleMap_basis_apply _ _ f a b

end QEC.Distillation

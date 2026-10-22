import QEC.Coding.HypergraphProduct.Parameters
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic

/-!
# Dimension of the Tillich--Zémor hypergraph product

This module proves the Künneth/rank calculation needed for the exact encoded
dimension.  The first lemmas establish the required finite-dimensional tensor
rank facts without assuming a rank formula for a Kronecker matrix.
-/

noncomputable section

namespace QEC.Coding.HypergraphProduct

universe u v

open TensorProduct

/-- The pair of tensor maps that applies `f` in the first factor and `g` in
the second factor. -/
def jointTensorMap
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M]
    [AddCommGroup M'] [Module F M']
    [AddCommGroup N] [Module F N]
    [AddCommGroup N'] [Module F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N') :
    M ⊗[F] N →ₗ[F] (M' ⊗[F] N) × (M ⊗[F] N') :=
  (f.rTensor N).prod (g.lTensor M)

/-- For surjective maps, the simultaneous tensor kernel has dimension equal
to the product of the two ordinary kernel dimensions. -/
theorem finrank_ker_jointTensorMap_of_surjective
    {F : Type u} {M M' N N' : Type v}
    [Field F]
    [AddCommGroup M] [Module F M] [Module.Free F M] [Module.Finite F M]
    [AddCommGroup M'] [Module F M'] [Module.Free F M'] [Module.Finite F M']
    [AddCommGroup N] [Module F N] [Module.Free F N] [Module.Finite F N]
    [AddCommGroup N'] [Module F N'] [Module.Free F N'] [Module.Finite F N']
    (f : M →ₗ[F] M') (g : N →ₗ[F] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Module.finrank F (LinearMap.ker (jointTensorMap f g)) =
      Module.finrank F (LinearMap.ker f) *
        Module.finrank F (LinearMap.ker g) := by
  let A : Submodule F (M ⊗[F] N) := LinearMap.ker (f.rTensor N)
  let B : Submodule F (M ⊗[F] N) := LinearMap.ker (g.lTensor M)
  have hA : A = LinearMap.range ((LinearMap.ker f).subtype.rTensor N) := by
    change LinearMap.ker (f.rTensor N) = _
    exact (Module.Flat.rTensor_exact N f.exact_subtype_ker_map).linearMap_ker_eq
  have hB : B = LinearMap.range ((LinearMap.ker g).subtype.lTensor M) := by
    change LinearMap.ker (g.lTensor M) = _
    exact (Module.Flat.lTensor_exact M g.exact_subtype_ker_map).linearMap_ker_eq
  have hAInjective :
      Function.Injective ((LinearMap.ker f).subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap
      (LinearMap.ker f).subtype (LinearMap.ker f).injective_subtype
  have hBInjective :
      Function.Injective ((LinearMap.ker g).subtype.lTensor M) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (LinearMap.ker g).subtype (LinearMap.ker g).injective_subtype
  have hAfinrank :
      Module.finrank F A =
        Module.finrank F (LinearMap.ker f) * Module.finrank F N := by
    rw [hA, LinearMap.finrank_range_of_inj hAInjective]
    exact Module.finrank_tensorProduct
  have hBfinrank :
      Module.finrank F B =
        Module.finrank F M * Module.finrank F (LinearMap.ker g) := by
    rw [hB, LinearMap.finrank_range_of_inj hBInjective]
    exact Module.finrank_tensorProduct
  have hMapKer := TensorProduct.map_ker
    (hfg := f.exact_subtype_ker_map) (hg := hf)
    (hfg' := g.exact_subtype_ker_map) (hg' := hg)
  have hSup : A ⊔ B = LinearMap.ker (TensorProduct.map f g) := by
    rw [hA, hB, sup_comm]
    exact hMapKer.symm
  have hF := f.finrank_range_add_finrank_ker
  have hG := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hF
  rw [LinearMap.range_eq_top.mpr hg, finrank_top] at hG
  have hMap := (TensorProduct.map f g).finrank_range_add_finrank_ker
  have hMapSurjective : Function.Surjective (TensorProduct.map f g) :=
    TensorProduct.map_surjective hf hg
  rw [LinearMap.range_eq_top.mpr hMapSurjective, finrank_top,
    Module.finrank_tensorProduct, Module.finrank_tensorProduct] at hMap
  have hGrass := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hSup, hAfinrank, hBfinrank] at hGrass
  have hJointKer : LinearMap.ker (jointTensorMap f g) = A ⊓ B := by
    simp [jointTensorMap, A, B, LinearMap.ker_prod]
  rw [hJointKer]
  nlinarith

end QEC.Coding.HypergraphProduct

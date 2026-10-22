import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scalar extension of affine normalization charts

Reusable tensor-product and affine-Spec transport, with both projections.
The supplied algebra equivalence is discharged by actual normalization
comparisons in the original modular-equation consumers.
-/

namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
lemma algEquivRingHom_apply (e : A ≃ₐ[R] B) (x : A) : e.toRingHom x = e x := rfl
lemma algHomRingHom_apply (f : A →ₐ[R] B) (x : A) : f.toRingHom x = f x := rfl
open scoped TensorProduct
section TensorApplications
variable {R₀ S₀ A₀ D₀ : Type} [CommRing R₀] [CommRing S₀] [CommRing A₀] [CommRing D₀]
  [Algebra R₀ S₀] [Algebra R₀ A₀]
def normalizationBaseRingHom (e : S₀ ⊗[R₀] A₀ →+* D₀) : A₀ →+* D₀ where
  toFun x := e ((1 : S₀) ⊗ₜ[R₀] x)
  map_one' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_one
  map_mul' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_mul x y
  map_zero' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_zero
  map_add' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_add x y

lemma normalizationBaseRingHom_apply (e : S₀ ⊗[R₀] A₀ →+* D₀) (x : A₀) :
    normalizationBaseRingHom e x = e ((1 : S₀) ⊗ₜ[R₀] x) := rfl

def normalizationConstantRingHom (e : S₀ ⊗[R₀] A₀ →+* D₀) : S₀ →+* D₀ where
  toFun x := e (x ⊗ₜ[R₀] (1 : A₀))
  map_one' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_one
  map_mul' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_mul x y
  map_zero' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_zero
  map_add' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_add x y

lemma normalizationConstantRingHom_apply (e : S₀ ⊗[R₀] A₀ →+* D₀) (c : S₀) :
    normalizationConstantRingHom e c = e (c ⊗ₜ[R₀] (1 : A₀)) := rfl
end TensorApplications
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

def normalizationTensorSpecIso (e : S ⊗[R] A ≃ₐ[S] B) :
    Spec (.of B) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso R S A).symm

lemma normalizationTensorSpecIso_baseRingProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R S A).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

lemma normalizationTensorSpecIso_scalarProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R S A).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact e.commutes c

end
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

lemma normalizationTensorSpecIso_baseRingHomProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (normalizationBaseRingHom e.toRingHom)) := by
  rw [normalizationTensorSpecIso_baseRingProjection]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

lemma normalizationTensorSpecIso_constantRingHomProjection (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (normalizationConstantRingHom e.toRingHom)) := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R S A).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  rfl
end
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

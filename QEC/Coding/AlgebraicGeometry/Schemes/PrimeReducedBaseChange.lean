import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import QEC.Coding.AlgebraicGeometry.Schemes.PrimeAlgebraFrobenius
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Reducedness after prime-field scalar extension

The tensor of two reduced prime-field algebras is reduced: their actual
Frobenius algebra maps are injective, tensor products over a field preserve
these injections, and the tensor map equals p-power on the tensor algebra.
For schemes, identify actual affine pullbacks with those tensor products,
descend through the pulled-back affine cover and prove geometric reducedness
by its full field-extension and pullback-cone definition.
-/

namespace QEC.Coding.AlgebraicGeometry.PrimeReducedTensor
open QEC.Coding.AlgebraicGeometry.PrimeFrobenius
open scoped TensorProduct
noncomputable section

variable (p : ℕ) [Fact p.Prime]

def primeFrobeniusAlgHom (C : Type*) [CommRing C] [Algebra (ZMod p) C] :
    C →ₐ[ZMod p] C where
  __ := primeAlgebraFrobenius p C
  commutes' := primeAlgebraFrobenius_constant p C

lemma primeFrobeniusAlgHom_injective
    (C : Type*) [CommRing C] [Algebra (ZMod p) C] [IsReduced C] :
    Function.Injective (primeFrobeniusAlgHom p C) := by
  intro x y h
  apply sub_eq_zero.mp
  apply IsReduced.eq_zero _
  refine ⟨p, ?_⟩
  change primeAlgebraFrobenius p C (x - y) = 0
  change primeAlgebraFrobenius p C x = primeAlgebraFrobenius p C y at h
  rw [map_sub, h, sub_self]

lemma isReduced_of_primeFrobeniusAlgHom_injective
    (C : Type*) [CommRing C] [Algebra (ZMod p) C]
    (h : Function.Injective (primeFrobeniusAlgHom p C)) : IsReduced C := by
  apply (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr
  intro x hx
  apply h
  change x ^ p = (0 : C) ^ p
  rw [hx, zero_pow (Fact.out : p.Prime).ne_zero]

lemma primeFrobeniusAlgHom_tensor_eq_map
    (C D : Type*) [CommRing C] [CommRing D]
    [Algebra (ZMod p) C] [Algebra (ZMod p) D] :
    primeFrobeniusAlgHom p (C ⊗[ZMod p] D) =
      Algebra.TensorProduct.map (primeFrobeniusAlgHom p C)
        (primeFrobeniusAlgHom p D) := by
  apply Algebra.TensorProduct.ext'
  intro c d
  change (c ⊗ₜ[ZMod p] d) ^ p = (c ^ p) ⊗ₜ[ZMod p] (d ^ p)
  exact Algebra.TensorProduct.tmul_pow c d p

lemma primeReducedTensor_isReduced
    (C D : Type*) [CommRing C] [CommRing D]
    [Algebra (ZMod p) C] [Algebra (ZMod p) D]
    [IsReduced C] [IsReduced D] : IsReduced (C ⊗[ZMod p] D) := by
  apply isReduced_of_primeFrobeniusAlgHom_injective p
  rw [primeFrobeniusAlgHom_tensor_eq_map]
  change Function.Injective (TensorProduct.map
    (primeFrobeniusAlgHom p C).toLinearMap
    (primeFrobeniusAlgHom p D).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _
    (primeFrobeniusAlgHom_injective p C)
    (primeFrobeniusAlgHom_injective p D)

end
end QEC.Coding.AlgebraicGeometry.PrimeReducedTensor

namespace QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits

lemma primeSpecPullback_isReduced
    (p : ℕ) [Fact p.Prime] (C K : Type) [CommRing C] [Field K]
    [_root_.IsReduced C]
    (f : Spec (.of C) ⟶ Spec (.of (ZMod p)))
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  let := PrimeReducedTensor.primeReducedTensor_isReduced p C K
  exact isReduced_of_isOpenImmersion (pullbackSpecIso (ZMod p) C K).hom

lemma primeFieldPullback_isReduced
    (p : ℕ) [Fact p.Prime] (X : Scheme)
    [_root_.AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of (ZMod p))) (K : Type) [Field K]
    (g : Spec (.of K) ⟶ Spec (.of (ZMod p))) :
    _root_.AlgebraicGeometry.IsReduced (pullback f g) := by
  wlog hX : ∃ R : CommRingCat, X = Spec R generalizing f X
  · let U := X.affineCover.pullback₁ (pullback.fst f g)
    let : ∀ i, _root_.AlgebraicGeometry.IsReduced (U.X i) := fun i => by
      have hAffine := this
      let : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
      let : _root_.AlgebraicGeometry.IsReduced (X.affineCover.X i) :=
        isReduced_of_isOpenImmersion (X.affineCover.f i)
      have h : _root_.AlgebraicGeometry.IsReduced
          (pullback (X.affineCover.f i ≫ f) g) :=
        hAffine (X.affineCover.X i) (X.affineCover.f i ≫ f) ⟨_, rfl⟩
      let := h
      have hChart : _root_.AlgebraicGeometry.IsReduced
          (pullback (X.affineCover.f i) (pullback.fst f g)) :=
        isReduced_of_isOpenImmersion
          (pullbackRightPullbackFstIso f g (X.affineCover.f i)).hom
      let := hChart
      change _root_.AlgebraicGeometry.IsReduced
        (pullback (pullback.fst f g) (X.affineCover.f i))
      exact ObjectProperty.prop_of_iso (P := fun Y : Scheme => _root_.AlgebraicGeometry.IsReduced Y)
        (pullbackSymmetry (pullback.fst f g) (X.affineCover.f i)).symm hChart
    exact _root_.AlgebraicGeometry.IsReduced.of_openCover _ U
  · obtain ⟨R, rfl⟩ := hX
    let : _root_.IsReduced R :=
      (affine_isReduced_iff R).mp (inferInstance : _root_.AlgebraicGeometry.IsReduced (Spec R))
    exact primeSpecPullback_isReduced p R K f g

lemma primeFieldMorphism_geometricallyReduced
    (p : ℕ) [Fact p.Prime] (X : Scheme)
    [_root_.AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of (ZMod p))) : GeometricallyReduced f := by
  constructor
  intro K _ g Z fst snd h
  let := primeFieldPullback_isReduced p X f K g
  exact isReduced_of_isOpenImmersion h.isoPullback.hom

end
end QEC.Coding.AlgebraicGeometry.PrimeReducedBaseChange

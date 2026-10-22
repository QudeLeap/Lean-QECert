import QEC.Coding.ExpanderCodes.LPSOriginalReciprocalSpecialFiber
import QEC.Coding.ExpanderCodes.LPSOriginalSpecialFibreFrobenius
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Reduced special fibre of the original integer model

For every positive level N and prime p not dividing N, the actual special
fibre of the SAME original glued proper model is reduced. Identify each
base-changed affine chart with its actual quotient by p through the tensor
product Spec isomorphism, apply the proved zero/infinity quotient results,
and descend reducedness through the pulled-back original open cover.

This internal arithmetic prerequisite supports the original LPS route in
pinned PK22 main.tex ex:Xpq:484–486 and th:qLDPC:231–238. Normal/smooth
special fibres, global good reduction, Hecke/Weil/LPS spectral bounds and
the full explicit quantum family remain unproved. No scheme reducedness,
good model or comparison hypothesis is supplied at the arithmetic endpoint.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section
open scoped TensorProduct

def quotientPrimeTensorEquiv (C : Type) [CommRing C] (p : ℕ) :
    (C ⧸ Ideal.span {(p : C)}) ≃+* (C ⊗[ℤ] ZMod p) := by
  have hI : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ C) = Ideal.span {(p : C)} := by
    rw [Ideal.map_span,Set.image_singleton,map_natCast]
  exact (Ideal.quotEquivOfEq hI.symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (Ideal.span {(p : ℤ)})).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℤ) (A₁ := C))
        (Int.quotientSpanNatEquivZMod p).toIntAlgEquiv).toRingEquiv)

lemma tensorPrime_isReduced_of_quotient (C : Type) [CommRing C] (p : ℕ)
    [IsReduced (C ⧸ Ideal.span {(p : C)})] : IsReduced (C ⊗[ℤ] ZMod p) := by
  let e := quotientPrimeTensorEquiv C p
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

lemma lpsOriginalPrimePullback_isReduced_of_quotient
    (C : Type) [CommRing C] (p : ℕ) [Fact p.Prime]
    (h : _root_.IsReduced (C ⧸ Ideal.span {(p : C)}))
    (f : Spec (.of C) ⟶ Spec (.of ℤ)) :
    _root_.AlgebraicGeometry.IsReduced (pullback f (lpsOriginalPrimeSpecToInteger p)) := by
  let := h
  let : _root_.IsReduced (C ⊗[ℤ] ZMod p) :=
    QEC.Coding.AlgebraicGeometry.tensorPrime_isReduced_of_quotient C p
  have hf : f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C)) :=
    lpsOriginalIntegerSpecZ_hom_unique C _ _
  let e := (pullback.congrHom hf (rfl : lpsOriginalPrimeSpecToInteger p =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))))) ≪≫ pullbackSpecIso ℤ C (ZMod p)
  exact isReduced_of_isOpenImmersion e.hom

lemma lpsOriginalSpecialFibre_pullbackChart_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (hpN : ¬ p ∣ N) (b : Bool) :
    _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalIntegerNormalGluedChartMap N hN b)
        (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
          (lpsOriginalPrimeSpecToInteger p))) := by
  have h : _root_.AlgebraicGeometry.IsReduced
      (pullback (lpsOriginalIntegerNormalGluedChartMap N hN b ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p)) := by
    cases b with
    | false =>
      exact lpsOriginalPrimePullback_isReduced_of_quotient
        (lpsOriginalIntegerNormalZeroChart N hN) p
        (lpsOriginalNormalZero_specialFiber_reduced N hN p hpN) _
    | true =>
      exact lpsOriginalPrimePullback_isReduced_of_quotient
        (lpsOriginalIntegerNormalInfinityChart N hN) p
        (lpsOriginalNormalInfinity_specialFiber_reduced N hN p hpN) _
  let := h
  exact isReduced_of_isOpenImmersion
    (pullbackRightPullbackFstIso (lpsOriginalIntegerNormalGluedToSpecZ N hN)
      (lpsOriginalPrimeSpecToInteger p) (lpsOriginalIntegerNormalGluedChartMap N hN b)).hom

lemma lpsOriginalSpecialFibre_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (hpN : ¬ p ∣ N) : _root_.AlgebraicGeometry.IsReduced (lpsOriginalSpecialFibre p N hN) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  let U := D.openCover.pullback₁
    (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
  let : ∀ b, _root_.AlgebraicGeometry.IsReduced (U.X b) := fun b => by
    change _root_.AlgebraicGeometry.IsReduced
      (pullback (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
        (lpsOriginalPrimeSpecToInteger p)) (lpsOriginalIntegerNormalGluedChartMap N hN b))
    let := lpsOriginalSpecialFibre_pullbackChart_reduced N hN p hpN b
    exact isReduced_of_isOpenImmersion
      (pullbackSymmetry (pullback.fst (lpsOriginalIntegerNormalGluedToSpecZ N hN)
        (lpsOriginalPrimeSpecToInteger p)) (lpsOriginalIntegerNormalGluedChartMap N hN b)).hom
  exact _root_.AlgebraicGeometry.IsReduced.of_openCover _ U

end
end QEC.Coding.TannerLiftedProduct

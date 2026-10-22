import QEC.Coding.ExpanderCodes.LPSOriginalIntegerFlatModel
import QEC.Coding.ExpanderCodes.LPSOriginalSpecialFibreFrobenius

/-!
# LPSOriginalSpecialFibreFlat

The existing actual original special fibre over every prime field inherits
flatness, surjectivity and local finite presentation by genuine base change
of the proved original integer morphism. Its field spectrum has a point,
so surjectivity supplies an actual point in the special fibre.

This prerequisite supports the original LPS route behind pinned PK22 ex:Xpq,
main.tex:484-486, and th:qLDPC, main.tex:231-238. Nonempty flat fibres may be
singular: smooth/good reduction and its uniformity in the original level,
Hecke=Frobenius+Verschiebung, Weil bounds, the LPS spectrum and the exact
quantum family remain unproved. No smoothness conclusion is assumed.
-/

open CategoryTheory AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalSpecialFibreToPrimeField_flat
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Flat (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  exact Flat.isStableUnderBaseChange.of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback
      (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
    (lpsOriginalIntegerNormalGluedToSpecZ_flat N hN)

lemma lpsOriginalSpecialFibreToPrimeField_surjective
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  exact (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{0})).of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback
      (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
    (lpsOriginalIntegerNormalGluedToSpecZ_surjective N hN)

lemma lpsOriginalSpecialFibreToPrimeField_locallyOfFinitePresentation
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 0 < N) :
    LocallyOfFinitePresentation (lpsOriginalSpecialFibreToPrimeField p N hN) := by
  exact locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback
    (CategoryTheory.IsPullback.of_hasPullback
      (lpsOriginalIntegerNormalGluedToSpecZ N hN) (lpsOriginalPrimeSpecToInteger p))
    (lpsOriginalIntegerNormalGluedToSpecZ_locallyOfFinitePresentation N hN)

lemma lpsOriginalSpecialFibre_nonempty
    (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N) :
    Nonempty (lpsOriginalSpecialFibre p N hN) := by
  let := lpsOriginalSpecialFibreToPrimeField_surjective p N hN
  let y : Spec (.of (ZMod p)) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, _⟩ := Scheme.Hom.surjective (lpsOriginalSpecialFibreToPrimeField p N hN) y
  exact ⟨x⟩

end
end QEC.Coding.TannerLiftedProduct

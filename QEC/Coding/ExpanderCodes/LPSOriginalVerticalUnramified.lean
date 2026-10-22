import QEC.Coding.ExpanderCodes.LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus

/-!
# Original vertical local rings

Every height-one prime of the original integer normal zero chart containing a
rational prime is disjoint from the Gauss localization denominators. Canonical
prime localization identifies its local ring with the corresponding local ring
of the SAME original Gauss normalization. When the prime does not divide the
positive level, the original local ring is formally unramified over Z[X] and
its ramification index is one. The scalar maps are constructed from the original
chart and coefficient maps; no comparison or unramifiedness is assumed.

This internal prerequisite supports the original LPS route in pinned PK22
main.tex ex:Xpq, lines 484–486, and th:qLDPC, lines 231–238. Horizontal branch
geometry, purity, global good reduction, spectral bounds and the full explicit
quantum family remain unproved.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section

def localizedPrimeAtPrimeEquiv
    {C D : Type*} [CommRing C] [CommRing D] [Algebra C D]
    (M : Submonoid C) [IsLocalization M D]
    (q : Ideal C) [q.IsPrime] (hd : Disjoint (M : Set C) (q : Set C)) :
    let Q := q.map (algebraMap C D)
    let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M D q inferInstance hd
    let : Algebra C (Localization.AtPrime Q) :=
      ((algebraMap D (Localization.AtPrime Q)).comp (algebraMap C D)).toAlgebra
    Localization.AtPrime q ≃ₐ[C] Localization.AtPrime Q := by
  let Q := q.map (algebraMap C D)
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M D q inferInstance hd
  let instCQ : Algebra C (Localization.AtPrime Q) :=
    ((algebraMap D (Localization.AtPrime Q)).comp (algebraMap C D)).toAlgebra
  let : SMul C (Localization.AtPrime Q) := instCQ.toSMul
  let instDQ : Algebra D (Localization.AtPrime Q) := inferInstance
  let : SMul D (Localization.AtPrime Q) := instDQ.toSMul
  let : IsScalarTower C D (Localization.AtPrime Q) :=
    .of_algebraMap_eq' rfl
  have hcon : Q.comap (algebraMap C D) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M D inferInstance hd
  let : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime Q) Q
    simpa only [hcon] using h
  exact IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (Localization.AtPrime Q)

lemma unramifiedAt_of_localization_disjoint
    {R C D : Type*} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra C D] [IsScalarTower R C D]
    (M : Submonoid C) [IsLocalization M D] [Algebra.FormallyUnramified R D]
    (q : Ideal C) [q.IsPrime] (hd : Disjoint (M : Set C) (q : Set C)) :
    Algebra.IsUnramifiedAt R q := by
  let Q := q.map (algebraMap C D)
  let : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M D q inferInstance hd
  let instCQ : Algebra C (Localization.AtPrime Q) :=
    ((algebraMap D (Localization.AtPrime Q)).comp (algebraMap C D)).toAlgebra
  let : SMul C (Localization.AtPrime Q) := instCQ.toSMul
  let instDQ : Algebra D (Localization.AtPrime Q) := inferInstance
  let : SMul D (Localization.AtPrime Q) := instDQ.toSMul
  let : IsScalarTower C D (Localization.AtPrime Q) := .of_algebraMap_eq' rfl
  let : IsScalarTower R C (Localization.AtPrime Q) :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change algebraMap D (Localization.AtPrime Q) (algebraMap R D r) =
        algebraMap D (Localization.AtPrime Q) (algebraMap C D (algebraMap R C r))
      rw [IsScalarTower.algebraMap_apply R C D])
  let : Algebra.FormallyUnramified D (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.of_isLocalization Q.primeCompl
  let : Algebra.FormallyUnramified R (Localization.AtPrime Q) :=
    Algebra.FormallyUnramified.comp R D (Localization.AtPrime Q)
  exact Algebra.FormallyUnramified.of_equiv
    ((localizedPrimeAtPrimeEquiv (D := D) M q hd).restrictScalars R).symm

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local notation "D" => integralClosure (LPSOriginalGaussBase p) K
include hN

omit [NeZero N] in
lemma lpsOriginalNormalZero_verticalDenominatorsDisjoint
    (q : Ideal C) [q.IsPrime] (hq : q.height = 1) (hpq : (p : C) ∈ q) :
    Disjoint (Algebra.algebraMapSubmonoid C (lpsOriginalGaussPrime p).primeCompl : Set C)
      (q : Set C) := by
  apply Set.disjoint_left.mpr
  intro x hx hxq
  obtain ⟨f,hf,rfl⟩ := hx
  have hfq : f ∈ q.under (Polynomial ℤ) := hxq
  rw [lpsOriginalNormalZero_heightOne_verticalUnder N hN p q hq hpq] at hfq
  exact hf hfq

lemma lpsOriginalNormalZero_verticalUnramified
    (hpN : ¬ p ∣ N) (q : Ideal C) [q.IsPrime] (hq : q.height = 1)
    (hpq : (p : C) ∈ q) : Algebra.IsUnramifiedAt (Polynomial ℤ) q := by
  let instGK : Algebra (LPSOriginalGaussBase p) K :=
    (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let := lpsOriginalGaussBase_scalarTower N hN p
  let instRD : Algebra (Polynomial ℤ) D :=
    ((algebraMap (LPSOriginalGaussBase p) D).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).toAlgebra
  let : SMul (Polynomial ℤ) D := instRD.toSMul
  let : IsScalarTower (Polynomial ℤ) (LPSOriginalGaussBase p) D :=
    .of_algebraMap_eq' rfl
  let instCD : Algebra C D :=
    (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower (Polynomial ℤ) C D :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro f
      apply Subtype.ext
      exact lpsOriginalGaussBaseToGeneratedField_base N hN p f)
  let M := Algebra.algebraMapSubmonoid C (lpsOriginalGaussPrime p).primeCompl
  let : IsLocalization M D := lpsOriginalIntegerNormalZeroGauss_localization N hN p
  let : Algebra.FormallyUnramified (Polynomial ℤ) (LPSOriginalGaussBase p) :=
    Algebra.FormallyUnramified.of_isLocalization (lpsOriginalGaussPrime p).primeCompl
  let : Algebra.Etale (LPSOriginalGaussBase p) D :=
    lpsOriginalGaussNormalization_etale N hN p hpN
  let : Algebra.FormallyUnramified (Polynomial ℤ) D :=
    Algebra.FormallyUnramified.comp (Polynomial ℤ) (LPSOriginalGaussBase p) D
  exact QEC.Coding.AlgebraicGeometry.unramifiedAt_of_localization_disjoint
    («D» := D) M q (lpsOriginalNormalZero_verticalDenominatorsDisjoint N hN p q hq hpq)

lemma lpsOriginalNormalZero_verticalRamificationIndex_one
    (hpN : ¬ p ∣ N) (q : Ideal C) [q.IsPrime] (hq : q.height = 1)
    (hpq : (p : C) ∈ q) : q.ramificationIdx (Polynomial ℤ) = 1 := by
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := lpsOriginalIntegerNormalAffine_finite N hN
  let := lpsOriginalNormalZero_verticalUnramified N hN p hpN q hq hpq
  exact Ideal.ramificationIdx_eq_one q (Polynomial ℤ)

end
end QEC.Coding.TannerLiftedProduct

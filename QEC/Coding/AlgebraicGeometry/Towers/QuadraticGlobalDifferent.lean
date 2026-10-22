import QEC.Coding.AlgebraicGeometry.Differents.PlaceLocalization
import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrder
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticDifferent

/-!
# The quadratic weak different at a specified global prime

The literal Artin--Schreier calculation is applied after localization at the
contraction of the supplied global prime. The result is transported back to
that same prime, with no selected-prime or global-different premise.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- A normalized quadratic source parameter gives the weak different at
the specified global upper prime. The local place represents the actual
height-one contraction, and field generation is ordinary source data. -/
theorem quadraticLiteral_globalPrime_weakDifferent
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : P.order a = -1 ∨ 0 ≤ P.order a) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) := by
  apply transportedIntegralClosurePrime_weak_formula A B K L P H hvaluationRing J
  intro R hRprime hRlies
  let O := P.valuationRing
  let C := integralClosure O L
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective O L)
  letI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  letI : R.IsPrime := hRprime
  letI : R.LiesOver (IsLocalRing.maximalIdeal O) := hRlies
  have hRne : R ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) R
  let HR : IsDedekindDomain.HeightOneSpectrum C := ⟨R, hRprime, hRne⟩
  exact quadraticLiteral_allPrime_weakDifferent P HR a y hy hdegree hgen ha

/-- The same global weak formula with the lower place constructed from the
supplied contracted prime. No independent place, valuation-ring equality, or
local different hypothesis is required. -/
theorem quadraticLiteral_heightOnePrime_weakDifferent
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) := by
  let P := heightOnePlace (k := F256) (K := K) H
  let O := P.valuationRing
  letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  letI : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : FaithfulSMul O L := Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  letI : Module.IsTorsionFree O (integralClosure O L) := IsIntegralClosure.isTorsionFree O L
  exact quadraticLiteral_globalPrime_weakDifferent A B K L P H
    (heightOnePlace_valuationRing H) J a y hy hdegree hgen ha

/-- The quadratic formula on any actual integral-closure carrier. In a
longer tower this lets the upper carrier remain the integral closure over
the fixed initial base, while the relative different is taken over `B`. -/
theorem quadraticLiteral_integralModel_weakDifferent
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    multiplicity Q.asIdeal (differentIdeal B C) =
      2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  let N := integralClosure B L
  letI : IsDedekindDomain N := integralClosure.isDedekindDomain B K L
  letI : Module.IsTorsionFree B N := IsIntegralClosure.isTorsionFree B L
  let σ : N ≃ₐ[B] C := IsIntegralClosure.equiv B N L C
  let J : IsDedekindDomain.HeightOneSpectrum N :=
    IsDedekindDomain.HeightOneSpectrum.comap σ.toRingHom σ.surjective Q
  letI : J.asIdeal.LiesOver H.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change H.asIdeal = Ideal.comap (algebraMap B N) (Ideal.comap σ.toRingHom Q.asIdeal)
    rw [Ideal.comap_comap]
    rw [show σ.toRingHom.comp (algebraMap B N) = algebraMap B C by
      ext b
      exact σ.commutes b]
    exact (show Q.asIdeal.LiesOver H.asIdeal from inferInstance).over
  have hweak := quadraticLiteral_heightOnePrime_weakDifferent A B K L
    H J.asIdeal a y hy hdegree hgen ha
  have hmap : Ideal.map σ.toRingHom J.asIdeal = Q.asIdeal :=
    Q.asIdeal.map_comap_of_surjective σ.toRingHom σ.surjective
  have he : H.asIdeal.ramificationIdx' J.asIdeal =
      H.asIdeal.ramificationIdx' Q.asIdeal :=
    H.asIdeal.ramificationIdx_comap_eq σ Q.asIdeal
  calc
    multiplicity Q.asIdeal (differentIdeal B C) =
        multiplicity J.asIdeal (differentIdeal B N) := by
      rw [← hmap]
      exact differentIdeal_multiplicity_map_algEquiv_eq B N C σ J.asIdeal
    _ = 2 * (H.asIdeal.ramificationIdx' Q.asIdeal - 1) := by rw [hweak, he]

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

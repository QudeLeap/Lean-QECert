import QEC.Coding.AlgebraicGeometry.Towers.QuadraticGlobalDifferent

/-!
# Regular quadratic steps at a fixed global prime

The unit different of a literal regular Artin--Schreier polynomial yields
ramification index one. Localization and carrier equivalence preserve the
actual prime throughout; no ramification output is an input hypothesis.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- A regular parameter gives index one at the supplied prime of the
actual integral closure, even when the lower ring is not itself local. -/
theorem quadraticLiteral_heightOnePrime_ramificationIdx_eq_one
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : 0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    H.asIdeal.ramificationIdx' J = 1 := by
  let P := heightOnePlace (k := F256) (K := K) H
  let O := P.valuationRing
  letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  letI : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing O := P.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  letI : FaithfulSMul O L := Module.isTorsionFree_iff_faithfulSMul.mp inferInstance
  letI : IsDedekindDomain (integralClosure O L) := integralClosure.isDedekindDomain O K L
  letI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI : Module.IsTorsionFree O (integralClosure O L) := IsIntegralClosure.isTorsionFree O L
  apply transportedIntegralClosurePrime_different_ramification_predicate A B K L P H
    (heightOnePlace_valuationRing H) J (fun _ e => e = 1)
  intro R hRprime hRlies
  letI : R.IsPrime := hRprime
  letI : R.LiesOver (IsLocalRing.maximalIdeal O) := hRlies
  let HR : IsDedekindDomain.HeightOneSpectrum (integralClosure O L) :=
    ⟨R, hRprime, Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field O) R⟩
  exact ramificationIdx_eq_one_of_unit_different
    (K := K) (L := L) (IsLocalRing.maximalIdeal O) HR
    (quadraticLiteral_different_eq_top P a ha y hy hdegree hgen)

/-- The regular calculation on any actual integral-closure carrier. -/
theorem quadraticLiteral_integralModel_ramificationIdx_eq_one
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : 0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    H.asIdeal.ramificationIdx' Q.asIdeal = 1 := by
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
  have h := quadraticLiteral_heightOnePrime_ramificationIdx_eq_one A B K L
    H J.asIdeal a y hy hdegree hgen ha
  have he : H.asIdeal.ramificationIdx' J.asIdeal = H.asIdeal.ramificationIdx' Q.asIdeal :=
    H.asIdeal.ramificationIdx_comap_eq σ Q.asIdeal
  exact he.symm.trans h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

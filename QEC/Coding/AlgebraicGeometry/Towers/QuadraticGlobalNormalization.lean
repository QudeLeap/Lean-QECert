import QEC.Coding.AlgebraicGeometry.Differents.PlaceLocalization
import QEC.Coding.AlgebraicGeometry.Towers.QuadraticNormalization

/-!
# Quadratic parameter corrections at a fixed global prime

The actual residue-square correction is constructed after localization and
returned in the unchanged upper fraction field. Its normalized order is
proved at the original global prime by prime-image order transport.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

/-- A literal quadratic insertion preserves normalized representatives for
every normalized lower parameter at a fixed global upper prime. No selected
place, local different formula, or order compatibility is assumed. -/
theorem quadraticLiteral_heightOnePrime_normalizing_correction
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
    [IsFractionRing (integralClosure B L) L]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (J : IsDedekindDomain.HeightOneSpectrum (integralClosure B L))
    [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (b : K)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      (c = 0 ∨ (heightOnePlace (k := F256) (K := L) J).order c = -1) ∧
      ((heightOnePlace (k := F256) (K := L) J).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) J).order (algebraMap K L b + c ^ 2 + c)) := by
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
  apply transportedIntegralClosurePrime_order_predicate A B K L P H
    (heightOnePlace_valuationRing H) J
    (fun ord => ∃ c : L, (c = 0 ∨ ord c = -1) ∧
      (ord (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ ord (algebraMap K L b + c ^ 2 + c)))
  intro R hRlies
  letI : R.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := hRlies
  exact quadraticLiteral_allPrime_normalizing_correction P R a y hy hdegree hgen ha b hb

/-- The same correction on any actual upper integral-closure carrier,
including an absolute integral model over the fixed initial base. -/
theorem quadraticLiteral_integralModel_normalizing_correction
    (A B C K L : Type*) [CommRing A] [CommRing B] [CommRing C]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    [Finite (heightOnePlace (k := F256) (K := K) H).residueField]
    (Q : IsDedekindDomain.HeightOneSpectrum C) [Q.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a)
    (b : K)
    (hb : (heightOnePlace (k := F256) (K := K) H).order b = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order b) :
    ∃ c : L,
      (c = 0 ∨ (heightOnePlace (k := F256) (K := L) Q).order c = -1) ∧
      ((heightOnePlace (k := F256) (K := L) Q).order (algebraMap K L b + c ^ 2 + c) = -1 ∨
        0 ≤ (heightOnePlace (k := F256) (K := L) Q).order (algebraMap K L b + c ^ 2 + c)) := by
  let N := integralClosure B L
  letI : IsDedekindDomain N := integralClosure.isDedekindDomain B K L
  letI : IsFractionRing N L := integralClosure.isFractionRing_of_finite_extension K L
  letI : Module.IsTorsionFree B N := IsIntegralClosure.isTorsionFree B L
  let σ : N ≃ₐ[B] C := IsIntegralClosure.equiv B N L C
  let J := IsDedekindDomain.HeightOneSpectrum.comap σ.toRingHom σ.surjective Q
  letI : J.asIdeal.LiesOver H.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    change H.asIdeal = Ideal.comap (algebraMap B N) (Ideal.comap σ.toRingHom Q.asIdeal)
    rw [Ideal.comap_comap]
    rw [show σ.toRingHom.comp (algebraMap B N) = algebraMap B C by
      ext b
      exact σ.commutes b]
    exact (show Q.asIdeal.LiesOver H.asIdeal from inferInstance).over
  obtain ⟨c, hc, hcorrected⟩ := quadraticLiteral_heightOnePrime_normalizing_correction
    A B K L H J a y hy hdegree hgen ha b hb
  letI : Algebra N C := σ.toRingHom.toAlgebra
  letI : IsScalarTower N C L := IsScalarTower.of_algebraMap_eq fun x =>
    (IsIntegralClosure.algebraMap_equiv B N L C x).symm
  letI : FaithfulSMul N C := (faithfulSMul_iff_algebraMap_injective N C).mpr σ.injective
  letI : Q.asIdeal.LiesOver J.asIdeal := ⟨rfl⟩
  have hmap : Ideal.map (algebraMap N C) J.asIdeal = Q.asIdeal :=
    Q.asIdeal.map_comap_of_surjective σ.toRingHom σ.surjective
  have horders (x : L) := heightOnePlace_order_eq_of_map_eq (k := F256) J Q hmap x
  refine ⟨c, ?_, ?_⟩
  · simpa only [horders] using hc
  · simpa only [horders] using hcorrected

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

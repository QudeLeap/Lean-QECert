import QEC.Coding.AlgebraicGeometry.Differents.LocalizedPrime
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialLocal
import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrderTransport

/-!
# Descending local weak differents at a specified global prime

A place whose valuation ring is the localization at the contracted prime
supplies the local calculation. The conclusion concerns the original global
prime, using the actual localization map and its preserved multiplicities.
-/

namespace QEC.Coding.AlgebraicGeometry

noncomputable section

/-- A commuting algebra square supplies the missing diagonal scalar tower.
Keeping this proof carrier-generic prevents dependent grid fields from being
normalized inside each local instance declaration. -/
private theorem scalarTower_of_commuting_square
    (R S T U : Type*)
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [Algebra T U] [Algebra S U] [Algebra R U]
    [IsScalarTower R S T] [IsScalarTower S T U]
    [IsScalarTower R T U] :
    IsScalarTower R S U :=
  IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap R U x = algebraMap T U (algebraMap R T x) :=
        IsScalarTower.algebraMap_apply R T U x
      _ = algebraMap T U (algebraMap S T (algebraMap R S x)) := by
        rw [IsScalarTower.algebraMap_apply R S T x]
      _ = algebraMap S U (algebraMap R S x) :=
        (IsScalarTower.algebraMap_apply S T U (algebraMap R S x)).symm

/-- Equal valuation subrings of one ambient ring are ring-equivalent without
dependent elimination on their (potentially non-definitionally-equal)
membership predicates. -/
private def valuationSubringRingEquivOfEq
    {K : Type*} [_root_.Field K]
    (S T : ValuationSubring K) (h : S = T) : S ≃+* T where
  toFun x := ⟨x, by rw [← h]; exact x.property⟩
  invFun x := ⟨x, by rw [h]; exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Transport an algebra structure across equality of two ambient
subrings, while retaining the literal ambient value of every scalar. -/
@[reducible] private noncomputable def transportedSubringAlgebra
    (B K : Type*) [CommRing B] [_root_.Field K]
    (S T : ValuationSubring K) [Algebra B S]
    (h : S = T) : Algebra B T :=
  (((valuationSubringRingEquivOfEq S T h).toRingHom).comp
    (algebraMap B S)).toAlgebra

/-- A localization remains a localization after transporting its target
along equality of ambient subrings. -/
private theorem transportedSubring_isLocalization
    (B K : Type*) [CommRing B] [_root_.Field K]
    (M : Submonoid B) (S T : ValuationSubring K) [Algebra B S]
    [IsLocalization M S] (h : S = T) :
    letI : Algebra B T := transportedSubringAlgebra B K S T h
    IsLocalization M T := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv M
    (valuationSubringRingEquivOfEq S T h)).mp inferInstance

/-- A property of the actual different exponent and ramification index
descends from localization to the same supplied global prime. -/
theorem transportedIntegralClosurePrime_different_ramification_predicate
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*)
    [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra k K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L]
    [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing
      (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L))
    [J.IsPrime] [J.LiesOver H.asIdeal]
    (Φ : ℕ → ℕ → Prop)
    (hlocal : ∀ R : Ideal (integralClosure P.valuationRing L),
      R.IsPrime →
      R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
      Φ (multiplicity R
          (differentIdeal P.valuationRing
            (integralClosure P.valuationRing L)))
        ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R)) :
    Φ (multiplicity J (differentIdeal B (integralClosure B L)))
      (H.asIdeal.ramificationIdx' J) := by
  letI : Algebra B P.valuationRing :=
    transportedSubringAlgebra B K
      (H.valuationSubringAtPrime K) P.valuationRing hvaluationRing
  letI : IsLocalization H.asIdeal.primeCompl P.valuationRing :=
    transportedSubring_isLocalization B K H.asIdeal.primeCompl
      (H.valuationSubringAtPrime K) P.valuationRing hvaluationRing
  let e : H.valuationSubringAtPrime K ≃+* P.valuationRing :=
    valuationSubringRingEquivOfEq _ _ hvaluationRing
  letI : IsScalarTower B P.valuationRing K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B K x = algebraMap P.valuationRing K
        (e (algebraMap B (H.valuationSubringAtPrime K) x))
      calc
        algebraMap B K x = algebraMap (H.valuationSubringAtPrime K) K
            (algebraMap B (H.valuationSubringAtPrime K) x) :=
          IsScalarTower.algebraMap_apply B (H.valuationSubringAtPrime K) K x
        _ = _ := rfl
  letI : IsScalarTower B P.valuationRing L :=
    scalarTower_of_commuting_square B P.valuationRing K L
  letI : Module.IsTorsionFree B P.valuationRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective (S := P.valuationRing)
        H.asIdeal.primeCompl_le_nonZeroDivisors)
  letI : Module.IsTorsionFree P.valuationRing L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective P.valuationRing L)
  letI : IsDiscreteValuationRing P.valuationRing :=
    P.valuationRing_isDiscreteValuationRing
  let R : Ideal (integralClosure P.valuationRing L) :=
    Ideal.map (localizedIntegralClosureMap B P.valuationRing L) J
  have htransported :=
    localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
      A B P.valuationRing K L H.asIdeal H.ne_bot J
  dsimp only at htransported
  have hRprime : R.IsPrime := by
    simpa only [R] using htransported.1
  have hRlies :
      R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := by
    simpa only [R] using htransported.2.1
  have hramification :
      (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R =
        H.asIdeal.ramificationIdx' J := by
    simpa only [R] using htransported.2.2.1
  have hmultiplicity :
      multiplicity R
          (differentIdeal P.valuationRing
            (integralClosure P.valuationRing L)) =
        multiplicity J (differentIdeal B (integralClosure B L)) := by
    simpa only [R] using htransported.2.2.2
  rw [← hmultiplicity, ← hramification]
  exact hlocal R hRprime hRlies

/-- The weak-different specialization of the same localization transport. -/
theorem transportedIntegralClosurePrime_weak_formula
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra k K] [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (hlocal : ∀ R : Ideal (integralClosure P.valuationRing L),
      R.IsPrime → R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
        multiplicity R (differentIdeal P.valuationRing (integralClosure P.valuationRing L)) =
          2 * ((IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx' R - 1)) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) :=
  transportedIntegralClosurePrime_different_ramification_predicate A B K L P H
    hvaluationRing J (fun d e => d = 2 * (e - 1)) hlocal


/-- A property of the normalized upper order descends from localization to
the same supplied global prime. This transports actual parameter corrections
as elements of the unchanged fraction field, not just different exponents. -/
theorem transportedIntegralClosurePrime_order_predicate
    {k : Type*} [_root_.Field k] [Finite k]
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra k K] [Algebra k L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    (P : GlobalPlace k K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [FaithfulSMul P.valuationRing L]
    [IsDedekindDomain (integralClosure B L)]
    [IsFractionRing (integralClosure B L) L]
    [Module.IsTorsionFree B (integralClosure B L)]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [IsFractionRing (integralClosure P.valuationRing L) L]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (hvaluationRing : H.valuationSubringAtPrime K = P.valuationRing)
    (J : IsDedekindDomain.HeightOneSpectrum (integralClosure B L))
    [J.asIdeal.LiesOver H.asIdeal]
    (Φ : (L → ℤ) → Prop)
    (hlocal : ∀ R : IsDedekindDomain.HeightOneSpectrum (integralClosure P.valuationRing L),
      R.asIdeal.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) →
        Φ (heightOnePlace (k := k) (K := L) R).order) :
    Φ (heightOnePlace (k := k) (K := L) J).order := by
  letI : Algebra B P.valuationRing :=
    transportedSubringAlgebra B K (H.valuationSubringAtPrime K) P.valuationRing hvaluationRing
  letI : IsLocalization H.asIdeal.primeCompl P.valuationRing :=
    transportedSubring_isLocalization B K H.asIdeal.primeCompl
      (H.valuationSubringAtPrime K) P.valuationRing hvaluationRing
  let e : H.valuationSubringAtPrime K ≃+* P.valuationRing :=
    valuationSubringRingEquivOfEq _ _ hvaluationRing
  letI : IsScalarTower B P.valuationRing K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B K x = algebraMap P.valuationRing K
        (e (algebraMap B (H.valuationSubringAtPrime K) x))
      exact IsScalarTower.algebraMap_apply B (H.valuationSubringAtPrime K) K x
  letI : IsScalarTower B P.valuationRing L :=
    scalarTower_of_commuting_square B P.valuationRing K L
  letI : Module.IsTorsionFree B P.valuationRing :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective (S := P.valuationRing) H.asIdeal.primeCompl_le_nonZeroDivisors)
  letI : Module.IsTorsionFree P.valuationRing L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective P.valuationRing L)
  letI : IsDiscreteValuationRing P.valuationRing := P.valuationRing_isDiscreteValuationRing
  let C := integralClosure B L
  let Cm := integralClosure P.valuationRing L
  let φ : C →+* Cm := localizedIntegralClosureMap B P.valuationRing L
  letI : Algebra C Cm := φ.toAlgebra
  letI : IsScalarTower C Cm L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul C Cm := (faithfulSMul_iff_algebraMap_injective C Cm).mpr (by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Cm => (z : L)) h))
  let R : Ideal Cm := Ideal.map φ J.asIdeal
  have ht := localizedIntegralClosurePrime_ramificationIdx_and_multiplicity_eq
    A B P.valuationRing K L H.asIdeal H.ne_bot J.asIdeal
  dsimp only at ht
  letI : R.IsPrime := ht.1
  letI : R.LiesOver (IsLocalRing.maximalIdeal P.valuationRing) := ht.2.1
  have hRne : R ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field P.valuationRing) R
  let HR : IsDedekindDomain.HeightOneSpectrum Cm := ⟨R, inferInstance, hRne⟩
  letI : HR.asIdeal.LiesOver J.asIdeal := by
    refine Ideal.LiesOver.mk ?_
    apply J.isMaximal.eq_of_le
    · exact (show (Ideal.comap (algebraMap C Cm) R).IsPrime from inferInstance).ne_top
    · exact Ideal.le_comap_map
  have horders : (heightOnePlace (k := k) (K := L) J).order =
      (heightOnePlace (k := k) (K := L) HR).order := by
    funext x
    exact heightOnePlace_order_eq_of_map_eq J HR rfl x
  rw [horders]
  exact hlocal HR inferInstance

end

end QEC.Coding.AlgebraicGeometry

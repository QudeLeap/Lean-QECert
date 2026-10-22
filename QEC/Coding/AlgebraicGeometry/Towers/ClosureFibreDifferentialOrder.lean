import QEC.Coding.AlgebraicGeometry.Towers.WBaseDifferentialOrder
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialPlaceTransport
import QEC.Coding.AlgebraicGeometry.Towers.ClosureFibreDifferent

/-!
# Actual dz orders at both source normal-closure fibres

The source's common indices alpha and beta are used at their actual primes.
The rational w-base orders 14 and -16 combine with the proved chain formula,
giving respectively 16 alpha - 2 and -14 beta - 2.
-/

open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
  fibreDifferent_baseAlgebra fibreDifferent_baseFraction fibreDifferent_baseFaithful
  fibreDifferent_baseDVR fibreDifferent_ambientAlgebra fibreDifferent_baseTower
  fibreDifferent_ambientTorsionFree

set_option maxHeartbeats 1000000 in
theorem sourceClosureWZero_dz_order (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    differentialOrder (sourceGaloisWZeroPlaceOfPrime m P)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
        16 * (sourceGaloisWZeroRamificationIndex m : ℤ) - 2 := by
  let B := sourceGaloisWClosureZeroPlace m
  let A := B.valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWZeroUpperHeightOne m P
  have h := sourceClosureW_integralModel_differentialGeneratorOrder m A Q
  have hlow := differentialGenerator_order_eq_of_order_eq
    (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A)) B
    (B.heightOne_valuationRing_order (Q.under A))
  have hb := sourceClosureWBase_dz_order_zero_fibre m B
    (sourceGaloisWClosureZeroPlace_order_generator m)
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hlow, hb, hp] at h
  have he : (IsLocalRing.maximalIdeal A).ramificationIdx' Q.asIdeal =
      sourceGaloisWZeroRamificationIndex m :=
    (sourceGaloisWZeroRamificationIndex_eq_prime m P).symm
  rw [he] at h
  change differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
    functionFieldDifferentialGenerator functionFieldDifferentialGenerator_ne_zero = _
  rw [h]
  ring

set_option maxHeartbeats 1000000 in
theorem sourceClosureWInfinity_dz_order (m : ℕ) (P : SourceGaloisWInfinityPrime m) :
    differentialOrder (sourceGaloisWInfinityPlaceOfPrime m P)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
        -14 * (sourceGaloisWInfinityRamificationIndex m : ℤ) - 2 := by
  let B := sourceGaloisWClosureInfinityPlace m
  let A := B.valuationRing
  let Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)) :=
    sourceGaloisWInfinityUpperHeightOne m P
  have h := sourceClosureW_integralModel_differentialGeneratorOrder m A Q
  have hlow := differentialGenerator_order_eq_of_order_eq
    (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A)) B
    (B.heightOne_valuationRing_order (Q.under A))
  have hb := sourceClosureWBase_dz_order_infinity_fibre m B
    (sourceGaloisWClosureInfinityPlace_order_generator m)
  have hp : (Q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Q.under A).isMaximal
  rw [hlow, hb, hp] at h
  have he : (IsLocalRing.maximalIdeal A).ramificationIdx' Q.asIdeal =
      sourceGaloisWInfinityRamificationIndex m :=
    (sourceGaloisWInfinityRamificationIndex_eq_prime m P).symm
  rw [he] at h
  change differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
    functionFieldDifferentialGenerator functionFieldDifferentialGenerator_ne_zero = _
  rw [h]
  ring

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

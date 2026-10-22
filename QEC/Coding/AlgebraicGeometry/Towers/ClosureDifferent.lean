import QEC.Coding.AlgebraicGeometry.Towers.ClosureRefinement
import QEC.Coding.AlgebraicGeometry.Towers.RefinementEndpoints

/-!
# The different of the actual source normal closure over k(w)

The whole w-rooted chain computes the different at every supplied prime of
an actual integral closure over a DVR with fraction field `k(w)`. The fixed
ambient-place model is transported to that very prime before its endpoint
different is read; no compatibility of intermediate places is assumed.
-/

open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]

local instance closureDifferent_modelDedekind :
    IsDedekindDomain (integralClosure A (SourceGaloisClosureField m)) :=
  integralClosure.isDedekindDomain A (sourceClosureWBase m) (SourceGaloisClosureField m)

local instance closureDifferent_modelFinite :
    Module.Finite A (integralClosure A (SourceGaloisClosureField m)) :=
  IsIntegralClosure.finite A (sourceClosureWBase m) (SourceGaloisClosureField m)
    (integralClosure A (SourceGaloisClosureField m))

local instance closureDifferent_modelFraction :
    IsFractionRing (integralClosure A (SourceGaloisClosureField m)) (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension (sourceClosureWBase m) (SourceGaloisClosureField m)

local instance closureDifferent_modelTorsionFree :
    Module.IsTorsionFree A (integralClosure A (SourceGaloisClosureField m)) :=
  IsIntegralClosure.isTorsionFree A (SourceGaloisClosureField m)

/-- The all-prime weak-different formula on the actual constructed normal
closure over its literal `k(w)` subfield. Only ordinary DVR/fraction-field
and inclusion structure is supplied; all chain and different facts are proved. -/
theorem sourceClosureW_integralModel_weakDifferent
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m))) :
    multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) =
      2 * ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal - 1) := by
  let E := SourceGaloisClosureField m
  let W := sourceClosureWBase m
  let R := heightOnePlace (k := F256) (K := E) Q
  let B := AmbientPlaceModels.baseRing W R
  let QB := AmbientPlaceModels.prime W R
  have hupper : (heightOnePlace (k := F256) (K := E) Q).order =
      (heightOnePlace (k := F256) (K := E) QB).order :=
    (AmbientPlaceModels.prime_order W R).symm
  have h := NormalizedRefinement.restrictScalars_of_common_ambient_order
    A B W W E Q QB hupper (sourceClosureW_normalizedRefinement m R)
  change NormalizedRefinement A W E Q ⊥ ⊤ at h
  exact NormalizedRefinement.integralClosure_weakDifferent A W E Q h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

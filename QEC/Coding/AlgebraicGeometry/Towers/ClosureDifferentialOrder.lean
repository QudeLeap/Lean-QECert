import QEC.Coding.AlgebraicGeometry.Towers.ClosureDifferent
import QEC.Coding.AlgebraicGeometry.Towers.NormalizedDifferentialRefinement

/-!
# Actual normal-closure differential orders over the w-field

The intermediate w-field is presented over the same rational z as the
existing normal closure. This is only ordinary scalar structure, ensuring
that the differential generator means the same literal dz in both fields.
The source's actual normalized chain then supplies its intrinsic order change.
-/

open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

/-- The existing z-embedding, restricted to its actual intermediate w-field. -/
def sourceClosureWBase_zMap (m : ℕ) : RatFunc F256 →ₐ[F256] sourceClosureWBase m :=
  (sourceGaloisClosureRatFuncEmbedding m).codRestrict (sourceClosureWBase m).toSubalgebra
    (fun r => (SourceGaloisWClosureField m).algebraMap_mem (galoisBaseFieldEquivRatFunc r))

scoped instance sourceClosureWBase_zAlgebra (m : ℕ) :
    Algebra (RatFunc F256) (sourceClosureWBase m) := (sourceClosureWBase_zMap m).toRingHom.toAlgebra

scoped instance sourceClosureWBase_zConstantTower (m : ℕ) :
    IsScalarTower F256 (RatFunc F256) (sourceClosureWBase m) := by
  refine @IsScalarTower.of_algebraMap_eq' F256 (RatFunc F256) (sourceClosureWBase m)
    _ _ _ _ (sourceClosureWBase_zAlgebra m) (sourceClosureWBase m).algebra' ?_
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F256 (RatFunc F256) (SourceGaloisClosureField m) c

scoped instance sourceClosureWBase_zAmbientTower (m : ℕ) :
    IsScalarTower (RatFunc F256) (sourceClosureWBase m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl

scoped instance sourceClosureWBase_zFinite (m : ℕ) :
    FiniteDimensional (RatFunc F256) (sourceClosureWBase m) := by
  letI : Module.IsTorsionFree (sourceClosureWBase m) (SourceGaloisClosureField m) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap (sourceClosureWBase m) (SourceGaloisClosureField m)).injective
  exact FiniteDimensional.left (RatFunc F256) (sourceClosureWBase m)
    (SourceGaloisClosureField m)

scoped instance sourceClosureWBase_zSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (sourceClosureWBase m) :=
  Algebra.isSeparable_tower_bot_of_isSeparable (RatFunc F256) (sourceClosureWBase m)
    (SourceGaloisClosureField m)

attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree

variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]

/-- The actual intrinsic order of dz in the source normal closure is its
lower order times the actual index, plus the proved weak-different correction. -/
theorem sourceClosureW_integralModel_differentialGeneratorOrder
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m))) :
    differentialOrder (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := SourceGaloisClosureField m))
      functionFieldDifferentialGenerator_ne_zero =
    ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) *
      differentialOrder (heightOnePlace (k := F256) (K := sourceClosureWBase m) (Q.under A))
        (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
        functionFieldDifferentialGenerator_ne_zero +
      2 * (((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) - 1) := by
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
  exact NormalizedRefinement.integralClosure_differentialGeneratorOrder A W E Q h

end

end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

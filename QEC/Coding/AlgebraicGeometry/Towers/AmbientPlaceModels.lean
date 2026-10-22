import QEC.Coding.AlgebraicGeometry.Places.RestrictedIntegralModel
import QEC.Coding.AlgebraicGeometry.Differentials.DifferentialLocal

/-!
# Concrete coordinate-window models under a fixed ambient place

For each finite separating base field, use the valuation ring of the actual
restricted place and its integral closure in the unchanged ambient field.
The selected height-one centre has the original ambient order. No
ramification, different, or normalized-chain conclusion is part of this
construction.
-/

namespace QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

noncomputable section

variable {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (F : Type*) [Field F] [Algebra k F] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace k E)

/-- The actual valuation ring of the normalized restricted place. -/
def baseRing : ValuationSubring F := (Q.restrict (F := F)).valuationRing

scoped instance baseDiscreteValuationRing : IsDiscreteValuationRing (baseRing F Q) :=
  (Q.restrict (F := F)).valuationRing_isDiscreteValuationRing

scoped instance baseAmbientAlgebra : Algebra (baseRing F Q) E :=
  ((algebraMap F E).comp (baseRing F Q).subtype).toAlgebra

scoped instance baseAmbientTower : IsScalarTower (baseRing F Q) F E :=
  IsScalarTower.of_algebraMap_eq' rfl

scoped instance baseAmbientTorsionFree : Module.IsTorsionFree (baseRing F Q) E :=
  Module.IsTorsionFree.trans_faithfulSMul (baseRing F Q) F E

/-- The literal integral closure of the restricted valuation ring. -/
abbrev Model := integralClosure (baseRing F Q) E

scoped instance modelDedekind : IsDedekindDomain (Model F Q) :=
  integralClosure.isDedekindDomain (baseRing F Q) F E

scoped instance modelFractionRing : IsFractionRing (Model F Q) E :=
  integralClosure.isFractionRing_of_finite_extension F E

scoped instance modelFinite : Module.Finite (baseRing F Q) (Model F Q) :=
  IsIntegralClosure.finite (baseRing F Q) F E (Model F Q)

scoped instance modelTorsionFree : Module.IsTorsionFree (baseRing F Q) (Model F Q) :=
  IsIntegralClosure.isTorsionFree (baseRing F Q) E

/-- A centre on this concrete integral model recovers the supplied ambient
valuation ring and normalized order. -/
theorem exists_prime :
    ∃ H : IsDedekindDomain.HeightOneSpectrum (Model F Q),
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by
  letI : Algebra (Q.restrict (F := F)).valuationRing E := baseAmbientAlgebra F Q
  letI : IsScalarTower (Q.restrict (F := F)).valuationRing F E := baseAmbientTower F Q
  letI : IsDedekindDomain (integralClosure (Q.restrict (F := F)).valuationRing E) :=
    modelDedekind F Q
  letI : IsFractionRing (integralClosure (Q.restrict (F := F)).valuationRing E) E :=
    modelFractionRing F Q
  exact Q.exists_restrictedIntegralClosure_prime (F := F)

/-- One actual height-one centre for the fixed ambient place. -/
def prime : IsDedekindDomain.HeightOneSpectrum (Model F Q) :=
  Classical.choose (exists_prime F Q)

theorem prime_order : (heightOnePlace (k := k) (K := E) (prime F Q)).order = Q.order :=
  (Classical.choose_spec (exists_prime F Q)).2

omit [FiniteDimensional F E] in
theorem baseResidueFieldFinite [Finite Q.residueField] :
    Finite (IsLocalRing.ResidueField (baseRing F Q)) :=
  Q.restrict_finite_residueField (F := F)

end

end QEC.Coding.AlgebraicGeometry.AmbientPlaceModels

import QEC.Coding.AlgebraicGeometry.Places.HeightOneOrder
import QEC.Coding.AlgebraicGeometry.Places.HeightOneQuotientResidue
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Integral models and prime contractions in a fixed finite ambient field

The source pyramid and its conjugate composita are intermediate fields in a
single finite separable ambient field. Their integral models are closures of
the same initial DVR. Every prime below is the contraction of one supplied
ambient prime; the inclusion maps are induced by literal field inclusions.
-/

open IntermediateField

namespace QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

noncomputable section

attribute [local instance 2500] Algebra.toSMul Algebra.toModule

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The actual integral model of an intermediate field. -/
abbrev Model (K : IntermediateField F E) := integralClosure A K

local notation "C" => Model A F E

scoped instance fieldTorsionFree (K : IntermediateField F E) : Module.IsTorsionFree A K :=
  Module.IsTorsionFree.trans_faithfulSMul A F K

scoped instance modelDedekind (K : IntermediateField F E) : IsDedekindDomain (C K) :=
  integralClosure.isDedekindDomain A F K

scoped instance modelFractionRing (K : IntermediateField F E) : IsFractionRing (C K) K :=
  integralClosure.isFractionRing_of_finite_extension F K

scoped instance modelFinite (K : IntermediateField F E) : Module.Finite A (C K) :=
  IsIntegralClosure.finite A F K (C K)

scoped instance modelTorsionFree (K : IntermediateField F E) : Module.IsTorsionFree A (C K) :=
  IsIntegralClosure.isTorsionFree A K

/-- The inclusion between integral models is the restriction of the literal
field inclusion, not an arbitrary carrier equivalence. -/
def inclusion {K L : IntermediateField F E} (h : K ≤ L) : C K →ₐ[A] C L :=
  ((IntermediateField.inclusion h).restrictScalars A).mapIntegralClosure

scoped instance fieldAlgebra (K L : IntermediateField F E) [h : Fact (K ≤ L)] :
    Algebra K L := (IntermediateField.inclusion h.out).toRingHom.toAlgebra

scoped instance fieldBaseTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl

scoped instance fieldAmbientTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl

scoped instance fieldRingTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl

scoped instance fieldTripleTower (K L M : IntermediateField F E)
    [Fact (K ≤ L)] [Fact (L ≤ M)] [Fact (K ≤ M)] :
    IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl

scoped instance fieldFinite (K L : IntermediateField F E) [Fact (K ≤ L)] :
    FiniteDimensional K L := Module.Finite.of_restrictScalars_finite F K L

scoped instance fieldSeparable (K L : IntermediateField F E) [Fact (K ≤ L)] :
    Algebra.IsSeparable K L := Algebra.isSeparable_tower_top_of_isSeparable F K L

scoped instance modelAlgebra (K L : IntermediateField F E) [h : Fact (K ≤ L)] :
    Algebra (C K) (C L) := (inclusion A F E h.out).toRingHom.toAlgebra

scoped instance modelTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower A (C K) (C L) := IsScalarTower.of_algebraMap_eq' rfl

scoped instance modelTripleTower (K L M : IntermediateField F E)
    [Fact (K ≤ L)] [Fact (L ≤ M)] [Fact (K ≤ M)] :
    IsScalarTower (C K) (C L) (C M) := IsScalarTower.of_algebraMap_eq' rfl

scoped instance modelFieldAlgebra (K L : IntermediateField F E) [Fact (K ≤ L)] :
    Algebra (C K) L := ((algebraMap K L).comp (algebraMap (C K) K)).toAlgebra

scoped instance modelFieldTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower (C K) K L := IsScalarTower.of_algebraMap_eq' rfl

scoped instance modelUpperFieldTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower (C K) (C L) L := IsScalarTower.of_algebraMap_eq' rfl

scoped instance modelRingFieldTower (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsScalarTower A (C K) L := IsScalarTower.of_algebraMap_eq' rfl

scoped instance modelIntegralClosure (K L : IntermediateField F E) [Fact (K ≤ L)] :
    IsIntegralClosure (C L) (C K) L := IsIntegralClosure.tower_top (R := A)

scoped instance modelRelativeFinite (K L : IntermediateField F E) [Fact (K ≤ L)] :
    Module.Finite (C K) (C L) := Module.Finite.of_restrictScalars_finite A (C K) (C L)

scoped instance modelFieldTorsionFree (K L : IntermediateField F E) [Fact (K ≤ L)] :
    Module.IsTorsionFree (C K) L := Module.IsTorsionFree.trans_faithfulSMul (C K) K L

scoped instance modelRelativeTorsionFree (K L : IntermediateField F E) [Fact (K ≤ L)] :
    Module.IsTorsionFree (C K) (C L) := IsIntegralClosure.isTorsionFree (C K) L

abbrev ambientDedekind : IsDedekindDomain (integralClosure A E) :=
  integralClosure.isDedekindDomain A F E

abbrev ambientFinite : Module.Finite A (integralClosure A E) :=
  IsIntegralClosure.finite A F E (integralClosure A E)

variable [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]

def toAmbient (K : IntermediateField F E) : C K →ₐ[A] integralClosure A E :=
  (K.val.restrictScalars A).mapIntegralClosure

scoped instance ambientAlgebra (K : IntermediateField F E) :
    Algebra (C K) (integralClosure A E) := (toAmbient A F E K).toRingHom.toAlgebra

scoped instance ambientTower (K : IntermediateField F E) :
    IsScalarTower A (C K) (integralClosure A E) := IsScalarTower.of_algebraMap_eq' rfl

scoped instance ambientRelativeFinite (K : IntermediateField F E) :
    Module.Finite (C K) (integralClosure A E) :=
  Module.Finite.of_restrictScalars_finite A (C K) (integralClosure A E)

scoped instance ambientFaithful (K : IntermediateField F E) :
    FaithfulSMul (C K) (integralClosure A E) := by
  apply (faithfulSMul_iff_algebraMap_injective (C K) (integralClosure A E)).mpr
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : integralClosure A E => (z : E)) h

/-- Restrict the supplied final prime to the actual intermediate model. -/
def prime (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (K : IntermediateField F E) : IsDedekindDomain.HeightOneSpectrum (C K) :=
  Q.under (C K)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A F]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [IsDedekindDomain (integralClosure A E)] in
/-- Prime contractions in a square are compatible with its literal edges. -/
theorem prime_liesOver
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (K L : IntermediateField F E) [Fact (K ≤ L)] :
    (prime A F E Q L).asIdeal.LiesOver (prime A F E Q K).asIdeal := by
  refine Ideal.LiesOver.mk ?_
  change Ideal.comap (algebraMap (C K) (integralClosure A E)) Q.asIdeal =
    Ideal.comap (algebraMap (C K) (C L))
      (Ideal.comap (algebraMap (C L) (integralClosure A E)) Q.asIdeal)
  rw [Ideal.comap_comap]
  rfl

scoped instance primeLiesOver
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (K L : IntermediateField F E) [Fact (K ≤ L)] :
    (prime A F E Q L).asIdeal.LiesOver (prime A F E Q K).asIdeal :=
  prime_liesOver A F E Q K L

omit [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)] in
/-- Finiteness of the residue field at every intermediate prime follows
from finiteness over the initial DVR, without rebuilding function-field
presentations for each compositum. -/
theorem modelResidueFieldFinite
    {k : Type*} [Field k] [Finite k]
    [Algebra k F] [Algebra k E] [IsScalarTower k F E]
    [Finite (IsLocalRing.ResidueField A)]
    (K : IntermediateField F E) (H : IsDedekindDomain.HeightOneSpectrum (C K)) :
    Finite (heightOnePlace (k := k) (K := K) H).residueField := by
  let m := IsLocalRing.maximalIdeal A
  let I := H.asIdeal
  let P := H.under A
  have hPm : P.asIdeal = m :=
    IsLocalRing.eq_maximalIdeal (P.isPrime.isMaximal P.ne_bot)
  letI : I.LiesOver m := by
    rw [← hPm]
    exact ⟨rfl⟩
  let quotientAlgebra : Algebra (A ⧸ m) ((C K) ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def I m).le
  letI : Algebra (A ⧸ m) ((C K) ⧸ I) := quotientAlgebra
  letI : Module.Finite (A ⧸ m) ((C K) ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ m) ((C K) ⧸ I)
  letI : Finite (A ⧸ m) := inferInstanceAs (Finite (IsLocalRing.ResidueField A))
  letI : Finite ((C K) ⧸ I) := Module.finite_of_finite (A ⧸ m)
  let e : ((C K) ⧸ I) ≃+* (heightOnePlace (k := k) (K := K) H).residueField :=
    H.quotientResidueEquivValuation (K := K)
  exact Finite.of_equiv ((C K) ⧸ I) e.toEquiv

end

end QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels

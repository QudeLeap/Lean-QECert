import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# CharZeroCurveSmoothness

An essentially finite-type DVR over a characteristic-zero field is formally
smooth. Its uniformizer yields an injective flat local polynomial parameter
map; its actual residue tensor fibre is the target residue field. The local
smooth-fibre criterion then proves formal smoothness. All localizations of a
finite-type Dedekind algebra are fields or actual DVRs, proving smoothness of
the entire algebra. These internal results support the original-curve route
behind PK22 ex:Xpq, main.tex:484-486. No smoothness conclusion is assumed.
-/

open scoped TensorProduct
namespace QEC.Coding.AlgebraicGeometry
noncomputable section

lemma dvrUniformizer_transcendental
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) : Transcendental k π := by
  intro h
  exact hπ.not_isUnit ((isAlgebraic_iff_isIntegral.mp h).isUnit hπ.ne_zero)

lemma dvrUniformizer_polynomialMapInjective
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) :
    Function.Injective (Polynomial.aeval π : Polynomial k →ₐ[k] V) := by
  exact transcendental_iff_injective.mp
    (dvrUniformizer_transcendental k V π hπ)


lemma dvrUniformizer_polynomialMapFlat
    (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V) (hπ : Irreducible π) :
    (Polynomial.aeval π : Polynomial k →ₐ[k] V).toRingHom.Flat := by
  let : Algebra (Polynomial k) V := (Polynomial.aeval π).toRingHom.toAlgebra
  change (algebraMap (Polynomial k) V).Flat
  rw [RingHom.flat_algebraMap_iff]
  let : FaithfulSMul (Polynomial k) V :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (dvrUniformizer_polynomialMapInjective k V π hπ)
  infer_instance


section LocalParameter
variable (k V : Type*) [Field k] [CommRing V] [IsDomain V] [Algebra k V]
    (π : V)

def dvrParameterPrime [IsLocalRing V] : Ideal (Polynomial k) :=
  (IsLocalRing.maximalIdeal V).comap (Polynomial.aeval π).toRingHom

local instance dvrParameterPrime_isPrime [IsLocalRing V] :
    (dvrParameterPrime k V π).IsPrime := by
  dsimp [dvrParameterPrime]
  infer_instance

def dvrParameterLocalMap [IsLocalRing V] :
    Localization.AtPrime (dvrParameterPrime k V π) →ₐ[k] V :=
  IsLocalization.liftAlgHom
    (M := (dvrParameterPrime k V π).primeCompl)
    (f := Polynomial.aeval π) fun y => by
      have hy : ¬¬IsUnit (Polynomial.aeval π (y : Polynomial k)) := y.property
      exact Classical.not_not.mp hy

omit [IsDomain V] in
lemma dvrParameterLocalMap_polynomial [IsLocalRing V] (r : Polynomial k) :
    dvrParameterLocalMap k V π
      (algebraMap (Polynomial k)
        (Localization.AtPrime (dvrParameterPrime k V π)) r) =
      Polynomial.aeval π r := by
  simp only [dvrParameterLocalMap,
    IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

lemma dvrParameterLocalMap_injective [IsLocalRing V] (hπ : Irreducible π) :
    Function.Injective (dvrParameterLocalMap k V π) := by
  change Function.Injective (dvrParameterLocalMap k V π).toRingHom
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (dvrParameterPrime k V π).primeCompl
    (dvrParameterLocalMap k V π).toRingHom]
  intro r s
  constructor
  · exact congrArg (dvrParameterLocalMap k V π)
  · intro h
    apply congrArg (algebraMap (Polynomial k)
      (Localization.AtPrime (dvrParameterPrime k V π)))
    apply dvrUniformizer_polynomialMapInjective k V π hπ
    change dvrParameterLocalMap k V π
      (algebraMap (Polynomial k) _ r) = dvrParameterLocalMap k V π
      (algebraMap (Polynomial k) _ s) at h
    simpa only [dvrParameterLocalMap_polynomial] using h

lemma dvrParameterLocalMap_flat [IsLocalRing V] (hπ : Irreducible π) :
    (dvrParameterLocalMap k V π).toRingHom.Flat := by
  let R := Localization.AtPrime (dvrParameterPrime k V π)
  let : Algebra R V := (dvrParameterLocalMap k V π).toRingHom.toAlgebra
  change (algebraMap R V).Flat
  rw [RingHom.flat_algebraMap_iff]
  let : FaithfulSMul R V := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (dvrParameterLocalMap_injective k V π hπ)
  infer_instance

omit [IsDomain V] in
lemma dvrParameterLocalMap_isLocalHom [IsLocalRing V] :
    IsLocalHom (dvrParameterLocalMap k V π).toRingHom := by
  let q := dvrParameterPrime k V π
  let R := Localization.AtPrime q
  let φ := dvrParameterLocalMap k V π
  apply IsLocalHom.mk
  intro x hx
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff R q r s).mpr
  have hs : IsUnit (φ (algebraMap (Polynomial k) R s)) :=
    (IsLocalization.map_units R s).map φ
  have he : φ (IsLocalization.mk' R r s) * φ (algebraMap (Polynomial k) R s) =
      φ (algebraMap (Polynomial k) R r) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  change IsUnit (φ (IsLocalization.mk' R r s)) at hx
  have hr := hx.mul hs
  rw [he, dvrParameterLocalMap_polynomial] at hr
  change ¬¬IsUnit (Polynomial.aeval π r)
  exact fun h => h hr


omit [IsDomain V] in
lemma dvrParameterPrime_eq_spanX [IsLocalRing V] (hπ : Irreducible π) :
    dvrParameterPrime k V π =
      Ideal.span ({Polynomial.X} : Set (Polynomial k)) := by
  have hp : IsLocalRing.residue V π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr hπ.not_isUnit
  have hc : (IsLocalRing.residue V).comp (Polynomial.aeval π).toRingHom =
      (algebraMap k (IsLocalRing.ResidueField V)).comp
        (Polynomial.evalRingHom (0 : k)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.coe_evalRingHom, Polynomial.aeval_C, Polynomial.eval_C]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.coe_evalRingHom, Polynomial.aeval_X, Polynomial.eval_X, hp, map_zero]
  rw [dvrParameterPrime, ← IsLocalRing.ker_residue,
    RingHom.comap_ker, hc, RingHom.ker_comp_of_injective _
      (algebraMap k (IsLocalRing.ResidueField V)).injective]
  simpa using Polynomial.ker_evalRingHom (0 : k)

lemma dvrParameterLocalMap_mapMaximal
    [IsDiscreteValuationRing V] (hπ : Irreducible π) :
    Ideal.map (dvrParameterLocalMap k V π).toRingHom
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (dvrParameterPrime k V π))) =
      IsLocalRing.maximalIdeal V := by
  let q := dvrParameterPrime k V π
  let R := Localization.AtPrime q
  let φ := dvrParameterLocalMap k V π
  have hf : φ.toRingHom.comp (algebraMap (Polynomial k) R) =
      (Polynomial.aeval π).toRingHom := by
    apply RingHom.ext
    intro r
    exact dvrParameterLocalMap_polynomial k V π r
  change Ideal.map φ.toRingHom (IsLocalRing.maximalIdeal R) = _
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := q), Ideal.map_map, hf]
  change Ideal.map (Polynomial.aeval π).toRingHom
    (dvrParameterPrime k V π) = IsLocalRing.maximalIdeal V
  rw [dvrParameterPrime_eq_spanX k V π hπ,
    Ideal.map_span, Set.image_singleton]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ).symm



lemma dvrParameterLocalFibre_isField
    [IsDiscreteValuationRing V] (hπ : Irreducible π) :
    let R := Localization.AtPrime (dvrParameterPrime k V π)
    letI : Algebra R V :=
      (dvrParameterLocalMap k V π).toRingHom.toAlgebra
    IsField (IsLocalRing.ResidueField R ⊗[R] V) := by
  let R := Localization.AtPrime (dvrParameterPrime k V π)
  let : Algebra R V :=
    (dvrParameterLocalMap k V π).toRingHom.toAlgebra
  have hm : Ideal.map (algebraMap R V) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal V :=
    dvrParameterLocalMap_mapMaximal k V π hπ
  let e : (IsLocalRing.ResidueField R ⊗[R] V) ≃+* IsLocalRing.ResidueField V :=
    (Algebra.TensorProduct.comm R (IsLocalRing.ResidueField R) V).toRingEquiv.trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot V
        (IsLocalRing.maximalIdeal R)).symm.toRingEquiv.trans
          (Ideal.quotientEquivAlgOfEq V hm).toRingEquiv)
  exact e.isField (Field.toIsField (IsLocalRing.ResidueField V))



lemma dvr_formallySmoothCharZero
    [CharZero k] [IsDiscreteValuationRing V] [Algebra.EssFiniteType k V] :
    Algebra.FormallySmooth k V := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let R := Localization.AtPrime (dvrParameterPrime k V π)
  let φ := dvrParameterLocalMap k V π
  let : Algebra R V := φ.toRingHom.toAlgebra
  let : SMul k R := Algebra.toSMul
  let : Module k R := Algebra.toModule
  let : SMul k V := Algebra.toSMul
  let : Module k V := Algebra.toModule
  let : SMul R V := Algebra.toSMul
  let : Module R V := Algebra.toModule
  let : IsScalarTower k R V := .of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Module.Flat R V := RingHom.flat_algebraMap_iff.mp
    (dvrParameterLocalMap_flat k V π hπ)
  let : IsLocalHom (algebraMap R V) :=
    dvrParameterLocalMap_isLocalHom k V π
  let : Algebra.EssFiniteType R V := .of_comp k R V
  let P := Algebra.EssFiniteType.subalgebra R V
  let M := Algebra.EssFiniteType.submonoid R V
  let : Algebra.FinitePresentation R P :=
    (Algebra.FinitePresentation.of_finiteType (R := R) (A := P)).mp inferInstance
  let F := IsLocalRing.ResidueField R ⊗[R] V
  let : Field F := (dvrParameterLocalFibre_isField k V π hπ).toField
  let : CharZero (IsLocalRing.ResidueField R) :=
    charZero_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField R)).injective
  let : PerfectField (IsLocalRing.ResidueField R) := inferInstance
  let : Algebra.FormallySmooth (IsLocalRing.ResidueField R) F :=
    Algebra.FormallySmooth.of_perfectField
  let : Algebra.FormallySmooth R V :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := R) (S := V) (P := P) M
  let : Algebra.FormallySmooth (Polynomial k) R :=
    Algebra.FormallySmooth.of_isLocalization
      (dvrParameterPrime k V π).primeCompl
  let : IsScalarTower k (Polynomial k) R := inferInstance
  let : Algebra.FormallySmooth k R := .comp k (Polynomial k) R
  exact Algebra.FormallySmooth.comp k R V

end LocalParameter

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.AlgebraicGeometry
noncomputable section
lemma dedekindFiniteType_smoothCharZero
    (k A : Type*) [Field k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    Algebra.Smooth k A := by
  let : Algebra.FinitePresentation k A :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := A)).mp inferInstance
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp
    (Set.eq_univ_iff_forall.mpr fun p ↦ ?_), inferInstance⟩
  change Algebra.FormallySmooth k (Localization.AtPrime p.asIdeal)
  let V := Localization.AtPrime p.asIdeal
  let : Algebra.EssFiniteType k V := Algebra.EssFiniteType.comp k A V
  by_cases hp : p.asIdeal = ⊥
  · have hf : IsField V := IsLocalRing.isField_iff_maximalIdeal_eq.mpr (by
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      exact (congrArg (Ideal.map (algebraMap A V)) hp).trans (Ideal.map_bot))
    let : Field V := hf.toField
    exact Algebra.FormallySmooth.of_perfectField
  · let : IsDiscreteValuationRing V :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp V
    exact dvr_formallySmoothCharZero k V
end
end QEC.Coding.AlgebraicGeometry

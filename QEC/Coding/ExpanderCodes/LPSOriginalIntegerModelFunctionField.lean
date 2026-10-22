import QEC.Coding.ExpanderCodes.LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# LPSOriginalIntegerModelFunctionField

The actual chart generic points agree on the common Laurent overlap. Their
image is a generic point of the whole glued scheme, which is proved integral.
Every actual local ring is integrally closed. The generic stalk function field
is identified with the same generated original Q(j,jN) by the genuine chart
stalk isomorphism and fraction-field uniqueness.

This internal construction follows the original modular-equation route behind
pinned PK22 ex:Xpq/th:qLDPC. Identification with ALL meromorphic functions on
the original compact analytic quotient, uniform good reduction away the
original level, the geometric Hecke/Frobenius/Weil bound and the exact public
PK22 theorem remain separate unproved obligations. No public node is registered.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

lemma lpsOriginalIntegerNormalSchemeChart_integral
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsIntegral (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      exact inferInstanceAs (IsIntegral (Spec (.of (lpsOriginalIntegerNormalZeroChart N hN))))
  | true =>
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      exact inferInstanceAs (IsIntegral (Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN))))

lemma lpsOriginalIntegerNormalSchemeOverlapMap_generic
    (N : ℕ) (hN : 0<N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    lpsOriginalIntegerNormalSchemeOverlapMap N hN b
      (genericPoint (Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)))) =
      genericPoint (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
  let := lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN b
  exact genericPoint_eq_of_isOpenImmersion _

lemma lpsOriginalIntegerNormalGluedChartMap_generic_agreement
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN false
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN true
    lpsOriginalIntegerNormalGluedChartMap N hN false
      (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false)) =
    lpsOriginalIntegerNormalGluedChartMap N hN true
      (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN true)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN true
  let η := genericPoint (Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)))
  have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN => f η)
    (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
  dsimp only [η] at h
  simpa only [Scheme.Hom.comp_apply,
    lpsOriginalIntegerNormalSchemeOverlapMap_generic] using h

def lpsOriginalIntegerNormalGluedGenericPoint (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedScheme N hN := by
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  exact lpsOriginalIntegerNormalGluedChartMap N hN false
    (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false))

lemma lpsOriginalIntegerNormalGluedChartMap_generic_eq
    (N : ℕ) (hN : 0<N) (b : Bool) :
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    lpsOriginalIntegerNormalGluedChartMap N hN b
      (genericPoint (lpsOriginalIntegerNormalSchemeChart N hN b)) =
      lpsOriginalIntegerNormalGluedGenericPoint N hN := by
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
  cases b with
  | false => rfl
  | true => exact (lpsOriginalIntegerNormalGluedChartMap_generic_agreement N hN).symm

lemma lpsOriginalIntegerNormalGluedGenericPoint_isGeneric
    (N : ℕ) (hN : 0<N) :
    IsGenericPoint (lpsOriginalIntegerNormalGluedGenericPoint N hN) Set.univ := by
  rw [isGenericPoint_iff_specializes]
  intro x
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  obtain ⟨b,y,rfl⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
  have h := ((genericPoint_spec (lpsOriginalIntegerNormalSchemeChart N hN b)).specializes
    (Set.mem_univ y)).map (lpsOriginalIntegerNormalGluedChartMap N hN b).continuous
  rwa [lpsOriginalIntegerNormalGluedChartMap_generic_eq] at h

lemma lpsOriginalIntegerNormalGluedScheme_integral
    (N : ℕ) (hN : 0<N) :
    IsIntegral (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  let : ∀ b : D.openCover.I₀, IsReduced (D.openCover.X b) := fun b => by
    let := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    exact inferInstanceAs (IsReduced (lpsOriginalIntegerNormalSchemeChart N hN b))
  let : IsReduced (lpsOriginalIntegerNormalGluedScheme N hN) :=
    IsReduced.of_openCover _ D.openCover
  let : IrreducibleSpace (lpsOriginalIntegerNormalGluedScheme N hN) :=
    (irreducibleSpace_def _).mpr
      (lpsOriginalIntegerNormalGluedGenericPoint_isGeneric N hN).isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

lemma lpsOriginalNormalAffineStalk_integrallyClosed
    (R : CommRingCat) [IsDomain R] [IsIntegrallyClosed R] (y : Spec R) :
    IsIntegrallyClosed ((Spec R).presheaf.stalk y) := by
  let : y.asIdeal.IsPrime := y.isPrime
  let : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime y.asIdeal)
      y.asIdeal.primeCompl y.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso R y).symm.commRingCatIsoToRingEquiv

lemma lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool)
    (y : lpsOriginalIntegerNormalSchemeChart N hN b) :
    IsIntegrallyClosed ((lpsOriginalIntegerNormalSchemeChart N hN b).presheaf.stalk y) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := lpsOriginalIntegerBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerNormalAffine_integrallyClosed N hN
      exact lpsOriginalNormalAffineStalk_integrallyClosed
        (.of (lpsOriginalIntegerNormalZeroChart N hN)) y
  | true =>
      let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed N hN
      exact lpsOriginalNormalAffineStalk_integrallyClosed
        (.of (lpsOriginalIntegerNormalInfinityChart N hN)) y

lemma lpsOriginalIntegerNormalGluedScheme_stalkIntegrallyClosed
    (N : ℕ) [NeZero N] (hN : 0<N)
    (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    IsIntegrallyClosed ((lpsOriginalIntegerNormalGluedScheme N hN).presheaf.stalk x) := by
  obtain ⟨b,y,rfl⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN b
  let := lpsOriginalIntegerNormalSchemeChart_stalkIntegrallyClosed N hN b y
  exact IsIntegrallyClosed.of_equiv
    (asIso ((lpsOriginalIntegerNormalGluedChartMap N hN b).stalkMap y)).symm.commRingCatIsoToRingEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def lpsOriginalIntegerNormalGluedFunctionFieldEquiv
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    (lpsOriginalIntegerNormalGluedScheme N hN).functionField ≃+*
      lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let R : CommRingCat := .of (lpsOriginalIntegerNormalZeroChart N hN)
  let : IsDomain R := inferInstanceAs (IsDomain (lpsOriginalIntegerNormalZeroChart N hN))
  let i := lpsOriginalIntegerNormalGluedChartMap N hN false
  let η := genericPoint (lpsOriginalIntegerNormalSchemeChart N hN false)
  have hη : i η=genericPoint X := genericPoint_eq_of_isOpenImmersion i
  let e := eqToIso (congrArg X.presheaf.stalk hη.symm) ≪≫ asIso (i.stalkMap η)
  let : IsFractionRing R (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalIntegerNormalAffine_fractionField N hN
  let : Algebra R (Spec R).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec R
  let : IsFractionRing R (Spec R).functionField :=
    functionField_isFractionRing_of_affine R
  exact e.commRingCatIsoToRingEquiv.trans
    (IsFractionRing.ringEquivOfRingEquiv
      (K := (Spec R).functionField)
      (L := lpsOriginalGeneratedFunctionFieldQ N hN) (RingEquiv.refl R))

end
end QEC.Coding.TannerLiftedProduct

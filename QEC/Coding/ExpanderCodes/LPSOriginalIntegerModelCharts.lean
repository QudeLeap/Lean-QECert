import QEC.Coding.ExpanderCodes.LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent

/-!
# LPSOriginalIntegerModelCharts

The reciprocal j coordinate and common Laurent coordinate are faithfully
embedded in the same original generated field. Both integral-closure charts
localize to the actual common Laurent integral closure; their maps preserve
the ambient-field values. These are ring-level constructions for the proper
model, not a good-reduction statement.

This internal construction follows the original modular-equation route behind
pinned PK22 ex:Xpq/th:qLDPC. Identification with ALL meromorphic functions on
the original compact analytic quotient, uniform good reduction away the
original level, the geometric Hecke/Frobenius/Weil bound and the exact public
PK22 theorem remain separate unproved obligations. No public node is registered.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

def lpsOriginalJReciprocalPolynomialMap :
    Polynomial ℚ →+* FractionRing (Polynomial ℚ) :=
  (Polynomial.aeval
    ((algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)⁻¹)).toRingHom

lemma lpsOriginalJReciprocalPolynomialMap_injective :
    Function.Injective lpsOriginalJReciprocalPolynomialMap := by
  apply transcendental_iff_injective.mp
  have hx : Transcendental ℚ
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X) :=
    (transcendental_algebraMap_iff
      (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).mpr
        (Polynomial.transcendental_X ℚ)
  exact fun h => hx (IsAlgebraic.inv_iff.mp h)

def lpsOriginalJFractionInversion :
    FractionRing (Polynomial ℚ) →+* FractionRing (Polynomial ℚ) :=
  IsFractionRing.lift lpsOriginalJReciprocalPolynomialMap_injective

lemma lpsOriginalJFractionInversion_polynomial (P : Polynomial ℚ) :
    lpsOriginalJFractionInversion
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)=
        lpsOriginalJReciprocalPolynomialMap P :=
  IsFractionRing.lift_algebraMap _ P

lemma lpsOriginalJFractionInversion_X :
    lpsOriginalJFractionInversion
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)=
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)⁻¹ := by
  rw [lpsOriginalJFractionInversion_polynomial]
  exact Polynomial.aeval_X _

lemma lpsOriginalJFractionInversion_involutive :
    Function.Involutive lpsOriginalJFractionInversion := by
  have h : lpsOriginalJFractionInversion.comp lpsOriginalJFractionInversion=
      RingHom.id (FractionRing (Polynomial ℚ)) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
    have hp : (lpsOriginalJFractionInversion.comp
        lpsOriginalJFractionInversion).comp
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
        algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) := by
      apply Polynomial.ringHom_ext
      · intro q
        change lpsOriginalJFractionInversion
            (lpsOriginalJFractionInversion
              (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (Polynomial.C q)))=_
        rw [Polynomial.C_eq_algebraMap,
          ←IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (FractionRing (Polynomial ℚ))]
        change lpsOriginalJFractionInversion
            (lpsOriginalJFractionInversion
              (algebraMap ℚ (FractionRing (Polynomial ℚ)) q))=
          algebraMap ℚ (FractionRing (Polynomial ℚ)) q
        rw [RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap]
      · change lpsOriginalJFractionInversion
          (lpsOriginalJFractionInversion
            (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X))=_
        rw [lpsOriginalJFractionInversion_X,map_inv₀,
          lpsOriginalJFractionInversion_X,inv_inv]
    intro P
    exact RingHom.congr_fun hp P
  intro x
  exact RingHom.congr_fun h x

def lpsOriginalIntegerReciprocalBaseFractionMap :
    Polynomial ℤ →+* FractionRing (Polynomial ℚ) :=
  lpsOriginalJFractionInversion.comp lpsOriginalIntegerBaseFractionMap

lemma lpsOriginalIntegerReciprocalBaseFractionMap_injective :
    Function.Injective lpsOriginalIntegerReciprocalBaseFractionMap :=
  lpsOriginalJFractionInversion.injective.comp
    lpsOriginalIntegerBaseFractionMap_injective

lemma lpsOriginalIntegerReciprocalBase_isFractionRing :
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) := by
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let : FaithfulSMul (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      lpsOriginalIntegerReciprocalBaseFractionMap_injective
  apply IsFractionRing.of_field
  intro x
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerBase_isFractionRing
  obtain ⟨a,b,_,h⟩ := IsFractionRing.div_surjective (Polynomial ℤ)
    (lpsOriginalJFractionInversion x)
  change lpsOriginalIntegerBaseFractionMap a /
    lpsOriginalIntegerBaseFractionMap b=lpsOriginalJFractionInversion x at h
  refine ⟨a,b,?_⟩
  change x=lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap a) /
    lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap b)
  rw [←map_div₀, h,lpsOriginalJFractionInversion_involutive]


def lpsOriginalIntegerReciprocalBaseToGeneratedField
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
    lpsOriginalIntegerReciprocalBaseFractionMap

lemma lpsOriginalIntegerReciprocalNormalAffine_finite
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Module.Finite (Polynomial ℤ)
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerReciprocalBase_isFractionRing
  let : IsScalarTower (Polynomial ℤ) (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let : FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  exact IsIntegralClosure.finite (Polynomial ℤ) (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN)
    (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))

lemma lpsOriginalIntegerReciprocalNormalAffine_noetherian
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    IsNoetherianRing
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerReciprocalNormalAffine_finite N hN
  exact IsNoetherianRing.of_finite (Polynomial ℤ) _

lemma lpsOriginalIntegerReciprocalNormalAffine_fractionField
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    IsFractionRing
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerReciprocalBase_isFractionRing
  let : IsScalarTower (Polynomial ℤ) (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let : FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  exact integralClosure.isFractionRing_of_finite_extension (A := Polynomial ℤ)
    (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)

lemma lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    IsIntegrallyClosed
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerReciprocalBase_isFractionRing
  let : IsScalarTower (Polynomial ℤ) (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let : FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (Polynomial ℚ))




lemma lpsOriginalIntegerBaseFractionMap_X_ne_zero :
    lpsOriginalIntegerBaseFractionMap Polynomial.X≠0 :=
  (map_ne_zero_iff _ lpsOriginalIntegerBaseFractionMap_injective).mpr
    Polynomial.X_ne_zero

lemma lpsOriginalIntegerBaseFractionMap_powers_unit
    (s : Submonoid.powers (Polynomial.X : Polynomial ℤ)) :
    IsUnit (lpsOriginalIntegerBaseFractionMap s) := by
  obtain ⟨n,hn⟩ := s.property
  rw [←hn,map_pow]
  exact (IsUnit.mk0 _ lpsOriginalIntegerBaseFractionMap_X_ne_zero).pow n

def lpsOriginalIntegerLaurentBaseFractionMap :
    LaurentPolynomial ℤ →+* FractionRing (Polynomial ℚ) :=
  IsLocalization.lift (S := LaurentPolynomial ℤ)
    (lpsOriginalIntegerBaseFractionMap_powers_unit)

lemma lpsOriginalIntegerLaurentBaseFractionMap_polynomial (P : Polynomial ℤ) :
    lpsOriginalIntegerLaurentBaseFractionMap (Polynomial.toLaurent P)=
      lpsOriginalIntegerBaseFractionMap P :=
  IsLocalization.lift_eq _ P

lemma lpsOriginalIntegerLaurentBaseFractionMap_injective :
    Function.Injective lpsOriginalIntegerLaurentBaseFractionMap := by
  rw [lpsOriginalIntegerLaurentBaseFractionMap,IsLocalization.lift_injective_iff]
  intro P Q
  simp only [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_inj,
    lpsOriginalIntegerBaseFractionMap_injective.eq_iff]

lemma lpsOriginalIntegerLaurentBaseFractionMap_T_one :
    lpsOriginalIntegerLaurentBaseFractionMap (LaurentPolynomial.T 1)=
      lpsOriginalIntegerBaseFractionMap Polynomial.X := by
  rw [←Polynomial.toLaurent_X,lpsOriginalIntegerLaurentBaseFractionMap_polynomial]

lemma lpsOriginalIntegerLaurentBaseFractionMap_T_neg_one :
    lpsOriginalIntegerLaurentBaseFractionMap (LaurentPolynomial.T (-1))=
      (lpsOriginalIntegerBaseFractionMap Polynomial.X)⁻¹ := by
  have h : lpsOriginalIntegerBaseFractionMap Polynomial.X *
      lpsOriginalIntegerLaurentBaseFractionMap (LaurentPolynomial.T (-1))=1 := by
    rw [←lpsOriginalIntegerLaurentBaseFractionMap_T_one,←map_mul,
      ←LaurentPolynomial.T_add]
    simp
  apply (mul_left_cancel₀ lpsOriginalIntegerBaseFractionMap_X_ne_zero)
  rw [h,mul_inv_cancel₀ lpsOriginalIntegerBaseFractionMap_X_ne_zero]

lemma lpsOriginalIntegerLaurentBaseFractionMap_reciprocalPolynomial
    (P : Polynomial ℤ) :
    lpsOriginalIntegerLaurentBaseFractionMap
      (LaurentPolynomial.invert (Polynomial.toLaurent P))=
        lpsOriginalIntegerReciprocalBaseFractionMap P := by
  have h : lpsOriginalIntegerLaurentBaseFractionMap.comp
      ((LaurentPolynomial.invert (R := ℤ)).toRingHom.comp Polynomial.toLaurent)=
        lpsOriginalIntegerReciprocalBaseFractionMap := by
    apply Polynomial.ringHom_ext
    · intro z
      change lpsOriginalIntegerLaurentBaseFractionMap
        (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C z)))=_
      rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C,
        ←Polynomial.toLaurent_C,lpsOriginalIntegerLaurentBaseFractionMap_polynomial]
      change lpsOriginalIntegerBaseFractionMap (Polynomial.C z)=
        lpsOriginalJFractionInversion
          (lpsOriginalIntegerBaseFractionMap (Polynomial.C z))
      simp [lpsOriginalIntegerBaseFractionMap]
    · change lpsOriginalIntegerLaurentBaseFractionMap
        (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X))=_
      rw [Polynomial.toLaurent_X,LaurentPolynomial.invert_T,
        lpsOriginalIntegerLaurentBaseFractionMap_T_neg_one]
      change (lpsOriginalIntegerBaseFractionMap Polynomial.X)⁻¹=
        lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap Polynomial.X)
      simp only [lpsOriginalIntegerBaseFractionMap,RingHom.comp_apply,
        Polynomial.coe_mapRingHom,Polynomial.map_X]
      exact lpsOriginalJFractionInversion_X.symm
  exact RingHom.congr_fun h P

def lpsOriginalIntegerLaurentBaseToGeneratedField
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LaurentPolynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
    lpsOriginalIntegerLaurentBaseFractionMap


lemma lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial
    (N : ℕ) (hN : 0<N) (P : Polynomial ℤ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerLaurentBaseToGeneratedField N hN (Polynomial.toLaurent P)=
      lpsOriginalIntegerBaseToGeneratedField N hN P := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerLaurentBaseFractionMap (Polynomial.toLaurent P))=_
  rw [lpsOriginalIntegerLaurentBaseFractionMap_polynomial]
  rfl

lemma lpsOriginalIntegerLaurentBase_scalarTower
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact .of_algebraMap_eq' (RingHom.ext
    (lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial N hN)).symm

def lpsOriginalIntegerNormalChartToOverlap
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  letI := lpsOriginalIntegerLaurentBase_scalarTower N hN
  exact
    { toFun := fun x => ⟨x.val,x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma lpsOriginalIntegerNormalChartToOverlap_injective
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    Function.Injective (lpsOriginalIntegerNormalChartToOverlap N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  intro x y h
  exact Subtype.ext (congrArg
    (fun z : integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) => z.val) h)

lemma lpsOriginalIntegerNormalOverlap_localization
    (N : ℕ) (hN : 0<N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    let := lpsOriginalIntegerLaurentBase_scalarTower N hN
    let := (lpsOriginalIntegerNormalChartToOverlap N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℤ)
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) Polynomial.X)
      (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerLaurentBase_scalarTower N hN
  let C := integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let D := integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let instCD : Algebra C D := (lpsOriginalIntegerNormalChartToOverlap N hN).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d l => by
      change (c.val*d.val)*l=c.val*(d.val*l)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  have hx : algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
      Polynomial.X≠0 := by
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerBaseFractionMap Polynomial.X)≠0
    exact (map_ne_zero_iff _ (algebraMap (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN)).injective).mpr
        lpsOriginalIntegerBaseFractionMap_X_ne_zero
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) Polynomial.X)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun y hy => by
      obtain ⟨n,rfl⟩ := hy
      exact (IsUnit.mk0 _ hx).pow n)
  exact IsLocalization.Away.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN) (Rf := LaurentPolynomial ℤ)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) Polynomial.X


def lpsOriginalIntegerReciprocalLaurentPolynomialMap :
    Polynomial ℤ →+* LaurentPolynomial ℤ :=
  (LaurentPolynomial.invert (R := ℤ)).toRingHom.comp Polynomial.toLaurent

lemma lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective :
    Function.Injective lpsOriginalIntegerReciprocalLaurentPolynomialMap :=
  (LaurentPolynomial.invert (R := ℤ)).injective.comp Polynomial.toLaurent_injective

lemma lpsOriginalIntegerReciprocalLaurent_isLocalization :
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    IsLocalization.Away (Polynomial.X : Polynomial ℤ) (LaurentPolynomial ℤ) := by
  have hu (b : Submonoid.powers (Polynomial.X : Polynomial ℤ)) :
      IsUnit (Polynomial.toLaurent (b : Polynomial ℤ)) :=
    IsLocalization.map_units (S := LaurentPolynomial ℤ) b
  have hs (z : LaurentPolynomial ℤ) : ∃ p : Polynomial ℤ ×
      Submonoid.powers (Polynomial.X : Polynomial ℤ),
        z*Polynomial.toLaurent (p.2 : Polynomial ℤ)=Polynomial.toLaurent p.1 :=
    IsLocalization.surj (Submonoid.powers (Polynomial.X : Polynomial ℤ)) z
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  refine
    { map_units := fun b => ?_
      surj := fun z => ?_
      exists_of_eq := fun {x y} h => ?_ }
  · change IsUnit (LaurentPolynomial.invert (Polynomial.toLaurent (b : Polynomial ℤ)))
    exact (hu b).map (LaurentPolynomial.invert (R := ℤ)).toRingHom
  · obtain ⟨p,hp⟩ := hs (LaurentPolynomial.invert z)
    refine ⟨p,?_⟩
    change z*LaurentPolynomial.invert (Polynomial.toLaurent (p.2 : Polynomial ℤ))=
      LaurentPolynomial.invert (Polynomial.toLaurent p.1)
    have hh := congrArg (fun w : LaurentPolynomial ℤ => LaurentPolynomial.invert w) hp
    rw [map_mul] at hh
    have hz : LaurentPolynomial.invert (LaurentPolynomial.invert z)=z :=
      LaurentPolynomial.involutive_invert z
    rw [hz] at hh
    exact hh
  · have hxy := lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective h
    refine ⟨1,?_⟩
    simpa only [Submonoid.coe_one,one_mul] using hxy


lemma lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero :
    lpsOriginalIntegerReciprocalBaseFractionMap Polynomial.X≠0 :=
  (map_ne_zero_iff _ lpsOriginalIntegerReciprocalBaseFractionMap_injective).mpr
    Polynomial.X_ne_zero

lemma lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial
    (N : ℕ) (hN : 0<N) (P : Polynomial ℤ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    lpsOriginalIntegerLaurentBaseToGeneratedField N hN
      (lpsOriginalIntegerReciprocalLaurentPolynomialMap P)=
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN P := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerLaurentBaseFractionMap
      (LaurentPolynomial.invert (Polynomial.toLaurent P)))=_
  rw [lpsOriginalIntegerLaurentBaseFractionMap_reciprocalPolynomial]
  rfl

lemma lpsOriginalIntegerReciprocalLaurentBase_scalarTower
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact .of_algebraMap_eq' (RingHom.ext
    (lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial N hN)).symm

def lpsOriginalIntegerReciprocalNormalChartToOverlap
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  letI := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  exact
    { toFun := fun x => ⟨x.val,x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma lpsOriginalIntegerReciprocalNormalChartToOverlap_injective
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    Function.Injective (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  intro x y h
  exact Subtype.ext (congrArg
    (fun z : integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) => z.val) h)

lemma lpsOriginalIntegerReciprocalNormalOverlap_localization
    (N : ℕ) (hN : 0<N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
    let := (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℤ)
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) Polynomial.X)
      (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  let C := integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let D := integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let instCD : Algebra C D := (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d l => by
      change (c.val*d.val)*l=c.val*(d.val*l)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  have hx : algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
      Polynomial.X≠0 := by
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerReciprocalBaseFractionMap Polynomial.X)≠0
    exact (map_ne_zero_iff _ (algebraMap (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN)).injective).mpr
        lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) Polynomial.X)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun y hy => by
      obtain ⟨n,rfl⟩ := hy
      exact (IsUnit.mk0 _ hx).pow n)
  let := lpsOriginalIntegerReciprocalLaurent_isLocalization
  exact IsLocalization.Away.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN) (Rf := LaurentPolynomial ℤ)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) Polynomial.X

end
end QEC.Coding.TannerLiftedProduct

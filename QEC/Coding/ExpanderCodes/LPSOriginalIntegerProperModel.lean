import QEC.Coding.ExpanderCodes.LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# LPSOriginalIntegerProperModel

Two actual normal integer charts are glued along their proved common open
Laurent chart. The resulting scheme maps finitely to the projective j-line:
actual Cartesian chart squares identify each chart preimage. The j-line is
proved proper over SpecZ using genuine valuative extension and uniqueness,
so the constructed finite model is proper over SpecZ at every positive level,
including the original composite levels 16*q^2.

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


abbrev lpsOriginalIntegerNormalZeroChart (N : ℕ) (hN : 0<N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)

abbrev lpsOriginalIntegerNormalInfinityChart (N : ℕ) (hN : 0<N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)

abbrev lpsOriginalIntegerNormalLaurentChart (N : ℕ) (hN : 0<N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)

def lpsOriginalIntegerNormalZeroToLaurent (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalZeroChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact lpsOriginalIntegerNormalChartToOverlap N hN

def lpsOriginalIntegerNormalInfinityToLaurent (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact lpsOriginalIntegerReciprocalNormalChartToOverlap N hN

lemma lpsOriginalIntegerNormalZeroToLaurent_openImmersion
    (N : ℕ) (hN : 0<N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalZeroToLaurent N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerNormalZeroToLaurent N hN).toAlgebra
  let := lpsOriginalIntegerLaurentBase_scalarTower N hN
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalZeroChart N hN) Polynomial.X)
      (lpsOriginalIntegerNormalLaurentChart N hN) :=
    lpsOriginalIntegerNormalOverlap_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalZeroChart N hN) Polynomial.X)

lemma lpsOriginalIntegerNormalInfinityToLaurent_openImmersion
    (N : ℕ) (hN : 0<N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalInfinityToLaurent N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToLaurent N hN).toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X)
      (lpsOriginalIntegerNormalLaurentChart N hN) :=
    lpsOriginalIntegerReciprocalNormalOverlap_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X)


def lpsOriginalIntegerNormalSchemeChart (N : ℕ) (hN : 0<N) : Bool → Scheme
  | false => Spec (.of (lpsOriginalIntegerNormalZeroChart N hN))
  | true => Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN))

def lpsOriginalIntegerNormalSchemeOverlapMap (N : ℕ) (hN : 0<N) (b : Bool) :
    Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerNormalSchemeChart N hN b := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN))
  | true => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN))

lemma lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerNormalSchemeOverlapMap N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroToLaurent_openImmersion N hN
  | true => exact lpsOriginalIntegerNormalInfinityToLaurent_openImmersion N hN

lemma lpsOriginalTwoChartDistinctTripleFalse
    (i j k : Bool) (hij : i≠j) (hik : i≠k) (hjk : j≠k) : False := by
  cases i <;> cases j <;> cases k
  all_goals first | exact hij rfl | exact hik rfl | exact hjk rfl

def lpsOriginalIntegerNormalSchemeGlueDataPrime (N : ℕ) (hN : 0<N) :
    CategoryTheory.GlueData' Scheme where
  J := Bool
  U := lpsOriginalIntegerNormalSchemeChart N hN
  V _ _ _ := Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN))
  f i _ _ := lpsOriginalIntegerNormalSchemeOverlapMap N hN i
  f_mono i _ _ := by
    let := lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN i
    infer_instance
  f_hasPullback i _ _ _ _ := by
    let := lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN i
    infer_instance
  t _ _ _ := 𝟙 _
  t' i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_fac i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_inv _ _ _ := by simp
  cocycle i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)

def lpsOriginalIntegerNormalSchemeGlueData (N : ℕ) (hN : 0<N) :
    Scheme.GlueData := by
  let D := lpsOriginalIntegerNormalSchemeGlueDataPrime N hN
  exact
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D
      f_open := fun i j => by
        change IsOpenImmersion (D.f' i j)
        dsimp [CategoryTheory.GlueData'.f']
        split_ifs with h
        · infer_instance
        · let : IsOpenImmersion (D.f i j h) :=
            lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN i
          infer_instance }

def lpsOriginalIntegerNormalGluedScheme (N : ℕ) (hN : 0<N) : Scheme :=
  (lpsOriginalIntegerNormalSchemeGlueData N hN).glued

def lpsOriginalIntegerNormalGluedChartMap (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  (lpsOriginalIntegerNormalSchemeGlueData N hN).ι b

lemma lpsOriginalIntegerNormalGluedChartMap_openImmersion
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerNormalGluedChartMap N hN b) := by
  exact Scheme.GlueData.ι_isOpenImmersion
    (lpsOriginalIntegerNormalSchemeGlueData N hN) b


lemma lpsOriginalIntegerNormalGluedChartMap_cover
    (N : ℕ) (hN : 0<N) (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalIntegerNormalSchemeChart N hN b),
      lpsOriginalIntegerNormalGluedChartMap N hN b y=x :=
  (lpsOriginalIntegerNormalSchemeGlueData N hN).ι_jointly_surjective x

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGluedOverlap_agreement
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
      lpsOriginalIntegerNormalGluedChartMap N hN false=
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  change lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫ D.ι false =
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫ D.ι true
  have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN false := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN true := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have h := D.glue_condition false true
  rw [hf,hf',ht] at h
  have hh := congrArg (fun f : D.V (false,true) ⟶ D.glued => eqToHom e.symm ≫ f) h.symm
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hh


def lpsOriginalIntegerNormalZeroChartToJLine (N : ℕ) (hN : 0<N) :
    Spec (.of (lpsOriginalIntegerNormalZeroChart N hN)) ⟶
      Spec (.of (Polynomial ℤ)) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalZeroChart N hN)))

def lpsOriginalIntegerNormalInfinityChartToJLine (N : ℕ) (hN : 0<N) :
    Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN)) ⟶
      Spec (.of (Polynomial ℤ)) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalInfinityChart N hN)))

lemma lpsOriginalIntegerNormalZeroChartToJLine_finite
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsFinite (lpsOriginalIntegerNormalZeroChartToJLine N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalZeroChart N hN))))
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (lpsOriginalIntegerNormalAffine_finite N hN)

lemma lpsOriginalIntegerNormalInfinityChartToJLine_finite
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsFinite (lpsOriginalIntegerNormalInfinityChartToJLine N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalInfinityChart N hN))))
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr
    (lpsOriginalIntegerReciprocalNormalAffine_finite N hN)

def lpsOriginalIntegerNormalLaurentChartToJOverlap (N : ℕ) (hN : 0<N) :
    Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      Spec (.of (LaurentPolynomial ℤ)) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial ℤ)
    (lpsOriginalIntegerNormalLaurentChart N hN)))

lemma lpsOriginalIntegerNormalZeroChartToJLine_overlap
    (N : ℕ) (hN : 0<N) :
    Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)) ≫
      lpsOriginalIntegerNormalZeroChartToJLine N hN =
    lpsOriginalIntegerNormalLaurentChartToJOverlap N hN ≫
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  unfold lpsOriginalIntegerNormalZeroChartToJLine
    lpsOriginalIntegerNormalLaurentChartToJOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  apply Subtype.ext
  exact (lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial N hN P).symm

lemma lpsOriginalIntegerNormalInfinityChartToJLine_overlap
    (N : ℕ) (hN : 0<N) :
    Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN)) ≫
      lpsOriginalIntegerNormalInfinityChartToJLine N hN =
    lpsOriginalIntegerNormalLaurentChartToJOverlap N hN ≫
      Spec.map (CommRingCat.ofHom lpsOriginalIntegerReciprocalLaurentPolynomialMap) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  unfold lpsOriginalIntegerNormalInfinityChartToJLine
    lpsOriginalIntegerNormalLaurentChartToJOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  apply Subtype.ext
  exact (lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial N hN P).symm

def lpsOriginalIntegerProjectiveJOverlapMap (b : Bool) :
    Spec (.of (LaurentPolynomial ℤ)) ⟶ Spec (.of (Polynomial ℤ)) := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ))
  | true => exact Spec.map (CommRingCat.ofHom lpsOriginalIntegerReciprocalLaurentPolynomialMap)

lemma lpsOriginalIntegerProjectiveJOverlapMap_openImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerProjectiveJOverlapMap b) := by
  cases b with
  | false =>
      exact IsOpenImmersion.of_isLocalization (R:=Polynomial ℤ) (S:=LaurentPolynomial ℤ) Polynomial.X
  | true =>
      let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
      let := lpsOriginalIntegerReciprocalLaurent_isLocalization
      exact IsOpenImmersion.of_isLocalization (R:=Polynomial ℤ) (S:=LaurentPolynomial ℤ) Polynomial.X

def lpsOriginalIntegerProjectiveJGlueDataPrime : CategoryTheory.GlueData' Scheme where
  J := Bool
  U _ := Spec (.of (Polynomial ℤ))
  V _ _ _ := Spec (.of (LaurentPolynomial ℤ))
  f i _ _ := lpsOriginalIntegerProjectiveJOverlapMap i
  f_mono i _ _ := by
    let := lpsOriginalIntegerProjectiveJOverlapMap_openImmersion i
    infer_instance
  f_hasPullback i _ _ _ _ := by
    let := lpsOriginalIntegerProjectiveJOverlapMap_openImmersion i
    infer_instance
  t _ _ _ := 𝟙 _
  t' i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_fac i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_inv _ _ _ := by simp
  cocycle i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)

def lpsOriginalIntegerProjectiveJGlueData : Scheme.GlueData := by
  let D := lpsOriginalIntegerProjectiveJGlueDataPrime
  exact
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D
      f_open := fun i j => by
        change IsOpenImmersion (D.f' i j)
        dsimp [CategoryTheory.GlueData'.f']
        split_ifs with h
        · infer_instance
        · let : IsOpenImmersion (D.f i j h) :=
            lpsOriginalIntegerProjectiveJOverlapMap_openImmersion i
          infer_instance }

def lpsOriginalIntegerProjectiveJLine : Scheme :=
  lpsOriginalIntegerProjectiveJGlueData.glued

def lpsOriginalIntegerProjectiveJChartMap (b : Bool) :
    Spec (.of (Polynomial ℤ)) ⟶ lpsOriginalIntegerProjectiveJLine :=
  lpsOriginalIntegerProjectiveJGlueData.ι b

lemma lpsOriginalIntegerProjectiveJChartMap_openImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerProjectiveJChartMap b) :=
  Scheme.GlueData.ι_isOpenImmersion lpsOriginalIntegerProjectiveJGlueData b

lemma lpsOriginalIntegerProjectiveJChartMap_cover
    (x : lpsOriginalIntegerProjectiveJLine) :
    ∃ (b : Bool) (y : Spec (.of (Polynomial ℤ))),
      lpsOriginalIntegerProjectiveJChartMap b y=x :=
  lpsOriginalIntegerProjectiveJGlueData.ι_jointly_surjective x

lemma lpsOriginalIntegerNormalSchemeChart_locallyNoetherian
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    IsLocallyNoetherian (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  cases b with
  | false =>
      let := lpsOriginalJFractionEmbeddingQ.toAlgebra
      let := lpsOriginalIntegerBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerNormalAffine_noetherian N hN
      change IsLocallyNoetherian (Spec (.of (lpsOriginalIntegerNormalZeroChart N hN)))
      infer_instance
  | true =>
      let := lpsOriginalJFractionEmbeddingQ.toAlgebra
      let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := lpsOriginalIntegerReciprocalNormalAffine_noetherian N hN
      change IsLocallyNoetherian (Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN)))
      infer_instance

lemma lpsOriginalIntegerNormalGluedScheme_noetherian
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsNoetherian (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  let : ∀ b : D.openCover.I₀, CompactSpace (D.openCover.X b) := fun b => by
    cases b with
    | false => exact Scheme.compactSpace_of_isAffine (Spec (.of (lpsOriginalIntegerNormalZeroChart N hN)))
    | true => exact Scheme.compactSpace_of_isAffine (Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN)))
  let : Finite D.openCover.I₀ := inferInstanceAs (Finite Bool)
  have hc : CompactSpace D.glued := D.openCover.compactSpace
  have hn : IsLocallyNoetherian D.glued :=
    (isLocallyNoetherian_iff_openCover D.openCover).mpr
      (lpsOriginalIntegerNormalSchemeChart_locallyNoetherian N hN)
  exact { toIsLocallyNoetherian := hn, toCompactSpace := hc }

lemma lpsOriginalIntegerProjectiveJLine_noetherian :
    IsNoetherian lpsOriginalIntegerProjectiveJLine := by
  let D := lpsOriginalIntegerProjectiveJGlueData
  let : ∀ b : D.openCover.I₀, CompactSpace (D.openCover.X b) :=
    fun _ => Scheme.compactSpace_of_isAffine (Spec (.of (Polynomial ℤ)))
  let : Finite D.openCover.I₀ := inferInstanceAs (Finite Bool)
  have hc : CompactSpace D.glued := D.openCover.compactSpace
  have hn : IsLocallyNoetherian D.glued :=
    (isLocallyNoetherian_iff_openCover D.openCover).mpr
      (fun _ => inferInstanceAs (IsLocallyNoetherian (Spec (.of (Polynomial ℤ)))))
  exact { toIsLocallyNoetherian := hn, toCompactSpace := hc }

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJOverlap_agreement :
    lpsOriginalIntegerProjectiveJOverlapMap false ≫
      lpsOriginalIntegerProjectiveJChartMap false=
    lpsOriginalIntegerProjectiveJOverlapMap true ≫
      lpsOriginalIntegerProjectiveJChartMap true := by
  let D := lpsOriginalIntegerProjectiveJGlueData
  change lpsOriginalIntegerProjectiveJOverlapMap false ≫ D.ι false =
    lpsOriginalIntegerProjectiveJOverlapMap true ≫ D.ι true
  have e : D.V (false,true)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerProjectiveJOverlapMap false := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerProjectiveJOverlapMap true := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have h := D.glue_condition false true
  rw [hf,hf',ht] at h
  have hh := congrArg (fun f : D.V (false,true) ⟶ D.glued => eqToHom e.symm ≫ f) h.symm
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hh



def lpsOriginalIntegerNormalChartToProjectiveJ (N : ℕ) (hN : 0<N) :
    ∀ b, lpsOriginalIntegerNormalSchemeChart N hN b ⟶
      lpsOriginalIntegerProjectiveJLine := by
  intro b
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroChartToJLine N hN ≫
      lpsOriginalIntegerProjectiveJChartMap false
  | true => exact lpsOriginalIntegerNormalInfinityChartToJLine N hN ≫
      lpsOriginalIntegerProjectiveJChartMap true

lemma lpsOriginalIntegerNormalChartToProjectiveJ_overlap
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN false =
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN true := by
  have hb : Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ)) ≫
      lpsOriginalIntegerProjectiveJChartMap false =
    Spec.map (CommRingCat.ofHom lpsOriginalIntegerReciprocalLaurentPolynomialMap) ≫
      lpsOriginalIntegerProjectiveJChartMap true :=
    lpsOriginalIntegerProjectiveJOverlap_agreement
  change Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)) ≫
      (lpsOriginalIntegerNormalZeroChartToJLine N hN ≫
        lpsOriginalIntegerProjectiveJChartMap false) =
    Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN)) ≫
      (lpsOriginalIntegerNormalInfinityChartToJLine N hN ≫
        lpsOriginalIntegerProjectiveJChartMap true)
  rw [← Category.assoc, lpsOriginalIntegerNormalZeroChartToJLine_overlap,
    Category.assoc, hb, ← Category.assoc,
    ← lpsOriginalIntegerNormalInfinityChartToJLine_overlap, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalChartToProjectiveJ_glueCondition
    (N : ℕ) (hN : 0<N) :
    let D := (lpsOriginalIntegerNormalSchemeGlueData N hN).toGlueData
    ∀ a : Bool × Bool,
      D.diagram.fst a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.2 := by
  let D := (lpsOriginalIntegerNormalSchemeGlueData N hN).toGlueData
  change ∀ a : Bool × Bool,
    D.diagram.fst a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.2
  rintro ⟨i,j⟩
  change D.f i j ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN i =
    (D.t i j ≫ D.f j i) ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN j
  cases i <;> cases j
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerProjectiveJLine => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalChartToProjectiveJ_overlap N hN)
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · have e : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerProjectiveJLine => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalChartToProjectiveJ_overlap N hN).symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]

def lpsOriginalIntegerNormalGluedToProjectiveJ (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedScheme N hN ⟶ lpsOriginalIntegerProjectiveJLine :=
  Multicoequalizer.desc _ _ (lpsOriginalIntegerNormalChartToProjectiveJ N hN)
    (lpsOriginalIntegerNormalChartToProjectiveJ_glueCondition N hN)

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_chart
    (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalGluedChartMap N hN b ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalChartToProjectiveJ N hN b :=
  Multicoequalizer.π_desc _ _ _ _ _

lemma lpsOriginalIntegerNormalZeroChartToJLine_pullback
    (N : ℕ) (hN : 0<N) :
    IsPullback (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)))
      (lpsOriginalIntegerNormalLaurentChartToJOverlap N hN)
      (lpsOriginalIntegerNormalZeroChartToJLine N hN)
      (lpsOriginalIntegerProjectiveJOverlapMap false) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerLaurentBase_scalarTower N hN
  let C := lpsOriginalIntegerNormalZeroChart N hN
  let B := lpsOriginalIntegerNormalLaurentChart N hN
  let instCB : Algebra C B := (lpsOriginalIntegerNormalZeroToLaurent N hN).toAlgebra
  let : SMul C B := instCB.toSMul
  let instAB : Algebra (Polynomial ℤ) B :=
    (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)).algebra'
  let : SMul (Polynomial ℤ) B := instAB.toSMul
  let : IsScalarTower (Polynomial ℤ) C B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  let : IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ) B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    exact (lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial N hN P).symm
  let : IsLocalization (Algebra.algebraMapSubmonoid C
      (Submonoid.powers (Polynomial.X : Polynomial ℤ))) B := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact lpsOriginalIntegerNormalOverlap_localization N hN
  let : Algebra.IsPushout (Polynomial ℤ) C (LaurentPolynomial ℤ) B :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial ℤ))
      (LaurentPolynomial ℤ) C B
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (Polynomial ℤ) C (LaurentPolynomial ℤ) B)

lemma lpsOriginalIntegerNormalInfinityChartToJLine_pullback
    (N : ℕ) (hN : 0<N) :
    IsPullback (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN)))
      (lpsOriginalIntegerNormalLaurentChartToJOverlap N hN)
      (lpsOriginalIntegerNormalInfinityChartToJLine N hN)
      (lpsOriginalIntegerProjectiveJOverlapMap true) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  let C := lpsOriginalIntegerNormalInfinityChart N hN
  let B := lpsOriginalIntegerNormalLaurentChart N hN
  let instCB : Algebra C B := (lpsOriginalIntegerNormalInfinityToLaurent N hN).toAlgebra
  let : SMul C B := instCB.toSMul
  let instAB : Algebra (Polynomial ℤ) B :=
    (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)).algebra'
  let : SMul (Polynomial ℤ) B := instAB.toSMul
  let : IsLocalization.Away (Polynomial.X : Polynomial ℤ) (LaurentPolynomial ℤ) :=
    lpsOriginalIntegerReciprocalLaurent_isLocalization
  let : IsScalarTower (Polynomial ℤ) C B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  let : IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ) B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    exact (lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial N hN P).symm
  let : IsLocalization (Algebra.algebraMapSubmonoid C
      (Submonoid.powers (Polynomial.X : Polynomial ℤ))) B := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact lpsOriginalIntegerReciprocalNormalOverlap_localization N hN
  let : Algebra.IsPushout (Polynomial ℤ) C (LaurentPolynomial ℤ) B :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial ℤ))
      (LaurentPolynomial ℤ) C B
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (Polynomial ℤ) C (LaurentPolynomial ℤ) B)

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJCharts_pullback :
    IsPullback (lpsOriginalIntegerProjectiveJOverlapMap false)
      (lpsOriginalIntegerProjectiveJOverlapMap true)
      (lpsOriginalIntegerProjectiveJChartMap false)
      (lpsOriginalIntegerProjectiveJChartMap true) := by
  let D := lpsOriginalIntegerProjectiveJGlueData
  have e : D.V (false,true)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerProjectiveJOverlapMap false := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerProjectiveJOverlapMap true := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have h : IsPullback (D.f false true) (D.t false true ≫ D.f true false)
      (D.ι false) (D.ι true) :=
    { w := (D.glue_condition false true).symm
      isLimit' := ⟨D.vPullbackConeIsLimit false true⟩ }
  apply h.of_iso (eqToIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, eqToIso.hom, Category.comp_id] using hf
  · simp only [Iso.refl_hom, eqToIso.hom, Category.comp_id]
    rw [ht,hf']
    simp only [Category.assoc,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp]
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply
    (N : ℕ) (hN : 0<N) (b : Bool)
    (y : lpsOriginalIntegerNormalSchemeChart N hN b) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN
      (lpsOriginalIntegerNormalGluedChartMap N hN b y) =
      lpsOriginalIntegerNormalChartToProjectiveJ N hN b y := by
  exact congrArg (fun f : lpsOriginalIntegerNormalSchemeChart N hN b ⟶
    lpsOriginalIntegerProjectiveJLine => f y)
    (lpsOriginalIntegerNormalGluedToProjectiveJ_chart N hN b)

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_zero
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN ⁻¹'
      Set.range (lpsOriginalIntegerProjectiveJChartMap false) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN false) := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨b,z,hz⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
    cases b with
    | false => exact ⟨z,hz⟩
    | true =>
      have h : lpsOriginalIntegerProjectiveJChartMap false y =
        lpsOriginalIntegerProjectiveJChartMap true
          (lpsOriginalIntegerNormalInfinityChartToJLine N hN z) := by
        rw [hy,← hz,lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply]
        rfl
      obtain ⟨v,hv0,hv1⟩ := Scheme.exists_preimage_of_isPullback
        lpsOriginalIntegerProjectiveJCharts_pullback y
        (lpsOriginalIntegerNormalInfinityChartToJLine N hN z) h
      obtain ⟨w,hw1,_⟩ := Scheme.exists_preimage_of_isPullback
        (lpsOriginalIntegerNormalInfinityChartToJLine_pullback N hN) z v hv1.symm
      refine ⟨lpsOriginalIntegerNormalSchemeOverlapMap N hN false w,?_⟩
      calc
        lpsOriginalIntegerNormalGluedChartMap N hN false
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN false w) =
          lpsOriginalIntegerNormalGluedChartMap N hN true
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN true w) :=
          congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
            lpsOriginalIntegerNormalGluedScheme N hN => f w)
            (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
        _ = lpsOriginalIntegerNormalGluedChartMap N hN true z :=
          congrArg (lpsOriginalIntegerNormalGluedChartMap N hN true) hw1
        _ = x := hz
  · rintro ⟨z,rfl⟩
    refine ⟨lpsOriginalIntegerNormalZeroChartToJLine N hN z,?_⟩
    exact (lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply N hN false z).symm

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN ⁻¹'
      Set.range (lpsOriginalIntegerProjectiveJChartMap true) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN true) := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨b,z,hz⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
    cases b with
    | false =>
      have h : lpsOriginalIntegerProjectiveJChartMap true y =
        lpsOriginalIntegerProjectiveJChartMap false
          (lpsOriginalIntegerNormalZeroChartToJLine N hN z) := by
        rw [hy,← hz,lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply]
        rfl
      obtain ⟨v,hv1,hv0⟩ := Scheme.exists_preimage_of_isPullback
        lpsOriginalIntegerProjectiveJCharts_pullback.flip y
        (lpsOriginalIntegerNormalZeroChartToJLine N hN z) h
      obtain ⟨w,hw0,_⟩ := Scheme.exists_preimage_of_isPullback
        (lpsOriginalIntegerNormalZeroChartToJLine_pullback N hN) z v hv0.symm
      refine ⟨lpsOriginalIntegerNormalSchemeOverlapMap N hN true w,?_⟩
      calc
        lpsOriginalIntegerNormalGluedChartMap N hN true
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN true w) =
          lpsOriginalIntegerNormalGluedChartMap N hN false
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN false w) :=
          congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
            lpsOriginalIntegerNormalGluedScheme N hN => f w)
            (lpsOriginalIntegerNormalGluedOverlap_agreement N hN).symm
        _ = lpsOriginalIntegerNormalGluedChartMap N hN false z :=
          congrArg (lpsOriginalIntegerNormalGluedChartMap N hN false) hw0
        _ = x := hz
    | true => exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    refine ⟨lpsOriginalIntegerNormalInfinityChartToJLine N hN z,?_⟩
    exact (lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply N hN true z).symm

def lpsOriginalIntegerNormalChartProjection (N : ℕ) (hN : 0<N) :
    ∀ b, lpsOriginalIntegerNormalSchemeChart N hN b ⟶ Spec (.of (Polynomial ℤ)) := by
  intro b
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroChartToJLine N hN
  | true => exact lpsOriginalIntegerNormalInfinityChartToJLine N hN

lemma lpsOriginalIntegerNormalChartProjection_comp
    (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalChartProjection N hN b ≫
      lpsOriginalIntegerProjectiveJChartMap b =
    lpsOriginalIntegerNormalChartToProjectiveJ N hN b := by
  cases b <;> rfl

lemma lpsOriginalIntegerNormalChartProjection_finite
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    IsFinite (lpsOriginalIntegerNormalChartProjection N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroChartToJLine_finite N hN
  | true => exact lpsOriginalIntegerNormalInfinityChartToJLine_finite N hN

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_chart
    (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN ⁻¹'
      Set.range (lpsOriginalIntegerProjectiveJChartMap b) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_zero N hN
  | true => exact lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity N hN

lemma lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsPullback (lpsOriginalIntegerNormalGluedChartMap N hN b)
      (lpsOriginalIntegerNormalChartProjection N hN b)
      (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
      (lpsOriginalIntegerProjectiveJChartMap b) := by
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN b
  let := lpsOriginalIntegerProjectiveJChartMap_openImmersion b
  have h : lpsOriginalIntegerNormalGluedChartMap N hN b ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalChartProjection N hN b ≫
      lpsOriginalIntegerProjectiveJChartMap b :=
    (lpsOriginalIntegerNormalGluedToProjectiveJ_chart N hN b).trans
      (lpsOriginalIntegerNormalChartProjection_comp N hN b).symm
  refine { w := h, isLimit' := ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩ }
  · intro s
    apply IsOpenImmersion.lift (lpsOriginalIntegerNormalGluedChartMap N hN b) s.fst
    rw [← lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_chart]
    rintro x ⟨x,rfl⟩
    refine ⟨s.snd x,?_⟩
    change (s.snd ≫ lpsOriginalIntegerProjectiveJChartMap b) x =
      (s.fst ≫ lpsOriginalIntegerNormalGluedToProjectiveJ N hN) x
    rw [s.condition]
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (lpsOriginalIntegerProjectiveJChartMap b),
      Category.assoc, ← h, IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    simpa only [← cancel_mono (lpsOriginalIntegerNormalGluedChartMap N hN b),
      IsOpenImmersion.lift_fac] using h1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma lpsOriginalIntegerNormalGluedToProjectiveJ_finite
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsFinite (lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P:=@IsFinite)
    lpsOriginalIntegerProjectiveJGlueData.openCover).mpr
  intro b
  let := lpsOriginalIntegerNormalChartProjection_finite N hN b
  have h := lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback N hN b
  change IsFinite (pullback.snd (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
    (lpsOriginalIntegerProjectiveJChartMap b))
  rw [← h.isoPullback_inv_snd]
  infer_instance

def lpsOriginalIntegerProjectiveJChartToSpecZ :
    Spec (.of (Polynomial ℤ)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

lemma lpsOriginalIntegerProjectiveJOverlap_compSpecZ (b : Bool) :
    lpsOriginalIntegerProjectiveJOverlapMap b ≫
      lpsOriginalIntegerProjectiveJChartToSpecZ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))) := by
  cases b with
  | false =>
      unfold lpsOriginalIntegerProjectiveJOverlapMap
        lpsOriginalIntegerProjectiveJChartToSpecZ
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact (Polynomial.toLaurent_C z).trans (LaurentPolynomial.C_eq_algebraMap z)
  | true =>
      unfold lpsOriginalIntegerProjectiveJOverlapMap
        lpsOriginalIntegerProjectiveJChartToSpecZ
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C z)) = _
      rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C,LaurentPolynomial.C_eq_algebraMap]
      rfl

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJChartToSpecZ_glueCondition :
    let D := lpsOriginalIntegerProjectiveJGlueData.toGlueData
    ∀ a : Bool × Bool, D.diagram.fst a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ =
      D.diagram.snd a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ := by
  let D := lpsOriginalIntegerProjectiveJGlueData.toGlueData
  change ∀ a : Bool × Bool, D.diagram.fst a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ =
    D.diagram.snd a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ
  rintro ⟨i,j⟩
  change D.f i j ≫ lpsOriginalIntegerProjectiveJChartToSpecZ =
    (D.t i j ≫ D.f j i) ≫ lpsOriginalIntegerProjectiveJChartToSpecZ
  have h : lpsOriginalIntegerProjectiveJOverlapMap false ≫
      lpsOriginalIntegerProjectiveJChartToSpecZ =
    lpsOriginalIntegerProjectiveJOverlapMap true ≫
      lpsOriginalIntegerProjectiveJChartToSpecZ :=
    (lpsOriginalIntegerProjectiveJOverlap_compSpecZ false).trans
      (lpsOriginalIntegerProjectiveJOverlap_compSpecZ true).symm
  cases i <;> cases j
  · simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',lpsOriginalIntegerProjectiveJGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (LaurentPolynomial ℤ)) := by
      simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
        lpsOriginalIntegerProjectiveJGlueDataPrime]
    have he := congrArg (fun f : Spec (.of (LaurentPolynomial ℤ)) ⟶ Spec (.of ℤ) => eqToHom e ≫ f) h
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime] using he
  · have e : D.V (true,false)=Spec (.of (LaurentPolynomial ℤ)) := by
      simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
        lpsOriginalIntegerProjectiveJGlueDataPrime]
    have he := congrArg (fun f : Spec (.of (LaurentPolynomial ℤ)) ⟶ Spec (.of ℤ) => eqToHom e ≫ f) h.symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime] using he
  · simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',lpsOriginalIntegerProjectiveJGlueDataPrime]

def lpsOriginalIntegerProjectiveJLineToSpecZ :
    lpsOriginalIntegerProjectiveJLine ⟶ Spec (.of ℤ) :=
  Multicoequalizer.desc _ _ (fun _ => lpsOriginalIntegerProjectiveJChartToSpecZ)
    lpsOriginalIntegerProjectiveJChartToSpecZ_glueCondition

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_chart (b : Bool) :
    lpsOriginalIntegerProjectiveJChartMap b ≫
      lpsOriginalIntegerProjectiveJLineToSpecZ =
    lpsOriginalIntegerProjectiveJChartToSpecZ :=
  Multicoequalizer.π_desc _ _ _ _ _

lemma lpsOriginalIntegerProjectiveJ_specLocal_chart
    (R : Type) [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ (b : Bool) (g : Spec (.of R) ⟶ Spec (.of (Polynomial ℤ))),
      g ≫ lpsOriginalIntegerProjectiveJChartMap b = f := by
  obtain ⟨b,y,hy⟩ := lpsOriginalIntegerProjectiveJChartMap_cover
    (f (IsLocalRing.closedPoint R))
  let := lpsOriginalIntegerProjectiveJChartMap_openImmersion b
  let U : TopologicalSpace.Opens (PrimeSpectrum R) :=
    f ⁻¹ᵁ (lpsOriginalIntegerProjectiveJChartMap b).opensRange
  have hU : U=⊤ := (IsLocalRing.closedPoint_mem_iff U).mp ⟨y,hy⟩
  have hr : Set.range f ⊆ Set.range (lpsOriginalIntegerProjectiveJChartMap b) := by
    rintro x ⟨x,rfl⟩
    have hx : x ∈ U := by rw [hU]; trivial
    exact hx
  exact ⟨b,IsOpenImmersion.lift (lpsOriginalIntegerProjectiveJChartMap b) f hr,
    IsOpenImmersion.lift_fac _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJChartToSpecZ_finiteType :
    LocallyOfFiniteType lpsOriginalIntegerProjectiveJChartToSpecZ := by
  unfold lpsOriginalIntegerProjectiveJChartToSpecZ
  rw [HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)]
  change RingHom.FiniteType (Polynomial.C : ℤ →+* Polynomial ℤ)
  rw [← Polynomial.algebraMap_eq, RingHom.finiteType_algebraMap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma lpsOriginalIntegerProjectiveJLineToSpecZ_finiteType :
    LocallyOfFiniteType lpsOriginalIntegerProjectiveJLineToSpecZ := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P:=@LocallyOfFiniteType)
    lpsOriginalIntegerProjectiveJGlueData.openCover).mpr
  intro b
  change LocallyOfFiniteType (lpsOriginalIntegerProjectiveJChartMap b ≫
    lpsOriginalIntegerProjectiveJLineToSpecZ)
  rw [lpsOriginalIntegerProjectiveJLineToSpecZ_chart]
  exact lpsOriginalIntegerProjectiveJChartToSpecZ_finiteType

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_quasiCompact :
    QuasiCompact lpsOriginalIntegerProjectiveJLineToSpecZ := by
  let := lpsOriginalIntegerProjectiveJLine_noetherian
  infer_instance

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated :
    QuasiSeparated lpsOriginalIntegerProjectiveJLineToSpecZ := by
  let := lpsOriginalIntegerProjectiveJLine_noetherian
  infer_instance

def lpsOriginalIntegerProjectiveJAffinePoint
    (R : Type) [CommRing R] (b : Bool) (x : R) :
    Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) x)) ≫
    lpsOriginalIntegerProjectiveJChartMap b

lemma lpsOriginalIntegerProjectiveJ_specLocal_coordinate
    (R : Type) [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ (b : Bool) (x : R), f=lpsOriginalIntegerProjectiveJAffinePoint R b x := by
  obtain ⟨b,g,hg⟩ := lpsOriginalIntegerProjectiveJ_specLocal_chart R f
  let φ := Spec.preimage g
  have he : φ.hom = Polynomial.eval₂RingHom (Int.castRingHom R) (φ.hom Polynomial.X) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [Polynomial.eval₂RingHom]
  have hm : Spec.map (CommRingCat.ofHom φ.hom)=g := Spec.map_preimage g
  rw [he] at hm
  refine ⟨b,φ.hom Polynomial.X,?_⟩
  unfold lpsOriginalIntegerProjectiveJAffinePoint
  rw [hm]
  exact hg.symm

lemma lpsOriginalIntegerProjectiveJAffinePoint_baseChange
    (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (b : Bool) (x : R) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      lpsOriginalIntegerProjectiveJAffinePoint R b x =
    lpsOriginalIntegerProjectiveJAffinePoint K b (algebraMap R K x) := by
  unfold lpsOriginalIntegerProjectiveJAffinePoint
  rw [← Category.assoc,← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · simp [Polynomial.eval₂RingHom]

lemma lpsOriginalIntegerProjectiveJAffinePoint_unitInverse
    (R : Type) [CommRing R] (u : Rˣ) :
    lpsOriginalIntegerProjectiveJAffinePoint R false (u : R) =
      lpsOriginalIntegerProjectiveJAffinePoint R true ((u⁻¹ : Rˣ) : R) := by
  let φ : LaurentPolynomial ℤ →+* R := LaurentPolynomial.eval₂ (Int.castRingHom R) u
  have h0 : Polynomial.eval₂RingHom (Int.castRingHom R) (u : R) =
      φ.comp (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [φ,RingHom.comp_apply,Polynomial.eval₂RingHom,Polynomial.toLaurent_X]
  have h1 : Polynomial.eval₂RingHom (Int.castRingHom R) ((u⁻¹ : Rˣ) : R) =
      φ.comp lpsOriginalIntegerReciprocalLaurentPolynomialMap := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [φ,RingHom.comp_apply,Polynomial.eval₂RingHom,
        lpsOriginalIntegerReciprocalLaurentPolynomialMap,Polynomial.toLaurent_X,
        LaurentPolynomial.invert_T]
  unfold lpsOriginalIntegerProjectiveJAffinePoint
  rw [h0,h1,CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp,
    Category.assoc,Category.assoc]
  exact congrArg (fun f : Spec (.of (LaurentPolynomial ℤ)) ⟶
    lpsOriginalIntegerProjectiveJLine => Spec.map (CommRingCat.ofHom φ) ≫ f)
    lpsOriginalIntegerProjectiveJOverlap_agreement

lemma lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse
    (K : Type) [Field K] (x : K) (hx : x≠0) :
    lpsOriginalIntegerProjectiveJAffinePoint K false x =
      lpsOriginalIntegerProjectiveJAffinePoint K true x⁻¹ := by
  simpa using lpsOriginalIntegerProjectiveJAffinePoint_unitInverse K (Units.mk0 x hx)

lemma lpsOriginalIntegerSpecZ_hom_unique
    (R : Type) [CommRing R] (f g : Spec (.of R) ⟶ Spec (.of ℤ)) : f=g := by
  rw [← Spec.map_preimage f,← Spec.map_preimage g]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

lemma lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ
    (R : Type) [CommRing R] (b : Bool) (x : R) :
    lpsOriginalIntegerProjectiveJAffinePoint R b x ≫
      lpsOriginalIntegerProjectiveJLineToSpecZ =
    Spec.map (CommRingCat.ofHom (Int.castRingHom R)) :=
  lpsOriginalIntegerSpecZ_hom_unique R _ _

lemma lpsOriginalIntegerProjectiveJ_valuation_extension
    (R K : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : Spec (.of K) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ g : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g=f := by
  obtain ⟨b,x,rfl⟩ := lpsOriginalIntegerProjectiveJ_specLocal_coordinate K f
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r,hr⟩ | ⟨r,hr⟩
  · refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R b r,?_⟩
    rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,hr]
  · by_cases hx : x=0
    · refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R b 0,?_⟩
      rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,map_zero,hx]
    · cases b with
      | false =>
          refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R true r,?_⟩
          rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,hr]
          exact (lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse K x hx).symm
      | true =>
          refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R false r,?_⟩
          rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,hr]
          simpa using lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse K x⁻¹ (inv_ne_zero hx)

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeExistence :
    ValuativeCriterion.Existence lpsOriginalIntegerProjectiveJLineToSpecZ := by
  intro S
  obtain ⟨g,hg⟩ := lpsOriginalIntegerProjectiveJ_valuation_extension S.R S.K S.i₁
  exact ⟨⟨g,hg,lpsOriginalIntegerSpecZ_hom_unique S.R _ S.i₂⟩⟩

lemma lpsOriginalIntegerProjectiveJAffinePoint_injective
    (R : Type) [CommRing R] (b : Bool) :
    Function.Injective (lpsOriginalIntegerProjectiveJAffinePoint R b) := by
  let := lpsOriginalIntegerProjectiveJChartMap_openImmersion b
  intro x y h
  change Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) x)) ≫
      lpsOriginalIntegerProjectiveJChartMap b =
    Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) y)) ≫
      lpsOriginalIntegerProjectiveJChartMap b at h
  have hm := (cancel_mono (lpsOriginalIntegerProjectiveJChartMap b)).mp h
  have he := congrArg (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of R =>
    f.hom Polynomial.X) (Spec.map_injective hm)
  simpa [Polynomial.eval₂RingHom] using he

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul
    (R : Type) [CommRing R] (x y : R)
    (h : lpsOriginalIntegerProjectiveJAffinePoint R false x =
      lpsOriginalIntegerProjectiveJAffinePoint R true y) : x*y=1 := by
  let fx : Spec (.of R) ⟶ Spec (.of (Polynomial ℤ)) :=
    Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) x))
  let fy : Spec (.of R) ⟶ Spec (.of (Polynomial ℤ)) :=
    Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) y))
  have hc : fx ≫ lpsOriginalIntegerProjectiveJChartMap false =
      fy ≫ lpsOriginalIntegerProjectiveJChartMap true := h
  let l := lpsOriginalIntegerProjectiveJCharts_pullback.lift fx fy hc
  let φ : LaurentPolynomial ℤ →+* R := (Spec.preimage l).hom
  have hl0 := lpsOriginalIntegerProjectiveJCharts_pullback.lift_fst fx fy hc
  change l ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ)) = fx at hl0
  rw [← Spec.map_preimage l,← Spec.map_comp] at hl0
  have he0 := congrArg (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of R =>
    f.hom Polynomial.X) (Spec.map_injective hl0)
  have hx : φ (LaurentPolynomial.T (1 : ℤ))=x := by
    simpa [φ,fx,CommRingCat.hom_comp,RingHom.comp_apply,
      Polynomial.toLaurent_X,Polynomial.eval₂RingHom] using he0
  have hl1 := lpsOriginalIntegerProjectiveJCharts_pullback.lift_snd fx fy hc
  change l ≫ Spec.map (CommRingCat.ofHom
    lpsOriginalIntegerReciprocalLaurentPolynomialMap) = fy at hl1
  rw [← Spec.map_preimage l,← Spec.map_comp] at hl1
  have he1 := congrArg (fun f : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of R =>
    f.hom Polynomial.X) (Spec.map_injective hl1)
  have hy : φ (LaurentPolynomial.T (-1 : ℤ))=y := by
    simpa [φ,fy,CommRingCat.hom_comp,RingHom.comp_apply,
      lpsOriginalIntegerReciprocalLaurentPolynomialMap,Polynomial.toLaurent_X,
      LaurentPolynomial.invert_T,Polynomial.eval₂RingHom] using he1
  calc
    x*y = φ (LaurentPolynomial.T (1 : ℤ))*φ (LaurentPolynomial.T (-1 : ℤ)) := by rw [hx,hy]
    _ = φ (LaurentPolynomial.T (1 : ℤ)*LaurentPolynomial.T (-1 : ℤ)) := (map_mul φ _ _).symm
    _ = φ (LaurentPolynomial.T (0 : ℤ)) := by congr 1; rw [← LaurentPolynomial.T_add]; rfl
    _ = 1 := by rw [LaurentPolynomial.T_zero,map_one]

lemma lpsOriginalIntegerProjectiveJAffinePoint_crossChart_of_mul
    (R : Type) [CommRing R] (x y : R) (hxy : x*y=1) :
    lpsOriginalIntegerProjectiveJAffinePoint R false x =
      lpsOriginalIntegerProjectiveJAffinePoint R true y := by
  let u : Rˣ := ⟨x,y,hxy,by rw [mul_comm]; exact hxy⟩
  exact lpsOriginalIntegerProjectiveJAffinePoint_unitInverse R u

lemma lpsOriginalIntegerProjectiveJ_fraction_precompose_injective
    (R K : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Function.Injective (fun f : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine =>
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f) := by
  intro f g h
  obtain ⟨b,x,rfl⟩ := lpsOriginalIntegerProjectiveJ_specLocal_coordinate R f
  obtain ⟨c,y,rfl⟩ := lpsOriginalIntegerProjectiveJ_specLocal_coordinate R g
  change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      lpsOriginalIntegerProjectiveJAffinePoint R b x =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      lpsOriginalIntegerProjectiveJAffinePoint R c y at h
  rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,
    lpsOriginalIntegerProjectiveJAffinePoint_baseChange] at h
  cases b <;> cases c
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_injective K false h
    rw [IsFractionRing.injective R K he]
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul K _ _ h
    have hr : x*y=1 := IsFractionRing.injective R K (by simpa only [map_mul,map_one] using he)
    exact lpsOriginalIntegerProjectiveJAffinePoint_crossChart_of_mul R x y hr
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul K _ _ h.symm
    have hr : y*x=1 := IsFractionRing.injective R K (by simpa only [map_mul,map_one] using he)
    exact (lpsOriginalIntegerProjectiveJAffinePoint_crossChart_of_mul R y x hr).symm
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_injective K true h
    rw [IsFractionRing.injective R K he]

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeUniqueness :
    ValuativeCriterion.Uniqueness lpsOriginalIntegerProjectiveJLineToSpecZ := by
  intro S
  refine ⟨fun l₁ l₂ => CommSq.LiftStruct.ext ?_⟩
  apply lpsOriginalIntegerProjectiveJ_fraction_precompose_injective S.R S.K
  exact l₁.fac_left.trans l₂.fac_left.symm

lemma lpsOriginalIntegerProjectiveJLineToSpecZ_proper :
    IsProper lpsOriginalIntegerProjectiveJLineToSpecZ := by
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_finiteType
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_quasiCompact
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated
  exact IsProper.of_valuativeCriterion _ (ValuativeCriterion.iff.mpr
    ⟨lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeExistence,
      lpsOriginalIntegerProjectiveJLineToSpecZ_valuativeUniqueness⟩)

def lpsOriginalIntegerNormalGluedToSpecZ (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedScheme N hN ⟶ Spec (.of ℤ) :=
  lpsOriginalIntegerNormalGluedToProjectiveJ N hN ≫
    lpsOriginalIntegerProjectiveJLineToSpecZ

lemma lpsOriginalIntegerNormalGluedToSpecZ_proper
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsProper (lpsOriginalIntegerNormalGluedToSpecZ N hN) := by
  let := lpsOriginalIntegerNormalGluedToProjectiveJ_finite N hN
  let := lpsOriginalIntegerProjectiveJLineToSpecZ_proper
  unfold lpsOriginalIntegerNormalGluedToSpecZ
  infer_instance


end
end QEC.Coding.TannerLiftedProduct

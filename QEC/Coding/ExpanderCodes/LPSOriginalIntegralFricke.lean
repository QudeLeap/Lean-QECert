import QEC.Coding.ExpanderCodes.LPSOriginalIntegerLevelFunctionField
import QEC.Coding.ExpanderCodes.LPSOriginalZeroNormalizationComparison
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Actual original integral Fricke involution

Restrict the genuine Fricke action to the original Q(j,j_N), and prove its
semilinear preservation of the original zero integral closure. Reverse,
swap, and reverse the actual monic integer modular equation. Its resulting
leading-coefficient denominator has constant coefficient one. On its actual
localization the inverse j_N satisfies a proved monic equation.

Integral closure commutes with this localization. The actual zero chart
and localized infinity chart cover the original glued integer model, and
the restricted Fricke maps agree on their scheme-theoretic intersection
by their literal original generated-field points. Glue them to a global
map and prove that it is an involution and an isomorphism over Z.

These are derived internal prerequisites of the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (484–486), not auxiliary statements
claimed to be separately stated there. Exact public th:qLDPC (231–238), node
pk-good-qldpc, and parent issue449 remain unproved. Complete good reduction,
Frobenius/Weil identities, full-level representation spectra and the exact
arbitrary-finite-field/every-rate quantum family require further mathematics.
-/

namespace QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

/-- Actual Fricke restricted to the original two-generator field. -/
def lpsOriginalRationalFrickePullback (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
    (lpsOriginalFrickeMatrix_pos N hN)
  exact
    { toFun := fun x => ⟨f x, by
        have hm := Subfield.map_mem_map f.toRingHom
          (s := (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield) (x := x)
        rw [lpsOriginalGeneratedFunctionFieldQ_fricke_map] at hm
        exact hm.mpr x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField))
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun x y => Subtype.ext (map_add f (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField)) }

lemma lpsOriginalRationalFrickePullback_coe (N : ℕ) (hN : 0 < N)
    (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalFrickePullback N hN x : lpsOriginalGeneratedFunctionFieldQ N hN) :
      LPSOriginalHolomorphicFractionField) =
    lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) x := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rfl

lemma lpsOriginalRationalFrickePullback_involutive (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Function.Involutive (lpsOriginalRationalFrickePullback N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
    (lpsOriginalFrickeMatrix_pos N hN)
  have hg : Set.EqOn (f.toRingHom.comp f.toRingHom)
      (RingHom.id LPSOriginalHolomorphicFractionField)
      {lpsOriginalJInFractionField, lpsOriginalJNInFractionField N hN} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · subst y
      change f (f lpsOriginalJInFractionField) = lpsOriginalJInFractionField
      simp only [f, lpsOriginalPositiveFractionPullback_fricke_j,
        lpsOriginalPositiveFractionPullback_fricke_jN]
    · have he := Set.mem_singleton_iff.mp hy
      subst y
      change f (f (lpsOriginalJNInFractionField N hN)) = lpsOriginalJNInFractionField N hN
      simp only [f, lpsOriginalPositiveFractionPullback_fricke_jN,
        lpsOriginalPositiveFractionPullback_fricke_j]
  intro x
  apply Subtype.ext
  change f (f (x : LPSOriginalHolomorphicFractionField)) = (x : LPSOriginalHolomorphicFractionField)
  apply RingHom.eqOn_field_closure hg
  rw [← lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure N hN]
  exact x.property

/-- Actual involution, with inverse built from the proved generator action. -/
def lpsOriginalRationalFrickeEquiv (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN ≃+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f := lpsOriginalRationalFrickePullback N hN
  exact
    { toFun := f
      invFun := f
      left_inv := lpsOriginalRationalFrickePullback_involutive N hN
      right_inv := lpsOriginalRationalFrickePullback_involutive N hN
      map_mul' := f.map_mul
      map_add' := f.map_add }

/-- The original integer j-coordinate really is the embedded analytic j. -/
lemma lpsOriginalIntegerBaseToGeneratedField_X_coe (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalIntegerBaseToGeneratedField N hN Polynomial.X :
      lpsOriginalGeneratedFunctionFieldQ N hN) : LPSOriginalHolomorphicFractionField) =
        lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change lpsOriginalJFractionEmbeddingQ (lpsOriginalIntegerBaseFractionMap Polynomial.X) = _
  rw [lpsOriginalIntegerBaseFractionMap, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_X, lpsOriginalJFractionEmbeddingQ_polynomial,
    lpsOriginalJHolomorphicEvalQ_localization]
  simp [lpsOriginalJInFractionField]

/-- A real semilinear coefficient map sends integer j to the actual integral j_N. -/
def lpsOriginalIntegerFrickeCoefficientMap (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalIntegerAffineToNormal N hN (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN)))

lemma lpsOriginalIntegerFrickeCoefficientMap_compatibility
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
      (lpsOriginalIntegerFrickeCoefficientMap N hN) =
    (lpsOriginalRationalFrickePullback N hN).comp
      (lpsOriginalIntegerBaseToGeneratedField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalIntegerFrickeCoefficientMap]
  · apply Subtype.ext
    simp only [RingHom.comp_apply, lpsOriginalIntegerFrickeCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change ((lpsOriginalIntegerAffineToNormal N hN
      (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))).val.val) =
      ((lpsOriginalRationalFrickePullback N hN
        (lpsOriginalIntegerBaseToGeneratedField N hN Polynomial.X) :
          lpsOriginalGeneratedFunctionFieldQ N hN) : LPSOriginalHolomorphicFractionField)
    rw [lpsOriginalIntegerAffineToNormal_root]
    rw [lpsOriginalRationalFrickePullback_coe,
      lpsOriginalIntegerBaseToGeneratedField_X_coe,
      lpsOriginalPositiveFractionPullback_fricke_j]

lemma lpsOriginalIntegerFricke_preserves_normalZero
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalZeroChart N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsIntegral (Polynomial ℤ)
      (lpsOriginalRationalFrickePullback N hN (x : lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  have h := IsIntegral.map_of_comp_eq (lpsOriginalIntegerFrickeCoefficientMap N hN)
    (lpsOriginalRationalFrickePullback N hN)
    (lpsOriginalIntegerFrickeCoefficientMap_compatibility N hN) x.property
  exact isIntegral_trans (R := Polynomial ℤ) _ h

/-- Actual restriction to the original zero integral closure. -/
def lpsOriginalIntegerNormalZeroFrickePullback
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalZeroChart N hN →+* lpsOriginalIntegerNormalZeroChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact
    { toFun := fun x => ⟨lpsOriginalRationalFrickePullback N hN x.val,
        lpsOriginalIntegerFricke_preserves_normalZero N hN x⟩
      map_one' := Subtype.ext (map_one (lpsOriginalRationalFrickePullback N hN))
      map_mul' := fun x y => Subtype.ext (map_mul (lpsOriginalRationalFrickePullback N hN) x.val y.val)
      map_zero' := Subtype.ext (map_zero (lpsOriginalRationalFrickePullback N hN))
      map_add' := fun x y => Subtype.ext (map_add (lpsOriginalRationalFrickePullback N hN) x.val y.val) }

lemma lpsOriginalIntegerNormalZeroFrickePullback_involutive
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Involutive (lpsOriginalIntegerNormalZeroFrickePullback N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  intro x
  apply Subtype.ext
  exact lpsOriginalRationalFrickePullback_involutive N hN x.val


/-- Swapping the variables preserves the actual constant/constant coefficient. -/
lemma lpsOriginalBivariateSwap_coeff_zero_zero (P : Polynomial (Polynomial ℤ)) :
    ((Polynomial.Bivariate.swap P).coeff 0).coeff 0 = (P.coeff 0).coeff 0 := by
  have h := Polynomial.Bivariate.aevalAeval_swap (R := ℤ) (A := ℤ) (0 : ℤ) 0 P
  simpa only [Polynomial.coe_aevalAeval_eq_evalEval, Polynomial.evalEval,
    Polynomial.C_0, ← Polynomial.coeff_zero_eq_eval_zero] using h

/-- The actual denominator arising from reciprocal coordinates. -/
def lpsOriginalIntegerFrickeReciprocalDenominator (P : Polynomial (Polynomial ℤ)) :
    Polynomial ℤ := (Polynomial.Bivariate.swap P.reverse).coeff 0

/-- The actual double reciprocal equation, built by reverse/swap/reverse. -/
def lpsOriginalIntegerFrickeReciprocalPolynomial (P : Polynomial (Polynomial ℤ)) :
    Polynomial (Polynomial ℤ) := (Polynomial.Bivariate.swap P.reverse).reverse

lemma lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    (lpsOriginalIntegerFrickeReciprocalDenominator P).coeff 0 = 1 := by
  rw [lpsOriginalIntegerFrickeReciprocalDenominator,
    lpsOriginalBivariateSwap_coeff_zero_zero, Polynomial.coeff_zero_reverse, hP.leadingCoeff]
  simp

lemma lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    lpsOriginalIntegerFrickeReciprocalDenominator P ≠ 0 := by
  intro h
  have hc := lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero P hP
  rw [h, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

lemma lpsOriginalIntegerFrickeReciprocalPolynomial_leadingCoeff
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    (lpsOriginalIntegerFrickeReciprocalPolynomial P).leadingCoeff =
      lpsOriginalIntegerFrickeReciprocalDenominator P := by
  rw [lpsOriginalIntegerFrickeReciprocalPolynomial, Polynomial.reverse_leadingCoeff,
    Polynomial.trailingCoeff_eq_coeff_zero
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero P hP)]
  rfl

lemma lpsOriginalIntegerFrickeReciprocalDenominator_coprime_X
    (P : Polynomial (Polynomial ℤ)) (hP : P.Monic) :
    IsCoprime Polynomial.X (lpsOriginalIntegerFrickeReciprocalDenominator P) := by
  have hd := Polynomial.X_dvd_sub_C (p := lpsOriginalIntegerFrickeReciprocalDenominator P)
  rw [lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero P hP, Polynomial.C_1] at hd
  simpa only [sub_add_cancel] using IsCoprime.add_one_right_of_dvd hd

/-- The denominator for the genuine original modular equation has constant1. -/
lemma lpsOriginalIntegerFrickeOriginalDenominator_coeff_zero
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerFrickeReciprocalDenominator
      (lpsOriginalIntegerPolynomial N hN)).coeff 0 = 1 :=
  lpsOriginalIntegerFrickeReciprocalDenominator_coeff_zero _
    (lpsOriginalIntegerPolynomial_monic N hN)


lemma lpsOriginalBivariateAevalAeval_eq_eval2 {S : Type*} [CommRing S]
    (x y : S) (P : Polynomial (Polynomial ℤ)) :
    Polynomial.aevalAeval x y P =
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.eval₂_add, hP, hQ]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aevalAeval_C,
      Polynomial.aevalAeval_Y, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X]
    congr 1

lemma lpsOriginalBivariateSwap_eval2 {S : Type*} [CommRing S]
    (x y : S) (P : Polynomial (Polynomial ℤ)) :
    (Polynomial.Bivariate.swap P).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom S) x) y =
    P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) y) x := by
  rw [← lpsOriginalBivariateAevalAeval_eq_eval2,
    Polynomial.Bivariate.aevalAeval_swap, lpsOriginalBivariateAevalAeval_eq_eval2]

lemma lpsOriginalBivariateIntegerCoefficientEval_comp {S : Type*} [CommRing S]
    (f : S →+* S) (x : S) :
    f.comp (Polynomial.eval₂RingHom (Int.castRingHom S) x) =
      Polynomial.eval₂RingHom (Int.castRingHom S) (f x) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp

/-- The double reciprocal equation has exactly the swapped original roots. -/
lemma lpsOriginalIntegerFrickeReciprocalPolynomial_root_iff
    {S : Type*} [Field S] (P : Polynomial (Polynomial ℤ))
    (x y : S) (hx : x ≠ 0) (hy : y ≠ 0) :
    (lpsOriginalIntegerFrickeReciprocalPolynomial P).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) y⁻¹ = 0 ↔
    P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) y) x = 0 := by
  let := invertibleOfNonzero hx
  let := invertibleOfNonzero hy
  have h₁ := Polynomial.eval₂_reverse_eq_zero_iff
    (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) y
    (Polynomial.Bivariate.swap P.reverse)
  have h₂ := Polynomial.eval₂_reverse_eq_zero_iff
    (Polynomial.eval₂RingHom (Int.castRingHom S) y) x P
  simp only [invOf_eq_inv] at h₁ h₂
  rw [lpsOriginalIntegerFrickeReciprocalPolynomial, h₁,
    lpsOriginalBivariateSwap_eval2, h₂]

/-- Reuse the actual rational j-element already defined by the original normalization comparison. -/
lemma lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerBaseToGeneratedField N hN Polynomial.X =
      lpsOriginalRationalJElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerBaseFractionMap Polynomial.X) =
    algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X)
  congr 1
  simp [lpsOriginalIntegerBaseFractionMap]

def lpsOriginalRationalJNElement (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact lpsOriginalIntegerAffineToGenerated N hN
    (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN))

lemma lpsOriginalRationalJElement_coe (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalJElement N hN : lpsOriginalGeneratedFunctionFieldQ N hN) :
      LPSOriginalHolomorphicFractionField) = lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ N hN]
  exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN

lemma lpsOriginalRationalJNElement_coe (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalJNElement N hN : lpsOriginalGeneratedFunctionFieldQ N hN) :
      LPSOriginalHolomorphicFractionField) = lpsOriginalJNInFractionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact lpsOriginalIntegerAffineToNormal_root N hN

lemma lpsOriginalIntegerBaseToGeneratedField_eq_eval (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerBaseToGeneratedField N hN =
      Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simpa using lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ N hN

lemma lpsOriginalRationalFrickePullback_JElement
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickePullback N hN (lpsOriginalRationalJElement N hN) =
      lpsOriginalRationalJNElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Subtype.ext
  rw [lpsOriginalRationalFrickePullback_coe, lpsOriginalRationalJElement_coe,
    lpsOriginalRationalJNElement_coe, lpsOriginalPositiveFractionPullback_fricke_j]

lemma lpsOriginalRationalFrickePullback_JNElement
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickePullback N hN (lpsOriginalRationalJNElement N hN) =
      lpsOriginalRationalJElement N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Subtype.ext
  rw [lpsOriginalRationalFrickePullback_coe, lpsOriginalRationalJNElement_coe,
    lpsOriginalRationalJElement_coe, lpsOriginalPositiveFractionPullback_fricke_jN]

lemma lpsOriginalRationalJElement_ne_zero (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalJElement N hN ≠ 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalIntegerBaseToGeneratedField_X_eq_existingJ N hN]
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalIntegerBaseFractionMap Polynomial.X) ≠ 0
  exact (map_ne_zero_iff _ (algebraMap (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN)).injective).mpr
      lpsOriginalIntegerBaseFractionMap_X_ne_zero

lemma lpsOriginalRationalJNElement_ne_zero (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalJNElement N hN ≠ 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalRationalFrickePullback_JElement N hN]
  exact (map_ne_zero_iff _ (lpsOriginalRationalFrickePullback N hN).injective).mpr
    (lpsOriginalRationalJElement_ne_zero N hN)

/-- Actual modular equation at the actual field elements, obtained from AdjoinRoot. -/
lemma lpsOriginalIntegerPolynomial_generatedRoot (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN))
      (lpsOriginalRationalJNElement N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let f := lpsOriginalIntegerAffineToGenerated N hN
  have hc : f.comp (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN)) =
      lpsOriginalIntegerBaseToGeneratedField N hN := by
    apply RingHom.ext
    intro P
    exact lpsOriginalIntegerAffineToGenerated_base N hN P
  have h := congrArg f (AdjoinRoot.eval₂_root (lpsOriginalIntegerPolynomial N hN))
  rw [Polynomial.hom_eval₂, map_zero, hc, lpsOriginalIntegerBaseToGeneratedField_eq_eval] at h
  exact h

/-- Genuine Fricke transport swaps the actual modular-equation roots. -/
lemma lpsOriginalIntegerPolynomial_frickeSwappedRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJNElement N hN))
      (lpsOriginalRationalJElement N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  have h := congrArg (lpsOriginalRationalFrickePullback N hN)
    (lpsOriginalIntegerPolynomial_generatedRoot N hN)
  rw [Polynomial.hom_eval₂, map_zero, lpsOriginalBivariateIntegerCoefficientEval_comp,
    lpsOriginalRationalFrickePullback_JElement, lpsOriginalRationalFrickePullback_JNElement] at h
  exact h

/-- The actual inverse j_N is a root of the genuine double reciprocal polynomial. -/
lemma lpsOriginalIntegerFrickeOriginalReciprocalRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerFrickeReciprocalPolynomial (lpsOriginalIntegerPolynomial N hN)).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN)⁻¹)
      (lpsOriginalRationalJNElement N hN)⁻¹ = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerFrickeReciprocalPolynomial_root_iff _ _ _
    (lpsOriginalRationalJElement_ne_zero N hN)
    (lpsOriginalRationalJNElement_ne_zero N hN)).mpr
      (lpsOriginalIntegerPolynomial_frickeSwappedRoot N hN)


lemma lpsOriginalIntegerReciprocalBaseToGeneratedField_injective
    (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Function.Injective (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).injective.comp
    lpsOriginalIntegerReciprocalBaseFractionMap_injective

lemma lpsOriginalIntegerReciprocalBaseToGeneratedField_eq_eval
    (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerReciprocalBaseToGeneratedField N hN =
      Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJElement N hN)⁻¹ := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalJFractionInversion (lpsOriginalIntegerBaseFractionMap Polynomial.X)) = _
    have hx : lpsOriginalIntegerBaseFractionMap Polynomial.X =
        algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X := by
      simp [lpsOriginalIntegerBaseFractionMap]
    rw [hx, lpsOriginalJFractionInversion_X, map_inv₀]
    rfl

abbrev lpsOriginalIntegerFrickeLocalizedBase (N : ℕ) [NeZero N] (hN : 0 < N) :=
  Localization.Away (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))

/-- Actual localization of the reciprocal integer base into the existing original field. -/
def lpsOriginalIntegerFrickeLocalizedBaseMap (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerFrickeLocalizedBase N hN →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let f := lpsOriginalIntegerReciprocalBaseToGeneratedField N hN
  have hq : f q ≠ 0 :=
    (map_ne_zero_iff f (lpsOriginalIntegerReciprocalBaseToGeneratedField_injective N hN)).mpr
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero _
        (lpsOriginalIntegerPolynomial_monic N hN))
  exact IsLocalization.Away.lift q (IsUnit.mk0 _ hq)

lemma lpsOriginalIntegerFrickeLocalizedBaseMap_comp
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).comp
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)) =
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  simp [lpsOriginalIntegerFrickeLocalizedBaseMap]

lemma lpsOriginalIntegerFrickeLocalizedDenominator_ne_zero
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    algebraMap (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)
      (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)) ≠ 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let f := lpsOriginalIntegerFrickeLocalizedBaseMap N hN
  have hq : lpsOriginalIntegerReciprocalBaseToGeneratedField N hN q ≠ 0 :=
    (map_ne_zero_iff _ (lpsOriginalIntegerReciprocalBaseToGeneratedField_injective N hN)).mpr
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero _
        (lpsOriginalIntegerPolynomial_monic N hN))
  intro h
  have he := RingHom.congr_fun (lpsOriginalIntegerFrickeLocalizedBaseMap_comp N hN) q
  exact hq (he.symm.trans ((congrArg f h).trans (map_zero f)))

/-- Monic normalization of the actual double reciprocal polynomial on D(q). -/
def lpsOriginalIntegerFrickeLocalizedMonicPolynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial (lpsOriginalIntegerFrickeLocalizedBase N hN) := by
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  exact (lpsOriginalIntegerFrickeReciprocalPolynomial (lpsOriginalIntegerPolynomial N hN)).map
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)) *
    Polynomial.C (IsLocalization.Away.invSelf q : lpsOriginalIntegerFrickeLocalizedBase N hN)

lemma lpsOriginalIntegerFrickeLocalizedMonicPolynomial_monic
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerFrickeLocalizedMonicPolynomial N hN).Monic := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Nontrivial (lpsOriginalIntegerFrickeLocalizedBase N hN) :=
    (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).domain_nontrivial
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let A := lpsOriginalIntegerFrickeLocalizedBase N hN
  let g := algebraMap (Polynomial ℤ) A
  let P := lpsOriginalIntegerFrickeReciprocalPolynomial (lpsOriginalIntegerPolynomial N hN)
  have hP : P.leadingCoeff = q :=
    lpsOriginalIntegerFrickeReciprocalPolynomial_leadingCoeff _ (lpsOriginalIntegerPolynomial_monic N hN)
  have hq : g q ≠ 0 := lpsOriginalIntegerFrickeLocalizedDenominator_ne_zero N hN
  have hl : (P.map g).leadingCoeff = g q := by
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (by rw [hP]; exact hq), hP]
  have hi : IsUnit (IsLocalization.Away.invSelf q : A) := by
    refine ⟨⟨IsLocalization.Away.invSelf q, g q, ?_, ?_⟩, rfl⟩
    · simpa only [mul_comm] using (IsLocalization.Away.mul_invSelf q : g q * IsLocalization.Away.invSelf q = 1)
    · exact IsLocalization.Away.mul_invSelf q
  change ((P.map g) * Polynomial.C (IsLocalization.Away.invSelf q : A)).leadingCoeff = 1
  rw [Polynomial.leadingCoeff_mul_C_of_isUnit hi, hl]
  exact IsLocalization.Away.mul_invSelf q

lemma lpsOriginalIntegerFrickeLocalizedMonicPolynomial_root
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerFrickeLocalizedMonicPolynomial N hN).eval₂
      (lpsOriginalIntegerFrickeLocalizedBaseMap N hN) (lpsOriginalRationalJNElement N hN)⁻¹ = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalIntegerFrickeLocalizedMonicPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_map, Polynomial.eval₂_C, lpsOriginalIntegerFrickeLocalizedBaseMap_comp,
    lpsOriginalIntegerReciprocalBaseToGeneratedField_eq_eval,
    lpsOriginalIntegerFrickeOriginalReciprocalRoot, zero_mul]

/-- The genuine inverse j_N is integral over the actual localized reciprocal integer base. -/
lemma lpsOriginalIntegerFrickeLocalizedInverseJN_integral
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    IsIntegral (lpsOriginalIntegerFrickeLocalizedBase N hN) (lpsOriginalRationalJNElement N hN)⁻¹ := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  refine ⟨lpsOriginalIntegerFrickeLocalizedMonicPolynomial N hN,
    lpsOriginalIntegerFrickeLocalizedMonicPolynomial_monic N hN, ?_⟩
  exact lpsOriginalIntegerFrickeLocalizedMonicPolynomial_root N hN

lemma lpsOriginalIntegerFrickeLocalizedBase_scalarTower
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    IsScalarTower (Polynomial ℤ) (lpsOriginalIntegerFrickeLocalizedBase N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (lpsOriginalIntegerFrickeLocalizedBaseMap_comp N hN).symm

/-- Integral closure of the actual reciprocal base localized at the actual denominator. -/
abbrev lpsOriginalIntegerFrickeLocalizedNormalChart
    (N : ℕ) [NeZero N] (hN : 0 < N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  integralClosure (lpsOriginalIntegerFrickeLocalizedBase N hN)
    (lpsOriginalGeneratedFunctionFieldQ N hN)

/-- The inclusion of the original infinity chart into its genuine denominator localization. -/
def lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerFrickeLocalizedNormalChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  letI := lpsOriginalIntegerFrickeLocalizedBase_scalarTower N hN
  exact
    { toFun := fun x => ⟨x.val, x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

lemma lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Injective (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN) := by
  intro x y h
  exact Subtype.ext (congrArg
    (fun z : lpsOriginalIntegerFrickeLocalizedNormalChart N hN => z.val) h)

/-- This is the actual localization of the original infinity normal chart at q_N. -/
lemma lpsOriginalIntegerFrickeLocalizedNormalChart_localization
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    letI := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
        (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)))
      (lpsOriginalIntegerFrickeLocalizedNormalChart N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  let := lpsOriginalIntegerFrickeLocalizedBase_scalarTower N hN
  let C := lpsOriginalIntegerNormalInfinityChart N hN
  let D := lpsOriginalIntegerFrickeLocalizedNormalChart N hN
  let q := lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)
  let instCD : Algebra C D := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d l => by
      change (c.val*d.val)*l = c.val*(d.val*l)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  have hq : algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) q ≠ 0 :=
    (map_ne_zero_iff _ (lpsOriginalIntegerReciprocalBaseToGeneratedField_injective N hN)).mpr
      (lpsOriginalIntegerFrickeReciprocalDenominator_ne_zero _
        (lpsOriginalIntegerPolynomial_monic N hN))
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) q)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun y hy => by
      obtain ⟨n,rfl⟩ := hy
      exact (IsUnit.mk0 _ hq).pow n)
  exact IsLocalization.Away.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN)
    (Rf := lpsOriginalIntegerFrickeLocalizedBase N hN)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) q

/-- Semilinear reciprocal-coordinate map defined using the proved integral inverse j_N. -/
def lpsOriginalIntegerFrickeLocalizedCoefficientMap
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalIntegerFrickeLocalizedNormalChart N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  exact Polynomial.eval₂RingHom (Int.castRingHom _)
    ⟨(lpsOriginalRationalJNElement N hN)⁻¹,
      lpsOriginalIntegerFrickeLocalizedInverseJN_integral N hN⟩

lemma lpsOriginalIntegerFrickeLocalizedCoefficientMap_compatibility
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    (algebraMap (lpsOriginalIntegerFrickeLocalizedNormalChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
      (lpsOriginalIntegerFrickeLocalizedCoefficientMap N hN) =
    (lpsOriginalRationalFrickePullback N hN).comp
      (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalIntegerFrickeLocalizedCoefficientMap]
  · simp only [RingHom.comp_apply, lpsOriginalIntegerFrickeLocalizedCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      lpsOriginalIntegerReciprocalBaseToGeneratedField_eq_eval]
    change (lpsOriginalRationalJNElement N hN)⁻¹ =
      lpsOriginalRationalFrickePullback N hN (lpsOriginalRationalJElement N hN)⁻¹
    rw [map_inv₀, lpsOriginalRationalFrickePullback_JElement]

lemma lpsOriginalIntegerFricke_maps_normalInfinity_to_localized
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
    IsIntegral (lpsOriginalIntegerFrickeLocalizedBase N hN)
      (lpsOriginalRationalFrickePullback N hN x.val) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  have h := IsIntegral.map_of_comp_eq (lpsOriginalIntegerFrickeLocalizedCoefficientMap N hN)
    (lpsOriginalRationalFrickePullback N hN)
    (lpsOriginalIntegerFrickeLocalizedCoefficientMap_compatibility N hN) x.property
  exact isIntegral_trans (R := lpsOriginalIntegerFrickeLocalizedBase N hN) _ h

/-- Actual Fricke pullback on infinity, with values in the proved denominator localization. -/
def lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerFrickeLocalizedNormalChart N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  exact
    { toFun := fun x => ⟨lpsOriginalRationalFrickePullback N hN x.val,
        lpsOriginalIntegerFricke_maps_normalInfinity_to_localized N hN x⟩
      map_one' := Subtype.ext (map_one (lpsOriginalRationalFrickePullback N hN))
      map_mul' := fun x y => Subtype.ext (map_mul (lpsOriginalRationalFrickePullback N hN) x.val y.val)
      map_zero' := Subtype.ext (map_zero (lpsOriginalRationalFrickePullback N hN))
      map_add' := fun x y => Subtype.ext (map_add (lpsOriginalRationalFrickePullback N hN) x.val y.val) }

lemma lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback_coe
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback N hN x).val =
      lpsOriginalRationalFrickePullback N hN x.val := rfl

def lpsOriginalIntegerFrickeLocalizedChartToInfinity
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    Spec (.of (lpsOriginalIntegerFrickeLocalizedNormalChart N hN)) ⟶
      lpsOriginalIntegerNormalSchemeChart N hN true :=
  Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN))

lemma lpsOriginalIntegerFrickeLocalizedChartToInfinity_openImmersion
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    IsOpenImmersion (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
  let := lpsOriginalIntegerFrickeLocalizedNormalChart_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
      (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN)))

lemma lpsOriginalIntegerFrickeLocalizedChartToInfinity_range
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Set.range (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN) =
      (PrimeSpectrum.basicOpen
        (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
          (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))) :
        Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN).toAlgebra
  let := lpsOriginalIntegerFrickeLocalizedNormalChart_localization N hN
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma lpsOriginalIntegerNormalInfinityToLaurent_range
    (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Set.range (lpsOriginalIntegerNormalSchemeOverlapMap N hN true) =
      (PrimeSpectrum.basicOpen
        (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X) :
        Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToLaurent N hN).toAlgebra
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X)
      (lpsOriginalIntegerNormalLaurentChart N hN) :=
    lpsOriginalIntegerReciprocalNormalOverlap_localization N hN
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- Actual coprime denominator cover of the original infinity chart. -/
lemma lpsOriginalIntegerFrickeInfinity_basicOpen_cover
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN)) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    x ∈ PrimeSpectrum.basicOpen
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X) ∨
    x ∈ PrimeSpectrum.basicOpen
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
        (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let g := algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
  have hc := (lpsOriginalIntegerFrickeReciprocalDenominator_coprime_X _
    (lpsOriginalIntegerPolynomial_monic N hN)).map g
  rcases hc with ⟨a,b,hab⟩
  simp only [PrimeSpectrum.mem_basicOpen]
  by_contra! h
  have h1 := x.asIdeal.add_mem
    (x.asIdeal.mul_mem_left a h.1) (x.asIdeal.mul_mem_left b h.2)
  rw [hab] at h1
  exact x.2.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- Source charts for the actual Fricke extension, refined only where the denominator is a unit. -/
def lpsOriginalIntegerFrickeRefinedSchemeChart
    (N : ℕ) [NeZero N] (hN : 0 < N) : Bool → Scheme
  | false => lpsOriginalIntegerNormalSchemeChart N hN false
  | true => Spec (.of (lpsOriginalIntegerFrickeLocalizedNormalChart N hN))

def lpsOriginalIntegerFrickeRefinedChartToGlued
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerFrickeRefinedSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN := by
  cases b with
  | false => exact lpsOriginalIntegerNormalGluedChartMap N hN false
  | true => exact lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true

lemma lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerFrickeRefinedChartToGlued N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  | true =>
      let := lpsOriginalIntegerFrickeLocalizedChartToInfinity_openImmersion N hN
      let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN true
      exact inferInstanceAs (IsOpenImmersion
        (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN ≫
          lpsOriginalIntegerNormalGluedChartMap N hN true))

set_option backward.isDefEq.respectTransparency false in
/-- The genuine refined charts cover the whole original integer model. -/
lemma lpsOriginalIntegerFrickeRefinedChartToGlued_cover
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalIntegerFrickeRefinedSchemeChart N hN b),
      lpsOriginalIntegerFrickeRefinedChartToGlued N hN b y = x := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  obtain ⟨b,y,rfl⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
  cases b with
  | false => exact ⟨false,y,rfl⟩
  | true =>
      rcases lpsOriginalIntegerFrickeInfinity_basicOpen_cover N hN y with hx | hq
      · change y ∈ (PrimeSpectrum.basicOpen
          (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X) :
          Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) at hx
        rw [← lpsOriginalIntegerNormalInfinityToLaurent_range N hN] at hx
        obtain ⟨z,hz⟩ := hx
        refine ⟨false,lpsOriginalIntegerNormalSchemeOverlapMap N hN false z, ?_⟩
        have he := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
            lpsOriginalIntegerNormalGluedScheme N hN => f z)
          (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
        change lpsOriginalIntegerNormalGluedChartMap N hN false
          (lpsOriginalIntegerNormalSchemeOverlapMap N hN false z) =
          lpsOriginalIntegerNormalGluedChartMap N hN true y
        have he' : lpsOriginalIntegerNormalGluedChartMap N hN false
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN false z) =
          lpsOriginalIntegerNormalGluedChartMap N hN true
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN true z) := he
        exact he'.trans (congrArg (lpsOriginalIntegerNormalGluedChartMap N hN true) hz)
      · change y ∈ (PrimeSpectrum.basicOpen
          (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN)
            (lpsOriginalIntegerFrickeReciprocalDenominator (lpsOriginalIntegerPolynomial N hN))) :
          Set (PrimeSpectrum (lpsOriginalIntegerNormalInfinityChart N hN))) at hq
        rw [← lpsOriginalIntegerFrickeLocalizedChartToInfinity_range N hN] at hq
        obtain ⟨z,hz⟩ := hq
        refine ⟨true,z,?_⟩
        change lpsOriginalIntegerNormalGluedChartMap N hN true
          (lpsOriginalIntegerFrickeLocalizedChartToInfinity N hN z) =
            lpsOriginalIntegerNormalGluedChartMap N hN true y
        exact congrArg (lpsOriginalIntegerNormalGluedChartMap N hN true) hz

/-- Local target maps use the actual rational Fricke action, restricted by proved integrality. -/
def lpsOriginalIntegerFrickeRefinedChartMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerFrickeRefinedSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroFrickePullback N hN)) ≫
      lpsOriginalIntegerNormalGluedChartMap N hN false
  | true => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback N hN)) ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true

set_option backward.isDefEq.respectTransparency false in
/-- The infinity field-valued point is the same literal generic point of the glued model. -/
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_infinity
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalInfinityChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true =
        lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let u := Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalLaurentChart N hN)
    (lpsOriginalGeneratedFunctionFieldQ N hN)))
  have h0 : u ≫ lpsOriginalIntegerNormalSchemeOverlapMap N hN false =
      Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) := by
    rw [lpsOriginalIntegerNormalSchemeOverlapMap, ← Spec.map_comp]
    rfl
  have h1 : u ≫ lpsOriginalIntegerNormalSchemeOverlapMap N hN true =
      Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalInfinityChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) := by
    rw [lpsOriginalIntegerNormalSchemeOverlapMap, ← Spec.map_comp]
    rfl
  have he := congrArg (fun f => u ≫ f) (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
  rw [← Category.assoc, ← Category.assoc, h0, h1] at he
  exact he.symm

/-- Literal generated-field points through both genuine refined source charts. -/
def lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec (.of (lpsOriginalGeneratedFunctionFieldQ N hN)) ⟶
      lpsOriginalIntegerFrickeRefinedSchemeChart N hN b := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      exact Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN)))
  | true =>
      let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
      exact Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerFrickeLocalizedNormalChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN)))

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN b ≫
      lpsOriginalIntegerFrickeRefinedChartToGlued N hN b =
        lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false => rfl
  | true =>
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
      change Spec.map (CommRingCat.ofHom (algebraMap
          (lpsOriginalIntegerFrickeLocalizedNormalChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToFrickeLocalizedChart N hN)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN true) = _
      rw [← Category.assoc, ← Spec.map_comp]
      exact lpsOriginalIntegerNormalGeneratedFieldPoint_infinity N hN

set_option backward.isDefEq.respectTransparency false in
/-- Both local maps induce exactly the already proved Fricke action on the original field. -/
lemma lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN b ≫
      lpsOriginalIntegerFrickeRefinedChartMap N hN b =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b with
  | false =>
      let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
      change Spec.map (CommRingCat.ofHom (algebraMap
          (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroFrickePullback N hN)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false) =
        Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap
            (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
              lpsOriginalIntegerNormalGluedChartMap N hN false)
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl
  | true =>
      let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
      let := (lpsOriginalIntegerFrickeLocalizedBaseMap N hN).toAlgebra
      rw [← lpsOriginalIntegerNormalGeneratedFieldPoint_infinity N hN]
      change Spec.map (CommRingCat.ofHom (algebraMap
          (lpsOriginalIntegerFrickeLocalizedNormalChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityFrickeLocalizedPullback N hN)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN true) =
        Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap
            (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
              lpsOriginalIntegerNormalGluedChartMap N hN true)
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl

def lpsOriginalIntegerFrickeRefinedOpenCover
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalGluedScheme N hN).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (lpsOriginalIntegerFrickeRefinedSchemeChart N hN)
    (lpsOriginalIntegerFrickeRefinedChartToGlued N hN)
    (lpsOriginalIntegerFrickeRefinedChartToGlued_cover N hN)
    (lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion N hN)

lemma lpsOriginalIntegerNormalGluedScheme_separated
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalGluedScheme N hN).IsSeparated := by
  let := lpsOriginalIntegerNormalGluedToSpecZ_proper N hN
  constructor
  rw [← terminal.comp_from (lpsOriginalIntegerNormalGluedToSpecZ N hN)]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_dominant
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IsDominant (lpsOriginalIntegerNormalGeneratedFieldPoint N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := Spec (.of (lpsOriginalGeneratedFunctionFieldQ N hN))
  let f := lpsOriginalIntegerNormalGeneratedFieldPoint N hN
  have hη : f (genericPoint Y) = genericPoint X := by
    change lpsOriginalIntegerNormalGluedChartMap N hN false
      (Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) (genericPoint Y)) = _
    rw [lpsOriginalInjectiveSpecMap_generic _ _ _ Subtype.val_injective]
    exact genericPoint_eq_of_isOpenImmersion _
  rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
  rw [← isGenericPoint_def.mp (genericPoint_spec X)]
  apply closure_mono
  intro z hz
  have hz' : z = genericPoint X := Set.mem_singleton_iff.mp hz
  subst z
  exact ⟨genericPoint Y,hη⟩

set_option backward.isDefEq.respectTransparency false in
/-- The two actual local Fricke maps agree on their genuine scheme-theoretic intersection. -/
lemma lpsOriginalIntegerFrickeRefinedChartMap_overlap
    (N : ℕ) [NeZero N] (hN : 0 < N) (i j : Bool) :
    pullback.fst (lpsOriginalIntegerFrickeRefinedChartToGlued N hN i)
      (lpsOriginalIntegerFrickeRefinedChartToGlued N hN j) ≫
        lpsOriginalIntegerFrickeRefinedChartMap N hN i =
    pullback.snd (lpsOriginalIntegerFrickeRefinedChartToGlued N hN i)
      (lpsOriginalIntegerFrickeRefinedChartToGlued N hN j) ≫
        lpsOriginalIntegerFrickeRefinedChartMap N hN j := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_separated N hN
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant N hN
  let := lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion N hN i
  let := lpsOriginalIntegerFrickeRefinedChartToGlued_openImmersion N hN j
  let fi := lpsOriginalIntegerFrickeRefinedChartToGlued N hN i
  let fj := lpsOriginalIntegerFrickeRefinedChartToGlued N hN j
  let u := lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN i
  let v := lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint N hN j
  have he : u ≫ fi = v ≫ fj :=
    (lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN i).trans
      (lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN j).symm
  let t := pullback.lift u v he
  let g := pullback.fst fi fj ≫ fi
  let : IsOpenImmersion g := inferInstance
  let : IsReduced (pullback fi fj) := isReduced_of_isOpenImmersion g
  have ht : t ≫ g = lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
    simp only [t,g,pullback.lift_fst_assoc]
    exact lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN i
  let : IsDominant (t ≫ g) := by rw [ht]; infer_instance
  let : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t g
  apply ext_of_isDominant t
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target,
    lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target]

/-- Global integral Fricke, glued from the genuine rational action on a proved covering. -/
def lpsOriginalIntegerNormalGluedFricke
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedScheme N hN ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  (lpsOriginalIntegerFrickeRefinedOpenCover N hN).glueMorphisms
    (lpsOriginalIntegerFrickeRefinedChartMap N hN)
    (lpsOriginalIntegerFrickeRefinedChartMap_overlap N hN)

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGluedFricke_chart
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerFrickeRefinedChartToGlued N hN b ≫
      lpsOriginalIntegerNormalGluedFricke N hN =
        lpsOriginalIntegerFrickeRefinedChartMap N hN b :=
  (lpsOriginalIntegerFrickeRefinedOpenCover N hN).ι_glueMorphisms
    (lpsOriginalIntegerFrickeRefinedChartMap N hN)
    (lpsOriginalIntegerFrickeRefinedChartMap_overlap N hN) b

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGeneratedFieldPoint_fricke
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerNormalGeneratedFieldPoint N hN ≫
      lpsOriginalIntegerNormalGluedFricke N hN =
    Spec.map (CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN)) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_source N hN false,
    Category.assoc, lpsOriginalIntegerNormalGluedFricke_chart]
  exact lpsOriginalIntegerFrickeRefinedGeneratedFieldChartPoint_target N hN false

set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalGluedFricke_involutive
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedFricke N hN ≫ lpsOriginalIntegerNormalGluedFricke N hN =
      𝟙 (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_separated N hN
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant N hN
  apply ext_of_isDominant (lpsOriginalIntegerNormalGeneratedFieldPoint N hN)
  rw [← Category.assoc, lpsOriginalIntegerNormalGeneratedFieldPoint_fricke,
    Category.assoc, lpsOriginalIntegerNormalGeneratedFieldPoint_fricke,
    ← Category.assoc, ← Spec.map_comp, Category.comp_id]
  have he : CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN) ≫
      CommRingCat.ofHom (lpsOriginalRationalFrickePullback N hN) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact lpsOriginalRationalFrickePullback_involutive N hN
  rw [he, Spec.map_id, Category.id_comp]

/-- Actual integral Fricke scheme isomorphism, with inverse proved to be the same map. -/
def lpsOriginalIntegerNormalGluedFrickeIso
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedScheme N hN ≅
      lpsOriginalIntegerNormalGluedScheme N hN where
  hom := lpsOriginalIntegerNormalGluedFricke N hN
  inv := lpsOriginalIntegerNormalGluedFricke N hN
  hom_inv_id := lpsOriginalIntegerNormalGluedFricke_involutive N hN
  inv_hom_id := lpsOriginalIntegerNormalGluedFricke_involutive N hN

/-- The constructed global Fricke map is an actual morphism over the integer base. -/
lemma lpsOriginalIntegerNormalGluedFricke_overSpecZ
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalGluedFricke N hN ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN =
      lpsOriginalIntegerNormalGluedToSpecZ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGeneratedFieldPoint_dominant N hN
  apply ext_of_isDominant (lpsOriginalIntegerNormalGeneratedFieldPoint N hN)
  exact lpsOriginalIntegerSpecZ_hom_unique (lpsOriginalGeneratedFunctionFieldQ N hN) _ _


end
end QEC.Coding.TannerLiftedProduct

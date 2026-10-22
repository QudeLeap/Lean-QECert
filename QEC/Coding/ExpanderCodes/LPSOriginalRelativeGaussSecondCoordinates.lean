import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussNormalizationBranches
import QEC.Coding.ExpanderCodes.LPSOriginalSecondIntegerHecke

/-! # Actual second coordinates on the relative Gauss normalization

Construct actual j_p in the same generated level-Np field and in its actual relative Gauss integral closure. Identify it with the existing Fricke-conjugated second projection and prove the literal prime and level-N modular equations.

These derived internal prerequisites support the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (lines 484-486). This is an actual
affine normalization and residue calculation. Global correspondence cycles,
smooth proper reduction, Weil bounds, principal-level spectrum, and the exact
explicit arbitrary-finite-field qLDPC family remain separate obligations.
Parent issue449 remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalBivariateIntegerCoefficientEval_comp_hom
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    f.comp (Polynomial.eval₂RingHom (Int.castRingHom R) x) =
      Polynomial.eval₂RingHom (Int.castRingHom S) (f x) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp

lemma lpsOriginalIntegerPolynomial_ambientRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
        lpsOriginalJInFractionField) (lpsOriginalJNInFractionField N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  have h := congrArg (lpsOriginalGeneratedFunctionFieldQ N hN).val.toRingHom
    (lpsOriginalIntegerPolynomial_generatedRoot N hN)
  rw [Polynomial.hom_eval₂, map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRationalJElement N hN).val)
    (lpsOriginalRationalJNElement N hN).val = 0 at h
  simpa only [lpsOriginalRationalJElement_coe, lpsOriginalRationalJNElement_coe] using h

def lpsOriginalRelativeGaussSecondJField
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact lpsOriginalRationalHeckePullback N p hN hp h4N
    (lpsOriginalRationalJElement N hN)

lemma lpsOriginalRelativeGaussSecondJField_coe
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussSecondJField N p h4N hN hp).val =
      lpsOriginalJNInFractionField p hp := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRelativeGaussSecondJField, lpsOriginalRationalHeckePullback_coe,
    lpsOriginalRationalJElement_coe, lpsOriginalDilationFractionPullback_j]

lemma lpsOriginalRelativeGaussSecondJField_primeRoot
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomial p hp).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN hp)))
      (lpsOriginalRelativeGaussSecondJField N p h4N hN hp) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).val.injective
  rw [map_zero, Polynomial.hom_eval₂,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom]
  change (lpsOriginalIntegerPolynomial p hp).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN hp)).val)
    (lpsOriginalRelativeGaussSecondJField N p h4N hN hp).val = 0
  rw [lpsOriginalRationalJElement_coe, lpsOriginalRelativeGaussSecondJField_coe]
  exact lpsOriginalIntegerPolynomial_ambientRoot p hp

lemma lpsOriginalRelativeGaussBase_integerDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    apply (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val.injective
    change (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)
        (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
          (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val =
      (lpsOriginalRationalJElement (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val
    rw [lpsOriginalRationalJElement_coe,lpsOriginalRelativeGaussHeckeToGenerated_base_coe]
    change (lpsOriginalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)).val = _
    rw [lpsOriginalGaussBaseToGeneratedField_base]
    exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN

lemma lpsOriginalRelativeGaussSecondJField_integral
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    IsIntegral (LPSOriginalGaussBase p)
      (lpsOriginalRelativeGaussSecondJField N p h4N hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  refine ⟨(lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)),
    (lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _, ?_⟩
  rw [Polynomial.eval₂_map]
  change (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
    (((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)))
    (lpsOriginalRelativeGaussSecondJField N p h4N hN (Fact.out : p.Prime).pos) = 0
  rw [lpsOriginalRelativeGaussBase_integerDiagram]
  exact lpsOriginalRelativeGaussSecondJField_primeRoot N p h4N hN (Fact.out : p.Prime).pos

def lpsOriginalRelativeGaussNormalizationSecondJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  ⟨lpsOriginalRelativeGaussSecondJField N p h4N hN (Fact.out : p.Prime).pos,
    lpsOriginalRelativeGaussSecondJField_integral N p hNp h4N hN⟩

lemma lpsOriginalRelativeGaussNormalizationSecondJ_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN).val.val =
      lpsOriginalJNInFractionField p (Fact.out : p.Prime).pos :=
  lpsOriginalRelativeGaussSecondJField_coe N p h4N hN (Fact.out : p.Prime).pos

lemma lpsOriginalIntegerPolynomial_ambientSecondRoot
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
        (lpsOriginalJNInFractionField p hp))
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0 := by
  have h := congrArg (lpsOriginalDilationFractionPullback p hp).toRingHom
    (lpsOriginalIntegerPolynomial_ambientRoot N hN)
  rw [Polynomial.hom_eval₂,map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalDilationFractionPullback p hp lpsOriginalJInFractionField))
    (lpsOriginalDilationFractionPullback p hp (lpsOriginalJNInFractionField N hN)) = 0 at h
  simpa only [lpsOriginalDilationFractionPullback_j,lpsOriginalDilationFractionPullback_jN] using h

def lpsOriginalRelativeGaussNormalizationFirstJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))

lemma lpsOriginalRelativeGaussNormalizationFirstJ_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN).val.val =
      lpsOriginalJInFractionField := by
  rw [lpsOriginalRelativeGaussNormalizationFirstJ,
    lpsOriginalRelativeGaussNormalizationCoefficients_coe]
  change (lpsOriginalGaussBaseToGeneratedField N hN p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)).val = _
  rw [lpsOriginalGaussBaseToGeneratedField_base]
  exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN

lemma lpsOriginalRelativeGaussNormalization_secondPrimeRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  let f : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalHolomorphicFractionField :=
    (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val.toRingHom.comp
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos))).val.toRingHom
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply hf
  rw [Polynomial.hom_eval₂,map_zero,lpsOriginalBivariateIntegerCoefficientEval_comp_hom]
  change (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN).val.val)
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN).val.val = 0
  rw [lpsOriginalRelativeGaussNormalizationFirstJ_coe,
    lpsOriginalRelativeGaussNormalizationSecondJ_coe]
  exact lpsOriginalIntegerPolynomial_ambientRoot p (Fact.out : p.Prime).pos

lemma lpsOriginalRelativeGaussNormalization_secondLevelRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))
      (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  let f : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalHolomorphicFractionField :=
    (lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).val.toRingHom.comp
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos))).val.toRingHom
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply hf
  rw [Polynomial.hom_eval₂,map_zero,lpsOriginalBivariateIntegerCoefficientEval_comp_hom]
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom LPSOriginalHolomorphicFractionField)
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN).val.val)
    (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN).val.val = 0
  rw [lpsOriginalRelativeGaussNormalizationSecondJ_coe,
    lpsOriginalRelativeGaussNormalizationRoot_coe]
  exact lpsOriginalIntegerPolynomial_ambientSecondRoot N p hN (Fact.out : p.Prime).pos

lemma lpsOriginalRelativeGaussSecondJField_eq_secondPullback
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRelativeGaussSecondJField N p h4N hN hp =
      lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN hp) (lpsOriginalRationalJElement N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRationalFrickeLevelPullback_eq_hecke]
  rfl

end
end QEC.Coding.TannerLiftedProduct

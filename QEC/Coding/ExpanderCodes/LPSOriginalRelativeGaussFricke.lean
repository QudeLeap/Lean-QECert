import QEC.Coding.ExpanderCodes.LPSOriginalGaussFricke
import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondResidueDegrees

/-! # Fricke on the actual relative Gauss normalization

Prove stability of the literal integral closure under actual rational Fricke
from the whole coefficient diagram and integrality transitivity. Restrict it,
prove its involution and both entire coefficient exchange diagrams, then
transfer actual first-action finite generation to the distinct second action.
Derive second-map integrality using these proved diagrams and equivalences.

These derived internal prerequisites are motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486). Global correspondence cycles, smooth proper good
reduction, Weil bounds, principal-level spectrum and the exact explicit
arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449
remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussBase p →+* LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).comp
    (lpsOriginalGaussFrickeBaseMap N hN p hpN)

lemma lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap_generatedDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    (algebraMap (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))).comp
      (lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap N p hNp h4N hN hpN) =
        (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)).comp
          (algebraMap (LPSOriginalGaussBase p)
            (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · apply Subtype.ext
    change (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (lpsOriginalGaussFrickeBaseMap N hN p hpN
        (algebraMap (Polynomial ℤ) A Polynomial.X))).val.val =
      (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
        (algebraMap A L (algebraMap (Polynomial ℤ) A Polynomial.X))).val
    rw [lpsOriginalGaussFrickeBaseMap_integer, Polynomial.eval₂_X,
      lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
      lpsOriginalRelativeGaussNormalizationRoot_coe, lpsOriginalRationalFrickePullback_coe]
    have hj : (algebraMap A L (algebraMap (Polynomial ℤ) A Polynomial.X)).val =
        lpsOriginalJInFractionField := by
      change (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN
        (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)
          (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
            (algebraMap (Polynomial ℤ) A Polynomial.X)))).val = _
      rw [lpsOriginalRelativeGaussHeckeToGenerated_base_coe,
        lpsOriginalGaussAffineToGenerated_j]
    rw [hj, lpsOriginalPositiveFractionPullback_fricke_j]

lemma lpsOriginalRelativeGaussFricke_preserves_normalization
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (x : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    IsIntegral (LPSOriginalGaussBase p)
      (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  have h := IsIntegral.map_of_comp_eq
    (lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap N p hNp h4N hN hpN)
    (lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    (lpsOriginalRelativeGaussNormalizationFrickeCoefficientMap_generatedDiagram N p hNp h4N hN hpN)
    x.property
  exact isIntegral_trans (R := A) _ h

def lpsOriginalRelativeGaussNormalizationFrickePullback
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let f := lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  exact { toFun := fun x => ⟨f x.val,
            lpsOriginalRelativeGaussFricke_preserves_normalization N p hNp h4N hN hpN x⟩
          map_one' := Subtype.ext (map_one f)
          map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val)
          map_zero' := Subtype.ext (map_zero f)
          map_add' := fun x y => Subtype.ext (map_add f x.val y.val) }

lemma lpsOriginalRelativeGaussNormalizationFrickePullback_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (x : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN x).val =
      lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val := by
  rfl

lemma lpsOriginalRelativeGaussNormalizationFrickePullback_involutive
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Function.Involutive (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro x
  apply Subtype.ext
  exact lpsOriginalRationalFrickePullback_involutive (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val

def lpsOriginalRelativeGaussNormalizationFrickeRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN ≃+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  RingEquiv.ofBijective (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationFrickePullback_involutive N p hNp h4N hN hpN).bijective

lemma lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN).comp
      (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) =
        (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).comp
          (lpsOriginalGaussFrickeOrderMap N hN p hpN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp only [RingHom.comp_apply]
      apply Subtype.ext
      apply Subtype.ext
      rw [lpsOriginalGaussFrickeOrderMap_j,
        lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
        lpsOriginalRelativeGaussNormalizationRoot_coe,
        lpsOriginalRelativeGaussNormalizationFrickePullback_coe,
        lpsOriginalRationalFrickePullback_coe,
        lpsOriginalRelativeGaussNormalizationCoefficients_coe,
        lpsOriginalGaussAffineToGenerated_j,
        lpsOriginalPositiveFractionPullback_fricke_j]
  · simp only [RingHom.comp_apply]
    apply Subtype.ext
    apply Subtype.ext
    rw [lpsOriginalGaussFrickeOrderMap_root,
      lpsOriginalRelativeGaussNormalizationSecondOrderMap_j,
      lpsOriginalRelativeGaussNormalizationSecondJ_coe,
      lpsOriginalRelativeGaussNormalizationFrickePullback_coe,
      lpsOriginalRationalFrickePullback_coe,
      lpsOriginalRelativeGaussNormalizationCoefficients_coe,
      lpsOriginalGaussAffineToGenerated_root,
      lpsOriginalPositiveFractionPullback_fricke_product_jN]

lemma lpsOriginalRelativeGaussNormalizationFrickePullback_comp_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN).comp
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) =
        (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).comp
          (lpsOriginalGaussFrickeOrderMap N hN p hpN) := by
  apply RingHom.ext
  intro c
  have h := congrArg (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN)
    (RingHom.congr_fun
      (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN)
      (lpsOriginalGaussFrickeOrderMap N hN p hpN c))
  simp only [RingHom.comp_apply] at h ⊢
  have hR : lpsOriginalGaussFrickeOrderMap N hN p hpN
      (lpsOriginalGaussFrickeOrderMap N hN p hpN c) = c :=
    RingHom.congr_fun (lpsOriginalGaussFrickeOrderMap_squared N hN p hpN) c
  rw [lpsOriginalRelativeGaussNormalizationFrickePullback_involutive, hR] at h
  exact h.symm

lemma lpsOriginalRelativeGaussNormalization_firstFinite
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let : Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussHeckeOrder N hN p) :=
    (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p).finite_adjoinRoot
  exact Module.Finite.equiv
    (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN).toLinearEquiv

lemma lpsOriginalRelativeGaussNormalization_secondFinite
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  refine @Module.Finite.of_equiv_equiv R C R C _ _ _ _
    (lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN)
    (lpsOriginalGaussFrickeRingEquiv N hN p hpN)
    (lpsOriginalRelativeGaussNormalizationFrickeRingEquiv N p hNp h4N hN hpN)
    ?_ (lpsOriginalRelativeGaussNormalization_firstFinite N p hNp h4N hN hpN)
  exact (lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first N p hNp h4N hN hpN).symm

lemma lpsOriginalRelativeGaussNormalizationSecondOrderMap_isIntegral
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).IsIntegral := by
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_secondFinite N p hNp h4N hN hpN
  exact Algebra.IsIntegral.isIntegral

end
end QEC.Coding.TannerLiftedProduct

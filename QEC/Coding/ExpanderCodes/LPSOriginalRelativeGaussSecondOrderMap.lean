import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondUnits

/-! # The genuine second Gauss order map

Lift the actual second coordinate through the whole Gauss localization and level-N AdjoinRoot relation. Prove both full branch projection diagrams, the original Fricke-conjugated pullback diagram, and injectivity.

These derived internal prerequisites are motivated by pinned PK22 main.tex ex:Xpq (lines 484-486). Global correspondence cycles, smooth proper good reduction, Weil bounds, principal-level spectrum and the exact explicit arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449 remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalRelativeGaussNormalizationSecondBaseMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussBase p →+* LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  exact IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl) (S := LPSOriginalGaussBase p)
    (g := Polynomial.eval₂RingHom (Int.castRingHom _)
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))
    (fun s => lpsOriginalRelativeGaussNormalization_secondInteger_isUnit
      N p hNp h4N hN hpN s s.property)

lemma lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (P : Polynomial ℤ) :
    lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P) =
      P.eval₂ (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  dsimp only [lpsOriginalRelativeGaussNormalizationSecondBaseMap]
  exact IsLocalization.lift_eq _ P

lemma lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer_comp
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) := by
  apply RingHom.ext
  intro P
  exact lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer N p hNp h4N hN hpN P

lemma lpsOriginalRelativeGaussNormalizationSecondBaseMap_levelRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussPolynomial N hN p).eval₂
      (lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN)
      (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN) = 0 := by
  change ((lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).eval₂ _ _ = 0
  rw [Polynomial.eval₂_map,
    lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer_comp]
  exact lpsOriginalRelativeGaussNormalization_secondLevelRoot N p hNp h4N hN hpN

def lpsOriginalRelativeGaussNormalizationSecondOrderMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p →+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  AdjoinRoot.lift (lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationSecondBaseMap_levelRoot N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) =
      lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN :=
  AdjoinRoot.lift_root _

lemma lpsOriginalRelativeGaussNormalizationSecondOrderMap_base
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (x : LPSOriginalGaussBase p) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p) x) =
      lpsOriginalRelativeGaussNormalizationSecondBaseMap N p hNp h4N hN hpN x :=
  AdjoinRoot.lift_of _

lemma lpsOriginalRelativeGaussNormalizationSecondOrderMap_j
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) =
      lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN := by
  rw [lpsOriginalRelativeGaussNormalizationSecondOrderMap_base,
    lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer,Polynomial.eval₂_X]

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) =
      (frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p).comp (Ideal.Quotient.mk q) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply,lpsOriginalRelativeGaussNormalizationSecondOrderMap_base]
    rw [lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer]
    have hP := RingHom.congr_fun (lpsOriginalGaussMaximalResidue_integerBaseEval N hN p q) P
    change Ideal.Quotient.mk q
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P)) = _ at hP
    rw [hP]
    change _ = (P.eval₂ (Int.castRingHom K) (lpsOriginalGaussMaximalResidueJ N hN p q))^p
    rw [lpsOriginalIntegerPolynomial_eval₂_hom,
      lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondJ,
      ← lpsOriginalIntegerPolynomial_eval₂_frobenius]
  · simp only [RingHom.comp_apply,lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
      lpsOriginalRelativeGaussNormalizationLinearBranchMap_root,frobenius_def]
    rfl

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) =
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm.toRingHom.comp
        (Ideal.Quotient.mk q) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply,lpsOriginalRelativeGaussNormalizationSecondOrderMap_base]
    rw [lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer]
    have hP := RingHom.congr_fun (lpsOriginalGaussMaximalResidue_integerBaseEval N hN p q) P
    change Ideal.Quotient.mk q
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P)) = _ at hP
    rw [hP,Polynomial.coe_eval₂RingHom,lpsOriginalIntegerPolynomial_eval₂_hom,
      lpsOriginalIntegerPolynomial_eval₂_hom]
    have he : (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv
        N p hNp h4N hN hpN q).symm.toRingHom (lpsOriginalGaussMaximalResidueJ N hN p q) =
        lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
          (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) :=
      lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j N p hNp h4N hN hpN q
    rw [he]
  · simp only [RingHom.comp_apply,lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
      lpsOriginalRelativeGaussNormalizationInseparableBranchMap_root]
    exact (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_jN
      N p hNp h4N hN hpN q).symm

lemma lpsOriginalGaussAffineToGenerated_j
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))).val =
      lpsOriginalJInFractionField := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change (lpsOriginalGaussBaseToGeneratedField N hN p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)).val = _
  rw [lpsOriginalGaussBaseToGeneratedField_base]
  exact lpsOriginalIntegerBaseToGeneratedField_X_coe N hN

lemma lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ a : LPSOriginalGaussAffineOrder N hN p,
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN a).val =
        lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)
          (lpsOriginalGaussAffineToGenerated N hN p a) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let v : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+* L :=
    (integralClosure A L).val.toRingHom
  let f := v.comp (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN)
  let g := (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N).comp
    (lpsOriginalGaussAffineToGenerated N hN p)
  have h : f = g := by
    apply AdjoinRoot.ringHom_ext
    · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
      apply Polynomial.ringHom_ext
      · intro z
        simp
      · apply Subtype.ext
        change (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
          (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
            (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))).val.val =
          (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N
            (lpsOriginalGaussAffineToGenerated N hN p
              (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
                (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val
        rw [lpsOriginalRelativeGaussNormalizationSecondOrderMap_j,
          lpsOriginalRelativeGaussNormalizationSecondJ_coe,
          lpsOriginalRationalHeckePullback_coe,lpsOriginalGaussAffineToGenerated_j,
          lpsOriginalDilationFractionPullback_j]
    · apply Subtype.ext
      change (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val =
        (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N
          (lpsOriginalGaussAffineToGenerated N hN p
            (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))).val
      rw [lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
        lpsOriginalRelativeGaussNormalizationRoot_coe,
        lpsOriginalRationalHeckePullback_coe,lpsOriginalGaussAffineToGenerated_root,
        lpsOriginalDilationFractionPullback_jN]
  intro a
  rw [lpsOriginalRationalFrickeLevelPullback_eq_hecke]
  exact RingHom.congr_fun h a

lemma lpsOriginalRelativeGaussNormalizationSecondOrderMap_injective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalGaussAffineOrder_domain N hN p
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let := lpsOriginalGaussAffineGenerated_isFractionRing N hN p
  have hg : Function.Injective (lpsOriginalGaussAffineToGenerated N hN p) :=
    IsFractionRing.injective (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN)
  intro a b hab
  apply hg
  apply (lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).injective
  rw [← lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
      N p hNp h4N hN hpN a,
    ← lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
      N p hNp h4N hN hpN b,hab]

end
end QEC.Coding.TannerLiftedProduct

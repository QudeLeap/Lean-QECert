import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussFrobeniusDescent

/-! # Primitive denominators at the actual second Gauss coordinate

Prove actual primitive polynomial denominators are units on both normalization branches and in the entire normalization, using integral coefficients and the complete maximal-prime classification.

These derived internal prerequisites are motivated by pinned PK22 main.tex ex:Xpq (lines 484-486). Global correspondence cycles, smooth proper good reduction, Weil bounds, principal-level spectrum and the exact explicit arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449 remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalIntegerPolynomial_eval₂_hom
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P : Polynomial ℤ) (x : R) :
    f (P.eval₂ (Int.castRingHom R) x) = P.eval₂ (Int.castRingHom S) (f x) := by
  rw [Polynomial.hom_eval₂]
  have hc : f.comp (Int.castRingHom R) = Int.castRingHom S := by
    ext z
    simp
  rw [hc]

lemma lpsOriginalIntegerPolynomial_eval₂_frobenius
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Polynomial ℤ) (x : K) :
    (P.eval₂ (Int.castRingHom K) x)^p = P.eval₂ (Int.castRingHom K) (x^p) := by
  simpa only [frobenius_def] using
    lpsOriginalIntegerPolynomial_eval₂_hom (frobenius K p) P x

lemma lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p ⧸ q))
      (lpsOriginalGaussMaximalResidueJ N hN p q)) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let g : LPSOriginalGaussBase p →+* K :=
    (Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))
  let s : (lpsOriginalGaussPrime p).primeCompl := ⟨P,hP⟩
  have h : IsUnit (g (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) s)) :=
    (IsLocalization.map_units (LPSOriginalGaussBase p) s).map g
  change IsUnit ((g.comp (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))) P) at h
  rw [lpsOriginalGaussMaximalResidue_integerBaseEval] at h
  exact h

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondInteger_isUnit
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (P.eval₂ (Int.castRingHom (LPSOriginalRelativeGaussNormalization N p hNp h4N hN))
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  rw [lpsOriginalIntegerPolynomial_eval₂_hom,
    lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondJ,
    ← lpsOriginalIntegerPolynomial_eval₂_frobenius]
  exact (lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit N hN p q P hP).pow p

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondInteger_isUnit
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (P.eval₂ (Int.castRingHom (LPSOriginalRelativeGaussNormalization N p hNp h4N hN))
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  have h := (lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit N hN p q P hP).map
    e.symm.toRingHom
  rw [lpsOriginalIntegerPolynomial_eval₂_hom] at h
  have he : e.symm.toRingHom (lpsOriginalGaussMaximalResidueJ N hN p q) =
      lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) :=
    lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j N p hNp h4N hN hpN q
  rw [he] at h
  rw [lpsOriginalIntegerPolynomial_eval₂_hom]
  exact h

lemma lpsOriginalMapKernelCompositionEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (e : R ≃+* A) (f : A →+* B) :
    (RingHom.ker (f.comp e.toRingHom)).map e = RingHom.ker f := by
  have h : RingHom.ker (f.comp e.toRingHom) = (RingHom.ker f).comap e := by
    ext x
    rfl
  rw [h]
  exact (RingHom.ker f).map_comap_eq_self_of_equiv e

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_equiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).toRingHom =
      lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q := by
  apply RingHom.ext
  intro x
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN x))).1 =
    (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q (Ideal.Quotient.mk _ x)).1
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk]

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_equiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).toRingHom =
      lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q := by
  apply RingHom.ext
  intro x
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN x))).2 =
    (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q (Ideal.Quotient.mk _ x)).2
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk]

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    RingHom.ker (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) =
      LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q := by
  change RingHom.ker (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) =
    (RingHom.ker (lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q)).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
  rw [← lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_equiv N p hNp h4N hN hpN q]
  exact (lpsOriginalMapKernelCompositionEquiv
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q)).symm

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    RingHom.ker (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q) =
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q := by
  change RingHom.ker (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q) =
    (RingHom.ker (lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q)).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
  rw [← lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_equiv N p hNp h4N hN hpN q]
  exact (lpsOriginalMapKernelCompositionEquiv
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q)).symm

lemma lpsOriginalRelativeGaussNormalizationCoefficients_isIntegral
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).IsIntegral := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let : Module.Finite R B := (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p).finite_adjoinRoot
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let e := lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN
  let : Algebra.IsIntegral R C := e.isIntegral_iff.mp inferInstance
  exact Algebra.IsIntegral.isIntegral

lemma lpsOriginalRelativeGaussNormalization_secondInteger_isUnit
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalRelativeGaussNormalization N p hNp h4N hN))
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)) := by
  classical
  let C := LPSOriginalRelativeGaussNormalization N p hNp h4N hN
  let x : C := P.eval₂ (Int.castRingHom C)
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)
  by_contra hx
  have hi : Ideal.span ({x} : Set C) ≠ ⊤ := by
    intro hi
    exact hx (Ideal.span_singleton_eq_top.mp hi)
  obtain ⟨m,hm,hxm⟩ := Ideal.exists_le_maximal (Ideal.span ({x} : Set C)) hi
  let : m.IsMaximal := hm
  let q := m.comap (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationCoefficients_isIntegral N p hNp h4N hN hpN) m
  have hmem : x ∈ m := hxm (Ideal.mem_span_singleton_self x)
  rcases lpsOriginalRelativeGaussNormalizationPrimeOver_classification
    N p hNp h4N hN hpN q m rfl with hlin | hins
  · let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let : Field K := Ideal.Quotient.field q
    have hu := lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondInteger_isUnit
      N p hNp h4N hN hpN q P hP
    rw [hlin,← lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker] at hmem
    exact hu.ne_zero (RingHom.mem_ker.mp hmem)
  · let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
    have hu := lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondInteger_isUnit
      N p hNp h4N hN hpN q P hP
    rw [hins,← lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker] at hmem
    exact hu.ne_zero (RingHom.mem_ker.mp hmem)

end
end QEC.Coding.TannerLiftedProduct

import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondOrderMap

/-! # The actual lower Gauss Fricke involution

Prove primitive denominators are units at the actual native level root from
residue transcendence. Lift the whole localization and proved dual modular
relation to the order involution exchanging j and j_N. Derive the ring
equivalence and entire actual generated-field diagram.

These derived internal prerequisites are motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486). Global correspondence cycles, smooth proper good
reduction, Weil bounds, principal-level spectrum and the exact explicit
arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449
remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalGaussMaximalResidueJN_integerPolynomial_isUnit
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p ⧸ q))
      (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  let f : Polynomial (ZMod p) →+* K :=
    Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q)
  have hi : Function.Injective f := transcendental_iff_injective.mp
    (lpsOriginalGaussMaximalResidueJN_transcendental N hN p hpN q)
  have hn : P.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h
    exact hP h
  have hx : f (P.map (Int.castRingHom (ZMod p))) =
      P.eval₂ (Int.castRingHom K) (lpsOriginalGaussMaximalResidueJN N hN p q) := by
    change (P.map (Int.castRingHom (ZMod p))).eval₂
      (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q) = _
    rw [Polynomial.eval₂_map]
    have hc : (lpsOriginalGaussMaximalResidueConstantMap N hN p q).comp
        (Int.castRingHom (ZMod p)) = Int.castRingHom K := by
      ext z
      simp
    rw [hc]
  apply isUnit_iff_ne_zero.mpr
  rw [← hx]
  intro h
  exact hn (hi (h.trans (map_zero f).symm))

lemma lpsOriginalGaussAffineOrder_rootInteger_isUnit
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p))
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))) := by
  by_contra hu
  obtain ⟨q, hq, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  let : q.IsMaximal := hq
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  have hunit : IsUnit (Ideal.Quotient.mk q
      (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p))
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))) := by
    rw [lpsOriginalIntegerPolynomial_eval₂_hom]
    exact lpsOriginalGaussMaximalResidueJN_integerPolynomial_isUnit N hN p hpN q P hP
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

def lpsOriginalGaussFrickeBaseMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    LPSOriginalGaussBase p →+* LPSOriginalGaussAffineOrder N hN p := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  exact IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl) (S := LPSOriginalGaussBase p)
    (g := Polynomial.eval₂RingHom (Int.castRingHom _) (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))
    (fun s => lpsOriginalGaussAffineOrder_rootInteger_isUnit N hN p hpN s s.property)

lemma lpsOriginalGaussFrickeBaseMap_integer
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (P : Polynomial ℤ) :
    lpsOriginalGaussFrickeBaseMap N hN p hpN
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P) =
        P.eval₂ (Int.castRingHom _) (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  dsimp only [lpsOriginalGaussFrickeBaseMap]
  exact IsLocalization.lift_eq _ P

lemma lpsOriginalGaussFrickeBaseMap_integer_comp
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussFrickeBaseMap N hN p hpN).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
        Polynomial.eval₂RingHom (Int.castRingHom _) (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) := by
  apply RingHom.ext
  intro P
  exact lpsOriginalGaussFrickeBaseMap_integer N hN p hpN P

lemma lpsOriginalGaussFrickeBaseMap_levelRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussPolynomial N hN p).eval₂
      (lpsOriginalGaussFrickeBaseMap N hN p hpN)
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = 0 := by
  change ((lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).eval₂ _ _ = 0
  rw [Polynomial.eval₂_map, lpsOriginalGaussFrickeBaseMap_integer_comp]
  exact lpsOriginalIntegerPolynomial_gaussDualRoot N hN p hpN

def lpsOriginalGaussFrickeOrderMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p →+* LPSOriginalGaussAffineOrder N hN p :=
  AdjoinRoot.lift (lpsOriginalGaussFrickeBaseMap N hN p hpN)
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) (lpsOriginalGaussFrickeBaseMap_levelRoot N hN p hpN)

lemma lpsOriginalGaussFrickeOrderMap_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) =
      AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) :=
  AdjoinRoot.lift_root _

lemma lpsOriginalGaussFrickeOrderMap_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (x : LPSOriginalGaussBase p) :
    lpsOriginalGaussFrickeOrderMap N hN p hpN
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p) x) =
        lpsOriginalGaussFrickeBaseMap N hN p hpN x :=
  AdjoinRoot.lift_of _

lemma lpsOriginalGaussFrickeOrderMap_j
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by
  rw [lpsOriginalGaussFrickeOrderMap_base,
    lpsOriginalGaussFrickeBaseMap_integer, Polynomial.eval₂_X]

lemma lpsOriginalGaussFrickeOrderMap_squared
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalGaussFrickeOrderMap N hN p hpN).comp
      (lpsOriginalGaussFrickeOrderMap N hN p hpN) =
        RingHom.id (LPSOriginalGaussAffineOrder N hN p) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · change lpsOriginalGaussFrickeOrderMap N hN p hpN
        (lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))) = AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)
      rw [lpsOriginalGaussFrickeOrderMap_j, lpsOriginalGaussFrickeOrderMap_root]
  · change lpsOriginalGaussFrickeOrderMap N hN p hpN
      (lpsOriginalGaussFrickeOrderMap N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))) = AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)
    rw [lpsOriginalGaussFrickeOrderMap_root, lpsOriginalGaussFrickeOrderMap_j]

def lpsOriginalGaussFrickeRingEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p ≃+* LPSOriginalGaussAffineOrder N hN p := by
  have h : Function.Involutive (lpsOriginalGaussFrickeOrderMap N hN p hpN) := by
    intro x
    exact congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+* LPSOriginalGaussAffineOrder N hN p => f x)
      (lpsOriginalGaussFrickeOrderMap_squared N hN p hpN)
  exact RingEquiv.ofBijective (lpsOriginalGaussFrickeOrderMap N hN p hpN) h.bijective

lemma lpsOriginalGaussFrickeRingEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeRingEquiv N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) = AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) :=
  lpsOriginalGaussFrickeOrderMap_root N hN p hpN

lemma lpsOriginalGaussFrickeRingEquiv_j
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeRingEquiv N hN p hpN (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) = AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) :=
  lpsOriginalGaussFrickeOrderMap_j N hN p hpN

lemma lpsOriginalGaussFrickeOrderMap_generatedDiagram
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p).comp
      (lpsOriginalGaussFrickeOrderMap N hN p hpN) =
        (lpsOriginalRationalFrickePullback N hN).comp
          (lpsOriginalGaussAffineToGenerated N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · apply Subtype.ext
      change (lpsOriginalGaussAffineToGenerated N hN p
        (lpsOriginalGaussFrickeOrderMap N hN p hpN
          (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
            (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val =
        (lpsOriginalRationalFrickePullback N hN
          (lpsOriginalGaussAffineToGenerated N hN p
            (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
              (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val
      rw [lpsOriginalGaussFrickeOrderMap_j, lpsOriginalGaussAffineToGenerated_root,
        lpsOriginalRationalFrickePullback_coe, lpsOriginalGaussAffineToGenerated_j,
        lpsOriginalPositiveFractionPullback_fricke_j]
  · apply Subtype.ext
    change (lpsOriginalGaussAffineToGenerated N hN p
      (lpsOriginalGaussFrickeOrderMap N hN p hpN
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))).val =
      (lpsOriginalRationalFrickePullback N hN
        (lpsOriginalGaussAffineToGenerated N hN p
          (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))).val
    rw [lpsOriginalGaussFrickeOrderMap_root, lpsOriginalGaussAffineToGenerated_j,
      lpsOriginalRationalFrickePullback_coe, lpsOriginalGaussAffineToGenerated_root,
      lpsOriginalPositiveFractionPullback_fricke_jN]

end
end QEC.Coding.TannerLiftedProduct

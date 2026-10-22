import QEC.Coding.ExpanderCodes.LPSOriginalGaussResidueCoordinate

/-! # Actual first residue coordinate

Prove generation and separability of the entire actual maximal Gauss residue over F_p(j), and prove that actual j has no pth root there. These are used by both branch coordinate proofs.

These derived internal prerequisites support the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (lines 484-486). This is an actual
affine normalization and residue calculation. Global correspondence cycles,
smooth proper reduction, Weil bounds, principal-level spectrum, and the exact
explicit arbitrary-finite-field qLDPC family remain separate obligations.
Parent issue449 remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

lemma lpsOriginalGaussMaximalResidueFractionMap_X
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalGaussMaximalResidueFractionMap N hN p q
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) =
      lpsOriginalGaussMaximalResidueJ N hN p q := by
  have h := congrArg (fun f : Polynomial (ZMod p) →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) => f Polynomial.X)
    (lpsOriginalGaussMaximalResidueFractionMap_polynomial N hN p q)
  simpa only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using h

lemma lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueFractionMap N hN p q).comp
      ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  rw [← RingHom.comp_assoc,lpsOriginalGaussMaximalResidueFractionMap_polynomial]
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp

lemma lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q))
      (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 := by
  have h := congrArg (Ideal.Quotient.mk q)
    (AdjoinRoot.eval₂_root (lpsOriginalGaussPolynomial N hN p))
  rw [Polynomial.hom_eval₂,map_zero] at h
  change ((lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).eval₂
    ((Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)))
    (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 at h
  rw [Polynomial.eval₂_map] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (((Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)))
    (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 at h
  rw [lpsOriginalGaussMaximalResidue_integerBaseEval] at h
  exact h

lemma lpsOriginalModularPolynomialModFraction_actualResidueRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalModularPolynomialModFraction N hN p).eval₂
      (lpsOriginalGaussMaximalResidueFractionMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 := by
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.eval₂_map,
    lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient]
  exact lpsOriginalIntegerPolynomial_gaussMaximalResidueRoot N hN p q

lemma lpsOriginalGaussMaximalResidueJN_separable_overJ
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    IsSeparable (FractionRing (Polynomial (ZMod p)))
      (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  have hr := lpsOriginalModularPolynomialModFraction_actualResidueRoot N hN p q
  change Polynomial.aeval (lpsOriginalGaussMaximalResidueJN N hN p q)
    (lpsOriginalModularPolynomialModFraction N hN p) = 0 at hr
  exact (lpsOriginalModularPolynomialModFraction_separable N hN p hpN).of_dvd
    (minpoly.dvd _ _ hr)

lemma lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
      {lpsOriginalGaussMaximalResidueJN N hN p q} = ⊤ := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  let L := IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
    {lpsOriginalGaussMaximalResidueJN N hN p q}
  have hn : lpsOriginalGaussMaximalResidueJN N hN p q ∈ L :=
    IntermediateField.mem_adjoin_simple_self _ _
  have hj : lpsOriginalGaussMaximalResidueJ N hN p q ∈ L := by
    rw [← lpsOriginalGaussMaximalResidueFractionMap_X N hN p q]
    exact L.algebraMap_mem _
  let g : LPSOriginalGaussBase p →+* K :=
    (Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))
  have hc : ∀ a : LPSOriginalGaussBase p, g a ∈ L.toSubfield := by
    intro a
    apply lpsOriginalLocalization_subfield_mem (Polynomial ℤ) (LPSOriginalGaussBase p)
      K (lpsOriginalGaussPrime p).primeCompl g L.toSubfield _ a
    intro P
    change (g.comp (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))) P ∈ L.toSubfield
    rw [lpsOriginalGaussMaximalResidue_integerBaseEval]
    exact lpsOriginalSubfield_eval₂_mem ℤ K (Int.castRingHom K) L.toSubfield
      (fun z => L.toSubfield.intCast_mem z) _ hj P
  have hs : L.toSubfield = ⊤ :=
    lpsOriginalAdjoinRoot_surjective_subfield_eq_top (LPSOriginalGaussBase p) K
      (lpsOriginalGaussPolynomial N hN p) (Ideal.Quotient.mk q)
      (Ideal.Quotient.mk_surjective) L.toSubfield hc hn
  apply IntermediateField.ext
  intro x
  change x ∈ L.toSubfield ↔ x ∈ (⊤ : IntermediateField (FractionRing (Polynomial (ZMod p))) K)
  rw [hs]
  simp

lemma lpsOriginalGaussMaximalResidue_separable_overJ
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
        {lpsOriginalGaussMaximalResidueJN N hN p q}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr
      (lpsOriginalGaussMaximalResidueJN_separable_overJ N hN p hpN q)
  let e := (IntermediateField.equivOfEq
    (lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top N hN p q)).trans
    IntermediateField.topEquiv
  exact Algebra.IsSeparable.of_algHom
    (FractionRing (Polynomial (ZMod p))) _ e.symm.toAlgHom

lemma lpsOriginalGaussMaximalResidueJ_not_prime_power
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    u^p ≠ lpsOriginalGaussMaximalResidueJ N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p))) K :=
    lpsOriginalGaussMaximalResidue_separable_overJ N hN p hpN q
  have h := QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
    (FractionRing (Polynomial (ZMod p))) K p
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X)
    (lpsOriginalFractionCoordinate_not_prime_power (ZMod p) p (Fact.out : p.Prime)) u
  change u^p ≠ lpsOriginalGaussMaximalResidueFractionMap N hN p q
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) at h
  rw [lpsOriginalGaussMaximalResidueFractionMap_X] at h
  exact h

end
end QEC.Coding.TannerLiftedProduct

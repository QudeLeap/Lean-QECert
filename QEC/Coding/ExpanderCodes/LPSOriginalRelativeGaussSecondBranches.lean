import QEC.Coding.ExpanderCodes.LPSOriginalGaussFirstResidueCoordinate
import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondCoordinates

/-! # Actual Frobenius coordinates of both Gauss branches

Identify the two actual quotient projections. Prove j_p=j^p on the degree-one branch and j_p^p=j on the degree-p branch; rule out the wrong alternative using separability of the Frobenius-mapped level-N modular polynomial and the genuine purely inseparable branch field.

These derived internal prerequisites support the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (lines 484-486). This is an actual
affine normalization and residue calculation. Global correspondence cycles,
smooth proper reduction, Weil bounds, principal-level spectrum, and the exact
explicit arbitrary-finite-field qLDPC family remain separate obligations.
Parent issue449 remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalRelativeGaussNormalizationLinearBranchMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (RingHom.fst _ _).comp
    ((lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (Ideal.Quotient.mk _))

def lpsOriginalRelativeGaussNormalizationInseparableBranchMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+*
      LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (RingHom.snd _ _).comp
    ((lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (Ideal.Quotient.mk _))

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_firstJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) =
      lpsOriginalGaussMaximalResidueJ N hN p q := by
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))).1 = _
  rw [lpsOriginalRelativeGaussNormalizationFirstJ,
    lpsOriginalRelativeGaussNormalizationFiberEquiv_base]
  rfl

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) =
      AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))).2 = _
  rw [lpsOriginalRelativeGaussNormalizationFirstJ,
    lpsOriginalRelativeGaussNormalizationFiberEquiv_base]
  rfl

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_root
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN) =
      AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN))).2 = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_root]

lemma lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (f : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+* A) :
    f (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) =
        (f (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN))^p ∨
      (f (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))^p =
        f (lpsOriginalRelativeGaussNormalizationFirstJ N p hNp h4N hN hpN) := by
  have h := congrArg f
    (lpsOriginalRelativeGaussNormalization_secondPrimeRoot N p hNp h4N hN hpN)
  rw [Polynomial.hom_eval₂,map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  exact (lpsOriginalPrimeIntegerPolynomial_charPRoot_iff p A _ _).mp h

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) =
      (lpsOriginalGaussMaximalResidueJ N hN p q)^p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  have h := lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
    N p hNp h4N hN hpN K
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q)
  rw [lpsOriginalRelativeGaussNormalizationLinearBranchMap_firstJ] at h
  rcases h with h | h
  · exact h
  · exact False.elim ((lpsOriginalGaussMaximalResidueJ_not_prime_power N hN p hpN q _) h)

lemma lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    ((lpsOriginalIntegerPolynomial N hN).map
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        ((lpsOriginalGaussMaximalResidueJ N hN p q)^p))).Separable := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  have h := (lpsOriginalModularPolynomialModFraction_separable N hN p hpN).map
    (f := lpsOriginalGaussMaximalResidueFractionMap N hN p q)
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.map_map,
    lpsOriginalGaussMaximalResidueFractionMap_integerCoefficient] at h
  have hf := h.map (f := frobenius K p)
  rw [Polynomial.map_map,lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at hf
  exact hf

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ_not_frobenius
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) ≠
      (AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
        (lpsOriginalGaussMaximalResidueJ N hN p q))^p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let : IsPurelyInseparable K T :=
    lpsOriginalRelativeGaussInseparableBranch_purelyInseparable N hN p hpN q
  let f := lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
  let j := lpsOriginalGaussMaximalResidueJ N hN p q
  let jN := lpsOriginalGaussMaximalResidueJN N hN p q
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C jN
  let Y : T := AdjoinRoot.root Q
  intro heq
  have h := congrArg f
    (lpsOriginalRelativeGaussNormalization_secondLevelRoot N p hNp h4N hN hpN)
  rw [Polynomial.hom_eval₂,map_zero,
    lpsOriginalBivariateIntegerCoefficientEval_comp_hom] at h
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom T) (f
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)))
    (f (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)) = 0 at h
  rw [heq,lpsOriginalRelativeGaussNormalizationInseparableBranchMap_root] at h
  have hr : Polynomial.aeval Y
      ((lpsOriginalIntegerPolynomial N hN).map
        (Polynomial.eval₂RingHom (Int.castRingHom K) (j^p))) = 0 := by
    rw [Polynomial.aeval_def,Polynomial.eval₂_map,
      lpsOriginalBivariateIntegerCoefficientEval_comp_hom,map_pow]
    exact h
  have hs : IsSeparable K Y :=
    (lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable N hN p hpN q).of_dvd
      (minpoly.dvd K Y hr)
  obtain ⟨u,hu⟩ := IsPurelyInseparable.inseparable K Y hs
  have he : algebraMap K T (u^p) = algebraMap K T jN := by
    rw [map_pow,hu]
    exact lpsOriginalAdjoinRootPrimePower_root p jN
  exact lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q u
    ((algebraMap K T).injective he)

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN))^p =
      AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let : Algebra (ZMod p) T :=
    ((algebraMap K T).comp (lpsOriginalGaussMaximalResidueConstantMap N hN p q)).toAlgebra
  have h := lpsOriginalRelativeGaussNormalization_secondResidueAlternatives
    N p hNp h4N hN hpN T
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q)
  rw [lpsOriginalRelativeGaussNormalizationInseparableBranchMap_firstJ] at h
  rcases h with h | h
  · exact False.elim ((lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ_not_frobenius
      N p hNp h4N hN hpN q) h)
  · exact h

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_root
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN) =
      (lpsOriginalGaussMaximalResidueJN N hN p q)^p := by
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN))).1 = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_root]

end
end QEC.Coding.TannerLiftedProduct

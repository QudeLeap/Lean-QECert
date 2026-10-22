import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondBranches

/-! # Actual Frobenius descent of the relative Gauss branch

Construct the coefficient-Frobenius/root descent on the genuine purely
inseparable branch, prove it bijective using actual residue generators, and
identify its inverse on both actual second coordinates. Prove those coordinates
generate the entire branch. Keep the original coefficient action on the branch
and explicitly give the target the Frobenius algebra/module action, so the
transported finrank is p rather than the ordinary self-field rank.

These derived internal prerequisites are motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486), not separate source claims. They support the subsequent
reduction of the genuine second Gauss projection and correspondence-cycle
identity. Global correspondence cycles, smooth proper good reduction, Weil
bounds, principal-level spectrum and the exact explicit arbitrary-finite-field
qLDPC family remain separate obligations. Parent issue449 remains OPEN;
pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalAdjoinRootPrimePowerFrobeniusDescent
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) :
    AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a) →+* K :=
  AdjoinRoot.lift (frobenius K p) a (by simp [frobenius_def])

lemma lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a u : K) :
    lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a
      (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p - Polynomial.C a) u) = u^p := by
  simp [lpsOriginalAdjoinRootPrimePowerFrobeniusDescent, AdjoinRoot.lift_of, frobenius_def]

lemma lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_root
    {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) :
    lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a
      (AdjoinRoot.root ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) = a := by
  simp [lpsOriginalAdjoinRootPrimePowerFrobeniusDescent, AdjoinRoot.lift_root]

lemma lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Fact (Irreducible ((Polynomial.X : Polynomial K)^p - Polynomial.C a))]
    (x : AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) :
    AdjoinRoot.of ((Polynomial.X : Polynomial K)^p - Polynomial.C a)
      (lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a x) = x^p := by
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
  let T := AdjoinRoot Q
  let : CharP T p := charP_of_injective_algebraMap (algebraMap K T).injective p
  have hroot := lpsOriginalAdjoinRootPrimePower_root p a
  have hcomm : (AdjoinRoot.of Q).comp (frobenius K p) =
      (frobenius T p).comp (AdjoinRoot.of Q) := by
    ext c
    simp [frobenius_def]
  induction x using AdjoinRoot.induction_on with
  | ih f =>
    rw [lpsOriginalAdjoinRootPrimePowerFrobeniusDescent, AdjoinRoot.lift_mk]
    calc
      AdjoinRoot.of Q (f.eval₂ (frobenius K p) a) =
          f.eval₂ ((AdjoinRoot.of Q).comp (frobenius K p)) (AdjoinRoot.of Q a) :=
        Polynomial.hom_eval₂ _ _ _ _
      _ = f.eval₂ ((frobenius T p).comp (AdjoinRoot.of Q))
          (frobenius T p (AdjoinRoot.root Q)) := by rw [hcomm, frobenius_def, hroot]
      _ = frobenius T p (f.eval₂ (AdjoinRoot.of Q) (AdjoinRoot.root Q)) :=
        (Polynomial.hom_eval₂ _ _ _ _).symm
      _ = (AdjoinRoot.mk Q f)^p := by
        rw [frobenius_def]
        congr 1
        exact (AdjoinRoot.aeval_eq f).trans rfl

lemma lpsOriginalGaussMaximalResidue_subfield_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    ∀ S : Subfield (LPSOriginalGaussAffineOrder N hN p ⧸ q),
      lpsOriginalGaussMaximalResidueJ N hN p q ∈ S →
      lpsOriginalGaussMaximalResidueJN N hN p q ∈ S → S = ⊤ := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  intro S hj hn
  let g : LPSOriginalGaussBase p →+* K :=
    (Ideal.Quotient.mk q).comp (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))
  have hc : ∀ a : LPSOriginalGaussBase p, g a ∈ S := by
    intro a
    apply lpsOriginalLocalization_subfield_mem (Polynomial ℤ) (LPSOriginalGaussBase p)
      K (lpsOriginalGaussPrime p).primeCompl g S _ a
    intro P
    change (g.comp (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))) P ∈ S
    rw [lpsOriginalGaussMaximalResidue_integerBaseEval]
    exact lpsOriginalSubfield_eval₂_mem ℤ K (Int.castRingHom K) S
      (fun z => S.intCast_mem z) _ hj P
  exact lpsOriginalAdjoinRoot_surjective_subfield_eq_top (LPSOriginalGaussBase p) K
    (lpsOriginalGaussPolynomial N hN p) (Ideal.Quotient.mk q)
    (Ideal.Quotient.mk_surjective) S hc hn

lemma lpsOriginalGaussMaximalResidue_coordinates_generate
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    Subfield.closure {lpsOriginalGaussMaximalResidueJ N hN p q,
      lpsOriginalGaussMaximalResidueJN N hN p q} = ⊤ := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  apply lpsOriginalGaussMaximalResidue_subfield_eq_top N hN p q
  · exact Subfield.subset_closure (by simp)
  · exact Subfield.subset_closure (by simp)

def lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    LPSOriginalRelativeGaussInseparableBranch N hN p q →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
    lpsOriginalGaussMaximalResidue_charP N hN p q
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p
    (lpsOriginalGaussMaximalResidueJN N hN p q)

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_secondJ
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
      (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)) =
      lpsOriginalGaussMaximalResidueJ N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let f := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  have h := congrArg f
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_secondJ
      N p hNp h4N hN hpN q)
  rw [map_pow] at h
  have hc : f (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalGaussMaximalResidueJ N hN p q)) =
      (lpsOriginalGaussMaximalResidueJ N hN p q)^p :=
    lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of p _ _
  rw [hc] at h
  exact (frobenius K p).injective h

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    Function.Surjective (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let f : T →+* K := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  let L : Subfield K := f.fieldRange
  have hj : lpsOriginalGaussMaximalResidueJ N hN p q ∈ L := by
    refine ⟨lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN), ?_⟩
    exact lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_secondJ N p hNp h4N hN hpN q
  have hn : lpsOriginalGaussMaximalResidueJN N hN p q ∈ L := by
    refine ⟨AdjoinRoot.root ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)), ?_⟩
    exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_root p _
  have hs : L = ⊤ := lpsOriginalGaussMaximalResidue_subfield_eq_top N hN p q L hj hn
  exact RingHom.fieldRange_eq_top_iff.mp hs

def lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    LPSOriginalRelativeGaussInseparableBranch N hN p q ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let f : T →+* K := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  exact RingEquiv.ofBijective f ⟨f.injective,
    lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_surjective N p hNp h4N hN hpN q⟩

def lpsOriginalRelativeGaussInseparableBranchFrobeniusAlgEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
    letI : Algebra K T := inferInstance
    letI : Algebra K K := (frobenius K p).toAlgebra
    T ≃ₐ[K] K := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let : Algebra K T := inferInstance
  let : Algebra K K := (frobenius K p).toAlgebra
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  apply AlgEquiv.ofRingEquiv (f := e)
  intro u
  change lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p
    (lpsOriginalGaussMaximalResidueJN N hN p q)
    (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) u) = u^p
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of p _ u

lemma lpsOriginalGaussMaximalResidue_frobenius_finrank
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : Algebra K K := (frobenius K p).toAlgebra
    letI : Module K K := Algebra.toModule
    Module.finrank K K = p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let : Algebra K T := inferInstance
  let : Algebra K K := (frobenius K p).toAlgebra
  let : Module K K := Algebra.toModule
  have hd := lpsOriginalRelativeGaussInseparableBranch_finrank N hN p q
  have he := (lpsOriginalRelativeGaussInseparableBranchFrobeniusAlgEquiv
    N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq
  exact he.symm.trans hd

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_of
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
      (AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) u) = u^p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
    lpsOriginalGaussMaximalResidue_charP N hN p q
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_of p _ u

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
      (AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) =
      lpsOriginalGaussMaximalResidueJN N hN p q := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
    lpsOriginalGaussMaximalResidue_charP N hN p q
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_root p _

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_pow
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (x : LPSOriginalRelativeGaussInseparableBranch N hN p q) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q x) = x^p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
    lpsOriginalGaussMaximalResidue_charP N hN p q
  let : Fact (Irreducible ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) :=
      ⟨lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q⟩
  exact lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow p _ x

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_apply
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (x : LPSOriginalRelativeGaussInseparableBranch N hN p q) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q x =
      lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q x := by
  rfl

lemma lpsOriginalRelativeGaussInseparableBranch_secondCoordinates_generate
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
    Subfield.closure
      {lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN),
       AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))} = ⊤ := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let T := LPSOriginalRelativeGaussInseparableBranch N hN p q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let f : T →+* K := lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
  let jp := lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
    (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN)
  let y : T := AdjoinRoot.root ((Polynomial.X : Polynomial K)^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
  let S : Subfield T := Subfield.closure {jp,y}
  let L : Subfield K := S.map f
  have hj : lpsOriginalGaussMaximalResidueJ N hN p q ∈ L := by
    refine ⟨jp, Subfield.subset_closure (by simp), ?_⟩
    exact lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_secondJ N p hNp h4N hN hpN q
  have hn : lpsOriginalGaussMaximalResidueJN N hN p q ∈ L := by
    refine ⟨y, Subfield.subset_closure (by simp), ?_⟩
    exact lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_root N hN p q
  have hs : L = ⊤ := lpsOriginalGaussMaximalResidue_subfield_eq_top N hN p q L hj hn
  apply top_unique
  intro x _
  have hx : f x ∈ L := by rw [hs]; trivial
  obtain ⟨u,hu,he⟩ := hx
  have heq : u = x := f.injective he
  exact heq ▸ hu

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_j
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
      (lpsOriginalGaussMaximalResidueJ N hN p q) =
      lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  apply e.injective
  rw [e.apply_symm_apply]
  exact (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_secondJ
    N p hNp h4N hN hpN q).symm

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_jN
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
      (lpsOriginalGaussMaximalResidueJN N hN p q) =
      AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  apply e.injective
  rw [e.apply_symm_apply]
  exact (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_root N hN p q).symm

lemma lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv_symm_prime_power
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
      (u^p) = AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) u := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
  apply e.injective
  rw [e.apply_symm_apply]
  exact (lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_of N hN p q u).symm

end
end QEC.Coding.TannerLiftedProduct

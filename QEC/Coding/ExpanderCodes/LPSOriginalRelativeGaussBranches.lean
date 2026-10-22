import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Actual branches of the relative Gauss Hecke order

At each maximal ideal of the actual lower-level good-prime Gauss order,
the literal relative Hecke fibre is the product of its actual residue field
and the field obtained by adjoining a pth root of actual j_N. The second
extension is proved purely inseparable of degree p. These are exactly the
two primes above the given maximal ideal; their contractions and product
are explicit. For levels divisible by 4 and prime p coprime to the level,
both ramification indices are 1 and the canonical residue degrees are 1
and p. Reducedness over the imperfect residue field does not imply etaleness.

These are derived internal prerequisites of the original modular-curve
route motivated by pinned PK22 main.tex ex:Xpq (lines 484-486), rather than
separate public claims of that passage. The companion normalization-branch
module transports them to the proved actual integral closure. Global
correspondence cycles, smooth good reduction, Weil bounds, the principal
cover and spectral estimate, and the exact explicit finite-field qLDPC
family remain separate proof obligations. Parent issue449 remains OPEN;
pk-good-qldpc remains lean.proved=false.
-/
namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalCoprimeAdjoinRootEquiv
    {R : Type*} [CommRing R] (P Q : Polynomial R) (h : IsCoprime P Q) :
    AdjoinRoot (P*Q) ≃+* AdjoinRoot P × AdjoinRoot Q :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton P Q).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {P}) (Ideal.span {Q})
      ((Ideal.isCoprime_span_singleton_iff P Q).mpr h))

lemma lpsOriginalCoprimeAdjoinRootEquiv_mk
    {R : Type*} [CommRing R] (P Q : Polynomial R) (h : IsCoprime P Q)
    (f : Polynomial R) :
    lpsOriginalCoprimeAdjoinRootEquiv P Q h (AdjoinRoot.mk (P*Q) f) =
      (AdjoinRoot.mk P f,AdjoinRoot.mk Q f) := by
  dsimp only [lpsOriginalCoprimeAdjoinRootEquiv]
  erw [RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk]
  apply Prod.ext
  · erw [Ideal.quotientMulEquivQuotientProd_fst]
  · erw [Ideal.quotientMulEquivQuotientProd_snd]

lemma lpsOriginalRelativeGaussHeckeResidueFactors_coprime
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsCoprime
      ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q)) -
        Polynomial.C ((lpsOriginalGaussMaximalResidueJN N hN p q)^p))
      (Polynomial.X^p - Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  have hi := lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q
  apply IsCoprime.symm
  apply hi.coprime_iff_not_dvd.mpr
  intro hdiv
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv
    (Polynomial.X_sub_C_ne_zero ((lpsOriginalGaussMaximalResidueJN N hN p q)^p))
  rw [Polynomial.natDegree_X_pow_sub_C,Polynomial.natDegree_X_sub_C] at hdeg
  exact (Nat.not_le_of_gt (Fact.out : p.Prime).one_lt) hdeg

abbrev LPSOriginalRelativeGaussInseparableBranch
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :=
  AdjoinRoot ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))

@[instance_reducible]
def lpsOriginalRelativeGaussInseparableBranch_field
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Field (LPSOriginalRelativeGaussInseparableBranch N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let : Fact (Irreducible
      ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) :=
    ⟨lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q⟩
  infer_instance

lemma lpsOriginalRelativeGaussInseparableBranch_finrank
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Module.finrank (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussInseparableBranch N hN p q) = p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let P : Polynomial K := Polynomial.X^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)
  have hn : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (Fact.out : p.Prime).pos _
  have hd : Module.finrank K (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis hn).finrank.trans (AdjoinRoot.powerBasis_dim hn)
  change Module.finrank K (AdjoinRoot P) = p
  rw [hd,Polynomial.natDegree_X_pow_sub_C]

def lpsOriginalRelativeGaussResiduePolynomialEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q)) ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
        LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let a := lpsOriginalGaussMaximalResidueJN N hN p q
  let P : Polynomial K := Polynomial.X - Polynomial.C (a^p)
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
  let e : AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q)) ≃+* AdjoinRoot (P*Q) :=
    Ideal.quotEquivOfEq (congrArg (fun f : Polynomial K => Ideal.span {f})
      (lpsOriginalRelativeGaussHeckePolynomial_residue N hN p q))
  exact e.trans ((lpsOriginalCoprimeAdjoinRootEquiv P Q
    (lpsOriginalRelativeGaussHeckeResidueFactors_coprime N hN p hpN q)).trans
      (RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv (a^p)).toRingEquiv
        (RingEquiv.refl (AdjoinRoot Q))))

def lpsOriginalRelativeGaussHeckeFiberEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸ q.map
      (algebraMap (LPSOriginalGaussAffineOrder N hN p)
        (LPSOriginalRelativeGaussHeckeOrder N hN p))) ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
        LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot q
    (lpsOriginalRelativeGaussHeckePolynomial N hN p)).trans
      (lpsOriginalRelativeGaussResiduePolynomialEquiv N hN p hpN q)

lemma lpsOriginalRelativeGaussResiduePolynomialEquiv_mk
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (f : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q)) :
    lpsOriginalRelativeGaussResiduePolynomialEquiv N hN p hpN q
      (AdjoinRoot.mk ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
        (Ideal.Quotient.mk q)) f) =
      (f.eval ((lpsOriginalGaussMaximalResidueJN N hN p q)^p),
        AdjoinRoot.mk ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) f) := by
  dsimp only [lpsOriginalRelativeGaussResiduePolynomialEquiv]
  erw [RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,RingEquiv.trans_apply,
    lpsOriginalCoprimeAdjoinRootEquiv_mk]
  rfl

lemma lpsOriginalRelativeGaussHeckeFiberEquiv_mk
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (f : Polynomial (LPSOriginalGaussAffineOrder N hN p)) :
    lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
      (Ideal.Quotient.mk (q.map (AdjoinRoot.of
        (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
        (AdjoinRoot.mk (lpsOriginalRelativeGaussHeckePolynomial N hN p) f)) =
      ((f.map (Ideal.Quotient.mk q)).eval
        ((lpsOriginalGaussMaximalResidueJN N hN p q)^p),
        AdjoinRoot.mk ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
              (f.map (Ideal.Quotient.mk q))) := by
  change lpsOriginalRelativeGaussResiduePolynomialEquiv N hN p hpN q
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot q
      (lpsOriginalRelativeGaussHeckePolynomial N hN p)
      (Ideal.Quotient.mk _ (AdjoinRoot.mk _ f))) = _
  rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]
  exact lpsOriginalRelativeGaussResiduePolynomialEquiv_mk N hN p hpN q _

lemma lpsOriginalRelativeGaussHeckeFiberEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
      (Ideal.Quotient.mk (q.map (AdjoinRoot.of
        (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
        (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p))) =
      ((lpsOriginalGaussMaximalResidueJN N hN p q)^p,
        AdjoinRoot.root ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) := by
  simpa using lpsOriginalRelativeGaussHeckeFiberEquiv_mk N hN p hpN q Polynomial.X

lemma lpsOriginalRelativeGaussHeckeFiberEquiv_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
      (Ideal.Quotient.mk (q.map (AdjoinRoot.of
        (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
        (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)) =
      (Ideal.Quotient.mk q c,
        AdjoinRoot.of ((Polynomial.X : Polynomial
          (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
            Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))
              (Ideal.Quotient.mk q c)) := by
  simpa only [Polynomial.map_C,Polynomial.eval_C,AdjoinRoot.of,RingHom.comp_apply] using
    lpsOriginalRelativeGaussHeckeFiberEquiv_mk N hN p hpN q (Polynomial.C c)

lemma lpsOriginalGaussMaximalResidue_charP
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  exact charP_of_injective_ringHom
    (lpsOriginalGaussMaximalResidueConstantMap N hN p q).injective p

lemma lpsOriginalAdjoinRootPrimePower_root
    {K : Type*} [CommRing K] (p : ℕ) (a : K) :
    let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
    (AdjoinRoot.root Q)^p = AdjoinRoot.of Q a := by
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
  exact sub_eq_zero.mp (by simpa [Q] using AdjoinRoot.eval₂_root Q)

lemma lpsOriginalAdjoinRootPrimePower_range
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Fact (Irreducible ((Polynomial.X : Polynomial K)^p - Polynomial.C a))]
    (x : AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) :
    x^p ∈ (algebraMap K
      (AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a))).range := by
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
    refine ⟨f.eval₂ (frobenius K p) a,?_⟩
    change AdjoinRoot.of Q (f.eval₂ (frobenius K p) a) = (AdjoinRoot.mk Q f)^p
    calc
      AdjoinRoot.of Q (f.eval₂ (frobenius K p) a) =
          f.eval₂ ((AdjoinRoot.of Q).comp (frobenius K p)) (AdjoinRoot.of Q a) :=
        Polynomial.hom_eval₂ _ _ _ _
      _ = f.eval₂ ((frobenius T p).comp (AdjoinRoot.of Q))
          (frobenius T p (AdjoinRoot.root Q)) := by rw [hcomm,frobenius_def,hroot]
      _ = frobenius T p (f.eval₂ (AdjoinRoot.of Q) (AdjoinRoot.root Q)) :=
        (Polynomial.hom_eval₂ _ _ _ _).symm
      _ = (AdjoinRoot.mk Q f)^p := by
        rw [frobenius_def]
        congr 1
        exact (AdjoinRoot.aeval_eq f).trans rfl

lemma lpsOriginalRelativeGaussInseparableBranch_purelyInseparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussInseparableBranch N hN p q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : Fact (Irreducible ((Polynomial.X : Polynomial K)^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) :=
    ⟨lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q⟩
  apply (isPurelyInseparable_iff_pow_mem K p).mpr
  intro x
  refine ⟨1,?_⟩
  simpa using lpsOriginalAdjoinRootPrimePower_range p
    (lpsOriginalGaussMaximalResidueJN N hN p q) x

lemma lpsOriginalSurjectiveProductKernels_coprime
    {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]
    (f : R →+* K × L) (hf : Function.Surjective f) :
    IsCoprime (RingHom.ker ((RingHom.fst K L).comp f))
      (RingHom.ker ((RingHom.snd K L).comp f)) := by
  obtain ⟨u,hu⟩ := hf (0,1)
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u,?_,1-u,?_,?_⟩
  · simpa [RingHom.mem_ker,RingHom.comp_apply] using congrArg Prod.fst hu
  · simp [RingHom.mem_ker,RingHom.comp_apply,map_sub,hu]
  · ring

lemma lpsOriginalSurjectiveProductKernels_product
    {R K L : Type*} [CommRing R] [CommRing K] [CommRing L]
    (f : R →+* K × L) (hf : Function.Surjective f) :
    (RingHom.ker ((RingHom.fst K L).comp f)) *
      (RingHom.ker ((RingHom.snd K L).comp f)) = RingHom.ker f := by
  rw [Ideal.mul_eq_inf_of_isCoprime (lpsOriginalSurjectiveProductKernels_coprime f hf)]
  ext x
  simp [RingHom.mem_ker,RingHom.comp_apply,Prod.ext_iff]

def lpsOriginalRelativeGaussHeckeBranchMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
        LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q).toRingHom.comp
    (Ideal.Quotient.mk (q.map (AdjoinRoot.of
      (lpsOriginalRelativeGaussHeckePolynomial N hN p))))

lemma lpsOriginalRelativeGaussHeckeBranchMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q) :=
  (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q).surjective.comp
    Ideal.Quotient.mk_surjective

def lpsOriginalRelativeGaussHeckeLinearBranchMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (RingHom.fst _ _).comp (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)

def lpsOriginalRelativeGaussHeckeInseparableBranchMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  (RingHom.snd _ _).comp (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)

abbrev LPSOriginalRelativeGaussHeckeLinearBranchIdeal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  RingHom.ker (lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q)

abbrev LPSOriginalRelativeGaussHeckeInseparableBranchIdeal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  RingHom.ker (lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q)

lemma lpsOriginalRelativeGaussHeckeLinearBranchMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q) := by
  intro y
  obtain ⟨x,hx⟩ := lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q (y,0)
  exact ⟨x,congrArg Prod.fst hx⟩

lemma lpsOriginalRelativeGaussHeckeInseparableBranchMap_surjective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q) := by
  intro y
  obtain ⟨x,hx⟩ := lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q (0,y)
  exact ⟨x,congrArg Prod.snd hx⟩

lemma lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).IsMaximal := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  exact RingHom.ker_isMaximal_of_surjective _
    (lpsOriginalRelativeGaussHeckeLinearBranchMap_surjective N hN p hpN q)

lemma lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).IsMaximal := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  exact RingHom.ker_isMaximal_of_surjective _
    (lpsOriginalRelativeGaussHeckeInseparableBranchMap_surjective N hN p hpN q)

lemma lpsOriginalRelativeGaussHeckeBranchIdeals_coprime
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    IsCoprime (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q)
      (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) :=
  lpsOriginalSurjectiveProductKernels_coprime _
    (lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q)

lemma lpsOriginalRelativeGaussHeckeBranchIdeals_product
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) *
      (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) =
      q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) := by
  change RingHom.ker ((RingHom.fst _ _).comp
      (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)) *
    RingHom.ker ((RingHom.snd _ _).comp
      (lpsOriginalRelativeGaussHeckeBranchMap N hN p hpN q)) = _
  rw [lpsOriginalSurjectiveProductKernels_product _
    (lpsOriginalRelativeGaussHeckeBranchMap_surjective N hN p hpN q)]
  ext x
  change lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
    (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [← map_zero (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q),
    (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q).injective.eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

lemma lpsOriginalRelativeGaussHeckeLinearBranchIdeal_contract
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).comap
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) = q := by
  ext c
  change (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
    (Ideal.Quotient.mk _ (AdjoinRoot.of
      (lpsOriginalRelativeGaussHeckePolynomial N hN p) c))).1 = 0 ↔ c ∈ q
  erw [congrArg Prod.fst (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)]
  exact Ideal.Quotient.eq_zero_iff_mem

lemma lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_contract
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).comap
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) = q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let Q : Polynomial K := Polynomial.X^p -
    Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  have hi : Function.Injective (AdjoinRoot.of Q) := (algebraMap K (AdjoinRoot Q)).injective
  ext c
  change (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q
    (Ideal.Quotient.mk _ (AdjoinRoot.of
      (lpsOriginalRelativeGaussHeckePolynomial N hN p) c))).2 = 0 ↔ c ∈ q
  erw [congrArg Prod.snd (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)]
  rw [← map_zero (AdjoinRoot.of Q),hi.eq_iff,Ideal.Quotient.eq_zero_iff_mem]

lemma lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).LiesOver q := by
  constructor
  exact (lpsOriginalRelativeGaussHeckeLinearBranchIdeal_contract N hN p hpN q).symm

lemma lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).LiesOver q := by
  constructor
  exact (lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_contract N hN p hpN q).symm

lemma lpsOriginalCoprimeMaximalIdeal_ne_bot
    {R : Type*} [CommRing R] (I J : Ideal R) [J.IsMaximal]
    (hc : IsCoprime I J) : I ≠ ⊥ := by
  intro hi
  have h := hc.sup_eq
  rw [hi,bot_sup_eq] at h
  exact (inferInstance : J.IsMaximal).ne_top h

lemma lpsOriginalCoprimeMaximalIdeal_factors
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : Ideal R) [I.IsMaximal] [J.IsMaximal] (hc : IsCoprime I J) :
    UniqueFactorizationMonoid.normalizedFactors (I*J) = {I} + {J} := by
  have hi := lpsOriginalCoprimeMaximalIdeal_ne_bot I J hc
  have hj := lpsOriginalCoprimeMaximalIdeal_ne_bot J I hc.symm
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hi hj,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime hi inferInstance).irreducible,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime hj inferInstance).irreducible,
    normalize_eq,normalize_eq]

lemma lpsOriginalCoprimeMaximalIdeal_factorCount
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : Ideal R) [I.IsMaximal] [J.IsMaximal] (hc : IsCoprime I J) :
    (UniqueFactorizationMonoid.normalizedFactors (I*J)).count I = 1 := by
  have hne : I ≠ J := by
    intro h
    have ht := hc.sup_eq
    rw [h,sup_idem] at ht
    exact (inferInstance : J.IsMaximal).ne_top ht
  rw [lpsOriginalCoprimeMaximalIdeal_factors I J hc]
  simp [hne]

lemma lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussHeckeOrder N hN p)) ≠ ⊥ := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  have hc := lpsOriginalRelativeGaussHeckeBranchIdeals_coprime N hN p hpN q
  have hi := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc
  have hj := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc.symm
  rw [AdjoinRoot.algebraMap_eq,← lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q]
  exact mul_ne_zero hi hj

lemma lpsOriginalRelativeGaussHeckeLinearBranch_ramificationIndex_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).ramificationIdx
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q _
    (lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot N p hNp h4N hN hpN q),
    AdjoinRoot.algebraMap_eq,← lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q]
  exact lpsOriginalCoprimeMaximalIdeal_factorCount _ _
    (lpsOriginalRelativeGaussHeckeBranchIdeals_coprime N hN p hpN q)

lemma lpsOriginalRelativeGaussHeckeInseparableBranch_ramificationIndex_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).ramificationIdx
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q _
    (lpsOriginalRelativeGaussHeckeMaximalMap_ne_bot N p hNp h4N hN hpN q),
    AdjoinRoot.algebraMap_eq,← lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q,
    mul_comm]
  exact lpsOriginalCoprimeMaximalIdeal_factorCount _ _
    (lpsOriginalRelativeGaussHeckeBranchIdeals_coprime N hN p hpN q).symm



def lpsOriginalRelativeGaussHeckeLinearBranchResidueEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
    (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) ≃ₐ[
        LPSOriginalGaussAffineOrder N hN p ⧸ q] (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  refine { (RingHom.quotientKerEquivOfSurjective
      (lpsOriginalRelativeGaussHeckeLinearBranchMap_surjective N hN p hpN q)) with
    commutes' := ?_ }
  intro c
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective c
  change lpsOriginalRelativeGaussHeckeLinearBranchMap N hN p hpN q
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c) = Ideal.Quotient.mk q c
  exact congrArg Prod.fst (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)

def lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
    (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) ≃ₐ[
        LPSOriginalGaussAffineOrder N hN p ⧸ q]
      LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  refine { (RingHom.quotientKerEquivOfSurjective
      (lpsOriginalRelativeGaussHeckeInseparableBranchMap_surjective N hN p hpN q)) with
    commutes' := ?_ }
  intro c
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective c
  change lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c) =
      AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) (Ideal.Quotient.mk q c)
  exact congrArg Prod.snd (lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c)

lemma lpsOriginalRelativeGaussHeckeLinearBranch_inertiaDegree_one
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussHeckeLinearBranchResidueEquiv N hN p hpN q).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self _)

lemma lpsOriginalRelativeGaussHeckeInseparableBranch_inertiaDegree_prime
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv N hN p hpN q).toLinearEquiv.finrank_eq.trans
    (lpsOriginalRelativeGaussInseparableBranch_finrank N hN p q)



lemma lpsOriginalRelativeGaussHeckePrimeOver_classification
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Ideal (LPSOriginalRelativeGaussHeckeOrder N hN p)) [P.IsPrime] [P.LiesOver q] :
    P = LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q ∨
      P = LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q := by
  have hmap : q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussHeckeOrder N hN p)) ≤ P :=
    (Ideal.map_le_iff_le_comap).mpr (le_of_eq (P.over_def q))
  rw [AdjoinRoot.algebraMap_eq,← lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q] at hmap
  rcases (inferInstance : P.IsPrime).mul_le.mp hmap with hi | hj
  · exact Or.inl ((lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q).eq_of_le
      (inferInstance : P.IsPrime).ne_top hi).symm
  · exact Or.inr ((lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q).eq_of_le
      (inferInstance : P.IsPrime).ne_top hj).symm

lemma lpsOriginalRelativeGaussHeckeInseparableBranchResidue_purelyInseparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
    letI := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
    letI : Field (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
        LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := Ideal.Quotient.field _
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
        LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  let : Field (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) := Ideal.Quotient.field _
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let := lpsOriginalRelativeGaussInseparableBranch_purelyInseparable N hN p hpN q
  exact (lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv N hN p hpN q).symm.isPurelyInseparable



end
end QEC.Coding.TannerLiftedProduct

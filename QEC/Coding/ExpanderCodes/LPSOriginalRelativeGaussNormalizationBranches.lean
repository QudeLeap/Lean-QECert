import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussBranches

/-!
# Actual branches on the relative Gauss normalization

Transport the actual relative Hecke fibre and its two canonical maximal
ideals along the proved normalization equivalence. The coefficients and
actual j_Np are preserved in the original generated function field; the
new affine-order algebra structure is exactly this proved coefficient map.
The normalized branch residue degrees are 1 and p, both ramification
indices are 1, and the degree-p residue extension is purely inseparable.
Every prime with the given contraction is one of these two ideals.

These derived internal statements support the original modular-curve route
motivated by pinned PK22 main.tex ex:Xpq (lines 484-486). This is an affine
normalization and residue calculation, not a global cycle identity, a
smooth proper reduction, a principal-level curve identification or a
spectral bound. The source-backed exact PK22 family theorem remains open.
Parent issue449 stays OPEN; pk-good-qldpc remains lean.proved=false.
-/
namespace QEC.Coding.TannerLiftedProduct
noncomputable section

abbrev LPSOriginalRelativeGaussNormalization
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  ↥(integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)))

@[instance_reducible, instance 1100]
def lpsOriginalRelativeGaussNormalization_commRing
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    CommRing (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  dsimp only [LPSOriginalRelativeGaussNormalization]
  infer_instance

def lpsOriginalRelativeGaussNormalizationRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussHeckeOrder N hN p ≃+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  exact (lpsOriginalRelativeGaussNormalizationEquiv N p hNp h4N hN hpN).toRingEquiv

def lpsOriginalRelativeGaussNormalizationCoefficients
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p →+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).toRingHom.comp
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p))

def lpsOriginalRelativeGaussNormalizationRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
    (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p))

lemma lpsOriginalRelativeGaussNormalizationRoot_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN).val.val =
      lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) :=
  lpsOriginalRelativeGaussNormalizationEquiv_root_coe N p hNp h4N hN hpN

lemma lpsOriginalRelativeGaussNormalizationCoefficients_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (c : LPSOriginalGaussAffineOrder N hN p) :
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c).val.val =
      (lpsOriginalGaussAffineToGenerated N hN p c).val :=
  lpsOriginalRelativeGaussNormalizationEquiv_base_coe N p hNp h4N hN hpN c

lemma lpsOriginalRelativeGaussNormalizationMaximalMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) =
      (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p))).map
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN :
          LPSOriginalRelativeGaussHeckeOrder N hN p →+*
            LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :=
  (Ideal.map_map _ _).symm

def lpsOriginalRelativeGaussNormalizationFiberEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) ≃+*
        (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
          LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  exact (Ideal.quotientEquiv
    (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q)).symm.trans
      (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q)

lemma lpsOriginalRelativeGaussNormalizationFiberEquiv_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (x : LPSOriginalRelativeGaussHeckeOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN x)) =
      lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q (Ideal.Quotient.mk _ x) := by
  let e := Ideal.quotientEquiv
    (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q)
  have hm := Ideal.quotientEquiv_mk
    (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q) x
  exact congrArg (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q)
    ((congrArg e.symm hm).symm.trans (e.symm_apply_apply _))

lemma lpsOriginalRelativeGaussNormalizationFiberEquiv_root
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN)) =
      ((lpsOriginalGaussMaximalResidueJN N hN p q)^p,
        AdjoinRoot.root ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
          Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q))) := by
  change lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
      (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p)))) = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk N p hNp h4N hN hpN q]
  exact lpsOriginalRelativeGaussHeckeFiberEquiv_root N hN p hpN q

lemma lpsOriginalRelativeGaussNormalizationFiberEquiv_base
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c)) =
      (Ideal.Quotient.mk q c,
        AdjoinRoot.of ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
          Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) (Ideal.Quotient.mk q c)) := by
  change lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c))) = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_mk N p hNp h4N hN hpN q]
  exact lpsOriginalRelativeGaussHeckeFiberEquiv_base N hN p hpN q c



@[instance_reducible]
def lpsOriginalRelativeGaussNormalizationCoefficients_algebra
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) : Algebra (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :=
  (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).toAlgebra

def lpsOriginalRelativeGaussNormalizationAffineEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    LPSOriginalRelativeGaussHeckeOrder N hN p ≃ₐ[LPSOriginalGaussAffineOrder N hN p]
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  refine { (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN) with commutes' := ?_ }
  intro c
  rfl

lemma lpsOriginalRelativeGaussNormalization_dedekind
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    IsDedekindDomain (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  let e := lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
  let : IsDomain (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := MulEquiv.isDomain (LPSOriginalRelativeGaussHeckeOrder N hN p) e.symm.toMulEquiv
  let : IsNoetherianRing (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := isNoetherianRing_of_ringEquiv (LPSOriginalRelativeGaussHeckeOrder N hN p) e
  let : Ring.DimensionLEOne (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.DimensionLEOne.of_ringEquiv e.symm
  let : IsIntegrallyClosed (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := IsIntegrallyClosed.of_equiv e
  exact {}


abbrev LPSOriginalRelativeGaussNormalizationLinearBranchIdeal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).map (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).IsMaximal := by
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal N hN p hpN q
  exact Ideal.IsMaximal.map_bijective _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).bijective inferInstance

lemma lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).LiesOver q := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  exact Ideal.LiesOver.of_eq_map_equiv q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN) rfl


abbrev LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).map (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).IsMaximal := by
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  exact Ideal.IsMaximal.map_bijective _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).bijective inferInstance

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).LiesOver q := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  exact Ideal.LiesOver.of_eq_map_equiv q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN) rfl


lemma lpsOriginalRelativeGaussNormalizationBranchIdeals_coprime
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] : IsCoprime (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  change ((LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) ⊔ ((LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) = ⊤
  rw [← Ideal.map_sup,(lpsOriginalRelativeGaussHeckeBranchIdeals_coprime N hN p hpN q).sup_eq,
    Ideal.map_top]

lemma lpsOriginalRelativeGaussNormalizationBranchIdeals_product
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) * (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) = q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) := by
  change ((LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) * ((LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).map
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)) = _
  rw [← Ideal.map_mul,lpsOriginalRelativeGaussHeckeBranchIdeals_product N hN p hpN q]
  exact (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q).symm


def lpsOriginalRelativeGaussNormalizationLinearBranchResidueEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸ LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) ≃ₐ[LPSOriginalGaussAffineOrder N hN p ⧸ q]
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
  exact (Ideal.Quotient.algEquivOfEqMap q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN)
      (P := LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) (Q := LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) rfl).symm.trans
    (lpsOriginalRelativeGaussHeckeLinearBranchResidueEquiv N hN p hpN q)

lemma lpsOriginalRelativeGaussNormalizationLinearBranch_inertiaDegree_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).inertiaDeg (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
  let : Algebra (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q).over)
  let : Module (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) := Algebra.toModule
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussNormalizationLinearBranchResidueEquiv N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self _)

lemma lpsOriginalRelativeGaussNormalizationLinearBranch_ramificationIndex_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).ramificationIdx (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
  have hc := lpsOriginalRelativeGaussNormalizationBranchIdeals_coprime N p hNp h4N hN hpN q
  have hi := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc
  have hj := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc.symm
  have hm : q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)) ≠ ⊥ := by
    change q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ≠ ⊥
    rw [← lpsOriginalRelativeGaussNormalizationBranchIdeals_product N p hNp h4N hN hpN q]
    exact mul_ne_zero hi hj
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q _ hm]
  change (UniqueFactorizationMonoid.normalizedFactors (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))).count (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) = 1
  rw [← lpsOriginalRelativeGaussNormalizationBranchIdeals_product N p hNp h4N hN hpN q]
  exact lpsOriginalCoprimeMaximalIdeal_factorCount _ _ hc


def lpsOriginalRelativeGaussNormalizationInseparableBranchResidueEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸ LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) ≃ₐ[LPSOriginalGaussAffineOrder N hN p ⧸ q]
      LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  exact (Ideal.Quotient.algEquivOfEqMap q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN)
      (P := LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) (Q := LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) rfl).symm.trans
    (lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv N hN p hpN q)

lemma lpsOriginalRelativeGaussNormalizationInseparableBranch_inertiaDegree_prime
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).inertiaDeg (LPSOriginalGaussAffineOrder N hN p) = p := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  let : Algebra (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q).over)
  let : Module (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := Algebra.toModule
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussNormalizationInseparableBranchResidueEquiv N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq.trans
    (lpsOriginalRelativeGaussInseparableBranch_finrank N hN p q)

lemma lpsOriginalRelativeGaussNormalizationInseparableBranch_ramificationIndex_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).ramificationIdx (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalization_dedekind N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  have hc := lpsOriginalRelativeGaussNormalizationBranchIdeals_coprime N p hNp h4N hN hpN q
  have hi := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc
  have hj := lpsOriginalCoprimeMaximalIdeal_ne_bot _ _ hc.symm
  have hm : q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)) ≠ ⊥ := by
    change q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ≠ ⊥
    rw [← lpsOriginalRelativeGaussNormalizationBranchIdeals_product N p hNp h4N hN hpN q]
    exact mul_ne_zero hi hj
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count q _ hm]
  change (UniqueFactorizationMonoid.normalizedFactors (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))).count (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) = 1
  rw [← lpsOriginalRelativeGaussNormalizationBranchIdeals_product N p hNp h4N hN hpN q,
    mul_comm (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q)
      (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q)]
  exact lpsOriginalCoprimeMaximalIdeal_factorCount _ _ hc.symm



lemma lpsOriginalRelativeGaussNormalizationPrimeOver_classification
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Ideal (LPSOriginalRelativeGaussNormalization N p hNp h4N hN)) [P.IsPrime]
    (hPq : P.comap (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) = q) :
    P = LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q ∨
      P = LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q := by
  let e := lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
  let P₀ := P.comap e
  let : P₀.IsPrime := Ideal.comap_isPrime e P
  let : P₀.LiesOver q := by
    constructor
    change q = (P.comap e).comap (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p))
    change q = P.comap (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    exact hPq.symm
  rcases lpsOriginalRelativeGaussHeckePrimeOver_classification N hN p hpN q P₀ with h | h
  · exact Or.inl ((P.map_comap_eq_self_of_equiv e).symm.trans
      (congrArg (fun I => I.map e) h))
  · exact Or.inr ((P.map_comap_eq_self_of_equiv e).symm.trans
      (congrArg (fun I => I.map e) h))

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchResidue_purelyInseparable
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
    letI : Field (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) :=
      Ideal.Quotient.field _
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  let : Field (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := Ideal.Quotient.field _
  let := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
  let := lpsOriginalRelativeGaussInseparableBranch_purelyInseparable N hN p hpN q
  exact (lpsOriginalRelativeGaussNormalizationInseparableBranchResidueEquiv N p hNp h4N hN hpN q).symm.isPurelyInseparable

end
end QEC.Coding.TannerLiftedProduct

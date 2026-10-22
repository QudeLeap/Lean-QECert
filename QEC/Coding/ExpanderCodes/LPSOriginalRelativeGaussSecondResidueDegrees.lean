import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondOrderMap

/-! # Residue degrees of the genuine second Gauss projection

Use the entire actual second Gauss order map to prove both actual branch ideals
lie over the original maximal ideal. Construct the named quotient equivalences
from the genuine branch projections, prove their scalar diagrams for the second
coefficient action, and derive inertia degrees p and 1 on the linear and
inseparable branches respectively. The target action in the linear calculation
is explicitly Frobenius; the original first projection action is not reused.

These derived internal prerequisites are motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486). Global correspondence cycles, smooth proper good
reduction, Weil bounds, principal-level spectrum and the exact explicit
arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449
remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

@[instance_reducible]
def lpsOriginalRelativeGaussNormalizationSecondOrder_algebra
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Algebra (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :=
  (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).toAlgebra

lemma lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondComap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).comap
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) = q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  rw [← lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker,RingHom.comap_ker,
    lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder]
  rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk q) (frobenius K p).injective]
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondComap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).comap
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) = q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  rw [← lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker,RingHom.comap_ker,
    lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder]
  rw [RingHom.ker_comp_of_injective (Ideal.Quotient.mk q)
    (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm.injective]
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem

lemma lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondLiesOver
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).LiesOver q := by
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  constructor
  change q = (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).comap
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN)
  exact (lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondComap
    N p hNp h4N hN hpN q).symm

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).LiesOver q := by
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  constructor
  change q = (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).comap
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN)
  exact (lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondComap
    N p hNp h4N hN hpN q).symm

/-- First isomorphism theorem through the named quotient, avoiding equality transport. -/
def lpsOriginalRingHomQuotientEquivOfKernel
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hker : RingHom.ker f = I)
    (hs : Function.Surjective f) : R ⧸ I ≃+* S := by
  let hI : I ≤ RingHom.ker f := le_of_eq hker.symm
  let g : R ⧸ I →+* S := Ideal.Quotient.lift I f (fun x hx => hI hx)
  apply RingEquiv.ofBijective g
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change f a = f b at h
    apply Ideal.Quotient.eq.mpr
    rw [← hker]
    change f (a-b) = 0
    rw [map_sub, h, sub_self]
  · intro y
    obtain ⟨a, ha⟩ := hs y
    exact ⟨Ideal.Quotient.mk I a, ha⟩

lemma lpsOriginalRingHomQuotientEquivOfKernel_mk
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hker : RingHom.ker f = I)
    (hs : Function.Surjective f) (x : R) :
    lpsOriginalRingHomQuotientEquivOfKernel f I hker hs (Ideal.Quotient.mk I x) = f x := by
  rfl

lemma lpsOriginalRelativeGaussNormalizationLinearBranchMap_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) := by
  intro x
  obtain ⟨z, hz⟩ := (lpsOriginalRelativeGaussNormalizationFiberEquiv
    N p hNp h4N hN hpN q).surjective (x, 0)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨c, ?_⟩
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ c)).1 = x
  rw [hc, hz]

def lpsOriginalRelativeGaussNormalizationLinearBranchResidueRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) ≃+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  lpsOriginalRingHomQuotientEquivOfKernel (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) _
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker N p hNp h4N hN hpN q)
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap_surjective N p hNp h4N hN hpN q)

lemma lpsOriginalRelativeGaussNormalizationLinearBranchResidueRingEquiv_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    lpsOriginalRelativeGaussNormalizationLinearBranchResidueRingEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ c) = lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q c :=
  lpsOriginalRingHomQuotientEquivOfKernel_mk
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q) _
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap_ker N p hNp h4N hN hpN q)
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap_surjective N p hNp h4N hN hpN q) c

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchMap_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q) := by
  intro x
  obtain ⟨z, hz⟩ := (lpsOriginalRelativeGaussNormalizationFiberEquiv
    N p hNp h4N hN hpN q).surjective (0, x)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨c, ?_⟩
  change (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ c)).2 = x
  rw [hc, hz]

def lpsOriginalRelativeGaussNormalizationInseparableBranchResidueRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) ≃+*
      LPSOriginalRelativeGaussInseparableBranch N hN p q :=
  lpsOriginalRingHomQuotientEquivOfKernel (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q) _
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker N p hNp h4N hN hpN q)
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_surjective N p hNp h4N hN hpN q)

lemma lpsOriginalRelativeGaussNormalizationInseparableBranchResidueRingEquiv_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    lpsOriginalRelativeGaussNormalizationInseparableBranchResidueRingEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ c) = lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q c :=
  lpsOriginalRingHomQuotientEquivOfKernel_mk
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q) _
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_ker N p hNp h4N hN hpN q)
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_surjective N p hNp h4N hN hpN q) c

def lpsOriginalRelativeGaussNormalizationLinearBranchSecondResidueAlgEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : Algebra K K := (frobenius K p).toAlgebra
    letI : Module K K := Algebra.toModule
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) ≃ₐ[K] K := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : Algebra K K := (frobenius K p).toAlgebra
  let : Module K K := Algebra.toModule
  apply AlgEquiv.ofRingEquiv (f := lpsOriginalRelativeGaussNormalizationLinearBranchResidueRingEquiv N p hNp h4N hN hpN q)
  intro u
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
  change lpsOriginalRelativeGaussNormalizationLinearBranchResidueRingEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c)) =
      frobenius K p (Ideal.Quotient.mk q c)
  rw [lpsOriginalRelativeGaussNormalizationLinearBranchResidueRingEquiv_mk]
  exact congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+* K => f c)
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder N p hNp h4N hN hpN q)

def lpsOriginalRelativeGaussNormalizationInseparableBranchSecondResidueAlgEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) ≃ₐ[K] K := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
  apply AlgEquiv.ofRingEquiv (f := (lpsOriginalRelativeGaussNormalizationInseparableBranchResidueRingEquiv N p hNp h4N hN hpN q).trans (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q))
  intro u
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
  change lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
    (lpsOriginalRelativeGaussNormalizationInseparableBranchResidueRingEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c))) =
        Ideal.Quotient.mk q c
  rw [lpsOriginalRelativeGaussNormalizationInseparableBranchResidueRingEquiv_mk]
  have h := congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+*
    LPSOriginalRelativeGaussInseparableBranch N hN p q => f c)
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder N p hNp h4N hN hpN q)
  change lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c) =
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
        (Ideal.Quotient.mk q c) at h
  rw [h]
  exact RingEquiv.apply_symm_apply _ _

lemma lpsOriginalRelativeGaussNormalizationLinearBranch_secondInertiaDegree_prime
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = p := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
  let : Algebra K (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_secondLiesOver
        N p hNp h4N hN hpN q).over)
  let : Module K (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) := Algebra.toModule
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : Algebra K K := (frobenius K p).toAlgebra
  let : Module K K := Algebra.toModule
  exact (lpsOriginalRelativeGaussNormalizationLinearBranchSecondResidueAlgEquiv
    N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq.trans
      (lpsOriginalGaussMaximalResidue_frobenius_finrank N p hNp h4N hN hpN q)

lemma lpsOriginalRelativeGaussNormalizationInseparableBranch_secondInertiaDegree_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal N p hNp h4N hN hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver N p hNp h4N hN hpN q
  let : Algebra K (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (le_of_eq (lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_secondLiesOver
        N p hNp h4N hN hpN q).over)
  let : Module K (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) := Algebra.toModule
  rw [Ideal.inertiaDeg_eq_of_isMaximal q]
  exact (lpsOriginalRelativeGaussNormalizationInseparableBranchSecondResidueAlgEquiv
    N p hNp h4N hN hpN q).toLinearEquiv.finrank_eq.trans (Module.finrank_self K)

end
end QEC.Coding.TannerLiftedProduct

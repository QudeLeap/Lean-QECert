import QEC.Coding.ExpanderCodes.LPSOriginalRelativeGaussSecondOrderMap

/-! # The genuine normalized Gauss fiber and its two Frobenius diagrams

Identify the actual first normalization fiber ring with the product of the
actual lower residue field with itself, using the proved inseparable descent.
Construct the two actual quotient maps and prove their entire diagrams as
(u, u^p) and (u^p, u). Derive the second contraction of the actual first fiber
ideal and injectivity of both maps. The product identification is a ring
equivalence; the two scalar actions are distinct.

These derived internal prerequisites are motivated by pinned PK22 main.tex
ex:Xpq (lines 484-486). Global correspondence cycles, smooth proper good
reduction, Weil bounds, principal-level spectrum and the exact explicit
arbitrary-finite-field qLDPC family remain separate obligations. Parent issue449
remains OPEN; pk-good-qldpc remains lean.proved=false.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) ≃+*
        (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
          (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  exact (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q).trans
    (RingEquiv.prodCongr (RingEquiv.refl K)
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q))

lemma lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_first
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c)) =
        (Ideal.Quotient.mk q c, (Ideal.Quotient.mk q c)^p) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  change ((lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c))).1,
    lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
        (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c))).2) = _
  rw [lpsOriginalRelativeGaussNormalizationFiberEquiv_base]
  apply Prod.ext
  · rfl
  · change lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent N hN p q
      (AdjoinRoot.of ((Polynomial.X : Polynomial K)^p -
        Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) (Ideal.Quotient.mk q c)) = _
    exact lpsOriginalRelativeGaussInseparableBranchFrobeniusDescent_of N hN p q _

lemma lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c)) =
        ((Ideal.Quotient.mk q c)^p, Ideal.Quotient.mk q c) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  change (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c),
    lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
        (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c))) = _
  apply Prod.ext
  · exact congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+* K => f c)
      (lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder N p hNp h4N hN hpN q)
  · have h := congrArg (fun f : LPSOriginalGaussAffineOrder N hN p →+*
        LPSOriginalRelativeGaussInseparableBranch N hN p q => f c)
      (lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder N p hNp h4N hN hpN q)
    change lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c) =
        (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm
          (Ideal.Quotient.mk q c) at h
    rw [h]
    exact RingEquiv.apply_symm_apply _ _

lemma lpsOriginalRelativeGaussNormalizationSecondOrder_mem_firstFiberIdeal_iff
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c ∈
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) ↔ c ∈ q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  constructor
  · intro hc
    have hc0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    have h := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
      N p hNp h4N hN hpN q c
    rw [hc0, map_zero] at h
    have hz := congrArg Prod.snd h
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz.symm
  · intro hc
    have hc0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    have h := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
      N p hNp h4N hN hpN q c
    rw [hc0, zero_pow (Fact.out : p.Prime).ne_zero] at h
    have he : e (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c)) = e 0 :=
      h.trans (map_zero e).symm
    exact Ideal.Quotient.eq_zero_iff_mem.mp (e.injective he)

def lpsOriginalRelativeGaussNormalizationFirstFiberMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalGaussAffineOrder N hN p ⧸ q) →+*
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) :=
  Ideal.Quotient.lift q ((Ideal.Quotient.mk _).comp (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (fun _c hc => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) hc))

lemma lpsOriginalRelativeGaussNormalizationFirstFiberMap_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q (Ideal.Quotient.mk q c) =
      Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c) := by
  rfl

lemma lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) =
        (RingHom.id K).prod (frobenius K p) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  apply RingHom.ext
  intro u
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
  change lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN c)) =
      (Ideal.Quotient.mk q c, (Ideal.Quotient.mk q c)^p)
  exact lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_first
    N p hNp h4N hN hpN q c

def lpsOriginalRelativeGaussNormalizationSecondFiberMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalGaussAffineOrder N hN p ⧸ q) →+*
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
        q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) :=
  Ideal.Quotient.lift q ((Ideal.Quotient.mk _).comp (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN))
    (fun c hc => Ideal.Quotient.eq_zero_iff_mem.mpr ((lpsOriginalRelativeGaussNormalizationSecondOrder_mem_firstFiberIdeal_iff N p hNp h4N hN hpN q c).mpr hc))

lemma lpsOriginalRelativeGaussNormalizationSecondFiberMap_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (c : LPSOriginalGaussAffineOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q (Ideal.Quotient.mk q c) =
      Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c) := by
  rfl

lemma lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q) =
        (frobenius K p).prod (RingHom.id K) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  apply RingHom.ext
  intro u
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective u
  change lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
    (Ideal.Quotient.mk _ (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN c)) =
      ((Ideal.Quotient.mk q c)^p, Ideal.Quotient.mk q c)
  exact lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_second
    N p hNp h4N hN hpN q c

lemma lpsOriginalRelativeGaussNormalizationFirstFiberIdeal_secondComap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)).comap
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) = q := by
  ext c
  exact lpsOriginalRelativeGaussNormalizationSecondOrder_mem_firstFiberIdeal_iff
    N p hNp h4N hN hpN q c

lemma lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Injective (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  intro x y h
  have hx := congrArg (fun f : K →+* K × K => f x)
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
      N p hNp h4N hN hpN q)
  have hy := congrArg (fun f : K →+* K × K => f y)
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
      N p hNp h4N hN hpN q)
  change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q x) = (x, x^p) at hx
  change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q y) = (y, y^p) at hy
  have hxy := congrArg e h
  exact congrArg Prod.fst (hx.symm.trans (hxy.trans hy))

lemma lpsOriginalRelativeGaussNormalizationSecondFiberMap_injective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Injective (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  intro x y h
  have hx := congrArg (fun f : K →+* K × K => f x)
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
      N p hNp h4N hN hpN q)
  have hy := congrArg (fun f : K →+* K × K => f y)
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
      N p hNp h4N hN hpN q)
  change e (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q x) = (x^p, x) at hx
  change e (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q y) = (y^p, y) at hy
  have hxy := congrArg e h
  exact congrArg Prod.snd (hx.symm.trans (hxy.trans hy))

end
end QEC.Coding.TannerLiftedProduct

import QEC.Coding.ExpanderCodes.LPSOriginalIntegralDualRelation
import QEC.Coding.ExpanderCodes.LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree

/-! # Actual good-prime Gauss residue coordinates

For every maximal ideal of the actual level-N Gauss affine order at a prime
not dividing N, construct the actual F_p(j) and F_p(j_N) embeddings. Prove both
coordinate transcendence, the literal dual modular equation, generation of the
entire residue field over F_p(j_N) by j, separability of that entire extension,
and that the actual j_N has no p-th root there.

All extension properties are proved for the actual quotient. The downstream
use is the coprime-level relative Hecke special-fibre calculation in PK22's LPS
input (`ex:Xpq`). Global correspondence cycles, smooth good reduction, the Weil
bound, principal spectrum, and the full qLDPC family are separate obligations.
-/

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

/-- The actual maximal residue of an integral monic root algebra receives the base residue. -/
def lpsOriginalAdjoinRootMaximalResidueBaseMap
    (R : Type*) [CommRing R] [IsLocalRing R]
    (P : Polynomial R) (hP : P.Monic)
    (q : Ideal (AdjoinRoot P)) [q.IsMaximal] :
    IsLocalRing.ResidueField R →+* (AdjoinRoot P ⧸ q) := by
  let : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  have hcontract : q.comap (algebraMap R (AdjoinRoot P)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) q)
  let i := (Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot P))
  exact Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) i (by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change a ∈ q.comap (algebraMap R (AdjoinRoot P))
    rwa [hcontract])

lemma lpsOriginalAdjoinRootMaximalResidueBaseMap_diagram
    (R : Type*) [CommRing R] [IsLocalRing R]
    (P : Polynomial R) (hP : P.Monic)
    (q : Ideal (AdjoinRoot P)) [q.IsMaximal] :
    (lpsOriginalAdjoinRootMaximalResidueBaseMap R P hP q).comp
      (IsLocalRing.residue R) =
      (Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot P)) := by
  apply RingHom.ext
  intro a
  rfl

def lpsOriginalGaussMaximalResidueFractionMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    FractionRing (Polynomial (ZMod p)) →+* (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (lpsOriginalAdjoinRootMaximalResidueBaseMap (LPSOriginalGaussBase p)
    (lpsOriginalGaussPolynomial N hN p)
    ((lpsOriginalIntegerPolynomial_monic N hN).map _) q).comp
    (lpsOriginalGaussResidueEquiv p).symm.toRingHom

lemma lpsOriginalGaussMaximalResidueFractionMap_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Injective (lpsOriginalGaussMaximalResidueFractionMap N hN p q) :=
  (lpsOriginalGaussMaximalResidueFractionMap N hN p q).injective

def lpsOriginalGaussMaximalResidueJ
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    LPSOriginalGaussAffineOrder N hN p ⧸ q :=
  Ideal.Quotient.mk q
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))

def lpsOriginalGaussMaximalResidueJN
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    LPSOriginalGaussAffineOrder N hN p ⧸ q :=
  Ideal.Quotient.mk q (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))

lemma lpsOriginalIntegerPolynomial_gaussMaximalResidueDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by
  let f := Ideal.Quotient.mk q
  have h := congrArg f (lpsOriginalIntegerPolynomial_gaussDualRoot N hN p hpN)
  have hc : f.comp (Polynomial.eval₂RingHom (Int.castRingHom _)
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp [lpsOriginalGaussMaximalResidueJN,f]
  rw [Polynomial.hom_eval₂,map_zero,hc] at h
  exact h

lemma lpsOriginalGaussMaximalResidueFractionMap_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) :
    lpsOriginalGaussMaximalResidueFractionMap N hN p q
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))
        (lpsOriginalGaussCoefficientReduction p P)) =
      Ideal.Quotient.mk q
        (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
          (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P)) := by
  rw [← lpsOriginalGaussResidueEquiv_base p P]
  simp only [lpsOriginalGaussMaximalResidueFractionMap,RingHom.comp_apply]
  erw [(lpsOriginalGaussResidueEquiv p).symm_apply_apply]
  rw [IsScalarTower.algebraMap_apply (Polynomial ℤ) (LPSOriginalGaussBase p)
    (IsLocalRing.ResidueField (LPSOriginalGaussBase p))]
  change (lpsOriginalAdjoinRootMaximalResidueBaseMap (LPSOriginalGaussBase p)
    (lpsOriginalGaussPolynomial N hN p)
    ((lpsOriginalIntegerPolynomial_monic N hN).map _) q).comp
    (IsLocalRing.residue (LPSOriginalGaussBase p))
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P) = _
  erw [lpsOriginalAdjoinRootMaximalResidueBaseMap_diagram]
  rfl

def lpsOriginalGaussMaximalResidueConstantMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    ZMod p →+* (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (lpsOriginalGaussMaximalResidueFractionMap N hN p q).comp
    (algebraMap (ZMod p) (FractionRing (Polynomial (ZMod p))))

lemma lpsOriginalGaussMaximalResidueFractionMap_polynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueFractionMap N hN p q).comp
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))) =
      Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
      lpsOriginalGaussMaximalResidueConstantMap]
    rw [IsScalarTower.algebraMap_apply (ZMod p) (Polynomial (ZMod p))
      (FractionRing (Polynomial (ZMod p)))]
    rfl
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    simpa only [lpsOriginalGaussCoefficientReduction,Polynomial.coe_mapRingHom,
      Polynomial.map_X,lpsOriginalGaussMaximalResidueJ] using
      lpsOriginalGaussMaximalResidueFractionMap_base N hN p q Polynomial.X

lemma lpsOriginalGaussMaximalResidueJ_transcendental
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
    Transcendental (ZMod p) (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  apply transcendental_iff_injective.mpr
  change Function.Injective (Polynomial.eval₂RingHom
    (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
    (lpsOriginalGaussMaximalResidueJ N hN p q))
  rw [← lpsOriginalGaussMaximalResidueFractionMap_polynomial]
  exact (lpsOriginalGaussMaximalResidueFractionMap_injective N hN p q).comp
    (IsFractionRing.injective (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))

lemma lpsOriginalGaussMaximalResidueJN_transcendental
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
    Transcendental (ZMod p) (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  let P := (lpsOriginalIntegerPolynomial N hN).map
    (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
  have hc : (Polynomial.eval₂RingHom (algebraMap (ZMod p) K)
      (lpsOriginalGaussMaximalResidueJN N hN p q)).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) =
      Polynomial.eval₂RingHom (Int.castRingHom K)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp
  have hr : P.eval₂ (Polynomial.eval₂RingHom (algebraMap (ZMod p) K)
      (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by
    dsimp only [P]
    rw [Polynomial.eval₂_map,hc]
    exact lpsOriginalIntegerPolynomial_gaussMaximalResidueDualRoot N hN p hpN q
  exact lpsOriginalDualMonicRelation_transcendental (ZMod p) K P
    ((lpsOriginalIntegerPolynomial_monic N hN).map _)
    (lpsOriginalGaussMaximalResidueJ N hN p q)
    (lpsOriginalGaussMaximalResidueJN N hN p q) hr
    (lpsOriginalGaussMaximalResidueJ_transcendental N hN p q)

lemma lpsOriginalFractionLift_polynomial
    (F K : Type*) [Field F] [Field K]
    (f : Polynomial F →+* K) (hf : Function.Injective f) :
    (IsFractionRing.lift (K := FractionRing (Polynomial F)) hf).comp
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))) = f := by
  apply RingHom.ext
  intro P
  exact IsFractionRing.lift_algebraMap hf P

def lpsOriginalGaussMaximalResidueJN_FractionMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    FractionRing (Polynomial (ZMod p)) →+* (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  letI := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  have hi : Function.Injective (Polynomial.eval₂RingHom
      (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q)) :=
    transcendental_iff_injective.mp
      (lpsOriginalGaussMaximalResidueJN_transcendental N hN p hpN q)
  exact IsFractionRing.lift hi

lemma lpsOriginalGaussMaximalResidueJN_FractionMap_polynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).comp
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))) =
      Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  exact lpsOriginalFractionLift_polynomial (ZMod p)
    (LPSOriginalGaussAffineOrder N hN p ⧸ q)
    (Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q))
    (transcendental_iff_injective.mp
      (lpsOriginalGaussMaximalResidueJN_transcendental N hN p hpN q))

lemma lpsOriginalGaussMaximalResidueJN_FractionMap_X
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) =
      lpsOriginalGaussMaximalResidueJN N hN p q := by
  have h := congrArg (fun f : Polynomial (ZMod p) →+*
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) => f Polynomial.X)
    (lpsOriginalGaussMaximalResidueJN_FractionMap_polynomial N hN p hpN q)
  simpa only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using h

lemma lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).comp
      ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  rw [← RingHom.comp_assoc,lpsOriginalGaussMaximalResidueJN_FractionMap_polynomial]
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp

lemma lpsOriginalModularPolynomialModFraction_actualResidueDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalModularPolynomialModFraction N hN p).eval₂
      (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q)
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.eval₂_map,
    lpsOriginalGaussMaximalResidueJN_FractionMap_integerCoefficient]
  exact lpsOriginalIntegerPolynomial_gaussMaximalResidueDualRoot N hN p hpN q

lemma lpsOriginalGaussMaximalResidueJ_separable_overJN
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
    IsSeparable (FractionRing (Polynomial (ZMod p)))
      (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  have hr := lpsOriginalModularPolynomialModFraction_actualResidueDualRoot N hN p hpN q
  change Polynomial.aeval (lpsOriginalGaussMaximalResidueJ N hN p q)
    (lpsOriginalModularPolynomialModFraction N hN p) = 0 at hr
  exact (lpsOriginalModularPolynomialModFraction_separable N hN p hpN).of_dvd
    (minpoly.dvd _ _ hr)

lemma lpsOriginalSubfield_eval₂_mem
    (R K : Type*) [CommRing R] [Field K] (f : R →+* K)
    (S : Subfield K) (hf : ∀ a, f a ∈ S) (x : K) (hx : x ∈ S)
    (P : Polynomial R) : P.eval₂ f x ∈ S := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add]
    exact S.add_mem hP hQ
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact S.mul_mem (hf a) (S.pow_mem hx n)

lemma lpsOriginalLocalization_subfield_mem
    (R A K : Type*) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] (M : Submonoid R) [IsLocalization M A]
    (f : A →+* K) (S : Subfield K)
    (hf : ∀ a : R, f (algebraMap R A a) ∈ S) (x : A) : f x ∈ S := by
  obtain ⟨⟨a,b⟩,hx⟩ := IsLocalization.mk'_surjective M x
  rw [← hx]
  have hb : f (algebraMap R A b) ≠ 0 :=
    ((IsLocalization.map_units A b).map f).ne_zero
  have h := congrArg f (IsLocalization.mk'_spec A a b)
  rw [map_mul] at h
  rw [(eq_div_iff hb).mpr h]
  exact S.div_mem (hf a) (hf b)

lemma lpsOriginalAdjoinRoot_surjective_subfield_eq_top
    (R K : Type*) [CommRing R] [Field K] (P : Polynomial R)
    (f : AdjoinRoot P →+* K) (hf : Function.Surjective f)
    (S : Subfield K) (hc : ∀ a : R, f (AdjoinRoot.of P a) ∈ S)
    (hx : f (AdjoinRoot.root P) ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a,rfl⟩ := hf x
  obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective a
  rw [← AdjoinRoot.aeval_eq,Polynomial.aeval_def,Polynomial.hom_eval₂]
  exact lpsOriginalSubfield_eval₂_mem R K
    (f.comp (algebraMap R (AdjoinRoot P))) S hc _ hx Q

lemma lpsOriginalGaussMaximalResidue_integerBaseEval
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    ((Ideal.Quotient.mk q).comp
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    rfl

lemma lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
    IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
      {lpsOriginalGaussMaximalResidueJ N hN p q} = ⊤ := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  let L := IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
    {lpsOriginalGaussMaximalResidueJ N hN p q}
  have hj : lpsOriginalGaussMaximalResidueJ N hN p q ∈ L :=
    IntermediateField.mem_adjoin_simple_self _ _
  have hn : lpsOriginalGaussMaximalResidueJN N hN p q ∈ L := by
    rw [← lpsOriginalGaussMaximalResidueJN_FractionMap_X N hN p hpN q]
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

lemma lpsOriginalGaussMaximalResidue_separable_overJN
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
    Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p)))
      (IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
        {lpsOriginalGaussMaximalResidueJ N hN p q}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr
      (lpsOriginalGaussMaximalResidueJ_separable_overJN N hN p hpN q)
  let e := (IntermediateField.equivOfEq
    (lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top N hN p hpN q)).trans
    IntermediateField.topEquiv
  exact Algebra.IsSeparable.of_algHom
    (FractionRing (Polynomial (ZMod p))) _ e.symm.toAlgHom

lemma lpsOriginalFractionCoordinate_not_prime_power
    (F : Type*) [Field F] (p : ℕ) (hp : p.Prime)
    (u : FractionRing (Polynomial F)) :
    u^p ≠ algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X := by
  let e := RatFunc.toFractionRingRingEquiv (K := F)
  have hx : e.symm
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) =
      (RatFunc.X : RatFunc F) := by
    change RatFunc.ofFractionRing
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) = _
    rw [RatFunc.ofFractionRing_algebraMap,RatFunc.algebraMap_X]
  intro h
  have he := congrArg e.symm h
  rw [map_pow,hx] at he
  exact QEC.Coding.AlgebraicGeometry.ratFunc_coordinate_not_prime_power F p hp (e.symm u) he

lemma lpsOriginalGaussMaximalResidueJN_not_prime_power
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    u^p ≠ lpsOriginalGaussMaximalResidueJN N hN p q := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
  let : Algebra.IsSeparable (FractionRing (Polynomial (ZMod p))) K :=
    lpsOriginalGaussMaximalResidue_separable_overJN N hN p hpN q
  have h := QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
    (FractionRing (Polynomial (ZMod p))) K p
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X)
    (lpsOriginalFractionCoordinate_not_prime_power (ZMod p) p (Fact.out : p.Prime)) u
  change u^p ≠ lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q
    (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) at h
  rw [lpsOriginalGaussMaximalResidueJN_FractionMap_X] at h
  exact h

end
end QEC.Coding.TannerLiftedProduct

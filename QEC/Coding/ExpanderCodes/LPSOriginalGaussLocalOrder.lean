import QEC.Coding.ExpanderCodes.LPSOriginalCoprimeModularReduction
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
The original modular polynomial at the coefficient Gauss prime. The kernel of
Z[X] → F_p[X] is (p); its local DVR has residue field F_p(X). For p not dividing
the positive level, the same original affine order is formally unramified and
is the integral closure in the already constructed original function field.
The canonical comparison preserves the original j_N generator.

Internal arithmetic prerequisite for PK22 main.tex ex:Xpq (lines 484–486) and
th:qLDPC (lines 231–238). This proves a generic-point normalization comparison,
not global good reduction, a spectral bound or the qLDPC main theorem. #449
remains open and pk-good-qldpc remains unproved.
-/

namespace QEC.Coding.AlgebraicGeometry
noncomputable section

lemma adjoinRoot_formallyUnramified_of_derivativeUnit
    (R : Type*) [CommRing R] (P : Polynomial R)
    (hd : IsUnit (Polynomial.aeval (AdjoinRoot.root P) P.derivative)) :
    Algebra.FormallyUnramified R (AdjoinRoot P) := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f₁ f₂ e
  have hmem : f₁ (AdjoinRoot.root P) - f₂ (AdjoinRoot.root P) ∈ I := by
    simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
      AlgHom.congr_fun e (AdjoinRoot.root P)
  have h := Polynomial.eval_add_of_sq_eq_zero (P.map (algebraMap R B))
    (f₂ (AdjoinRoot.root P)) (f₁ (AdjoinRoot.root P) - f₂ (AdjoinRoot.root P))
    (show (f₁ (AdjoinRoot.root P) - f₂ (AdjoinRoot.root P))^2 ∈ ⊥ from
      hI ▸ Ideal.pow_mem_pow hmem 2)
  simp only [add_sub_cancel,Polynomial.eval_map_algebraMap,
    Polynomial.aeval_algHom_apply,AdjoinRoot.aeval_eq,AdjoinRoot.mk_self,
    map_zero,Polynomial.derivative_map,zero_add] at h
  have hd' : IsUnit (AdjoinRoot.mk P P.derivative) := by
    simpa only [AdjoinRoot.aeval_eq] using hd
  have hr : f₁ (AdjoinRoot.root P) = f₂ (AdjoinRoot.root P) := by
    rwa [eq_comm,((hd'.map f₂).mul_right_eq_zero),sub_eq_zero] at h
  apply AlgHom.ext
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih q =>
    rw [← AdjoinRoot.aeval_eq,← Polynomial.aeval_algHom_apply,
      hr,Polynomial.aeval_algHom_apply]


lemma adjoinRoot_derivativeUnit_of_residueSeparable
    (R : Type*) [CommRing R] [IsLocalRing R] (P : Polynomial R)
    (hmonic : P.Monic)
    (hsep : (P.map (IsLocalRing.residue R)).Separable) :
    IsUnit (Polynomial.aeval (AdjoinRoot.root P) P.derivative) := by
  classical
  let B := AdjoinRoot P
  let : Module.Finite R B := hmonic.finite_adjoinRoot
  by_contra hu
  obtain ⟨q,hq,hdq⟩ := exists_max_ideal_of_mem_nonunits hu
  let : q.IsMaximal := hq
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  have hcontract : q.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) q)
  let j : B →+* B ⧸ q := Ideal.Quotient.mk q
  let i : R →+* B ⧸ q := j.comp (algebraMap R B)
  have hzero : ∀ a : R, a ∈ IsLocalRing.maximalIdeal R → i a = 0 := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change a ∈ q.comap (algebraMap R B)
    rwa [hcontract]
  let k : IsLocalRing.ResidueField R →+* B ⧸ q :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) i hzero
  have hdiagram : k.comp (IsLocalRing.residue R) = i := by
    apply RingHom.ext
    intro a
    change k (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a) = i a
    rfl
  have hroot : (P.map (IsLocalRing.residue R)).eval₂ k
      (j (AdjoinRoot.root P)) = 0 := by
    rw [Polynomial.eval₂_map,hdiagram,← Polynomial.hom_eval₂]
    rw [← Polynomial.aeval_def,AdjoinRoot.aeval_eq,AdjoinRoot.mk_self,map_zero]
  have hnonzero := hsep.eval₂_derivative_ne_zero k hroot
  have hderivative : j (Polynomial.aeval (AdjoinRoot.root P) P.derivative) ≠ 0 := by
    rw [Polynomial.derivative_map,Polynomial.eval₂_map,hdiagram] at hnonzero
    change P.derivative.eval₂ (j.comp (algebraMap R B)) (j (AdjoinRoot.root P)) ≠ 0 at hnonzero
    rw [← Polynomial.hom_eval₂,← Polynomial.aeval_def] at hnonzero
    exact hnonzero
  exact hderivative (Ideal.Quotient.eq_zero_iff_mem.mpr hdq)

lemma adjoinRoot_formallyUnramified_of_residueSeparable
    (R : Type*) [CommRing R] [IsLocalRing R] (P : Polynomial R)
    (hmonic : P.Monic)
    (hsep : (P.map (IsLocalRing.residue R)).Separable) :
    Algebra.FormallyUnramified R (AdjoinRoot P) :=
  adjoinRoot_formallyUnramified_of_derivativeUnit R P
    (adjoinRoot_derivativeUnit_of_residueSeparable R P hmonic hsep)


open scoped TensorProduct

def adjoinRoot_baseChangeEquiv (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (P : Polynomial R) :
    (A ⊗[R] AdjoinRoot P) ≃ₐ[A] AdjoinRoot (P.map (algebraMap R A)) := by
  let e : (A ⊗[R] R) ≃ₐ[A] A := Algebra.TensorProduct.rid R A A
  let i : R →+* (A ⊗[R] R) :=
    (Algebra.TensorProduct.includeRight : R →ₐ[R] (A ⊗[R] R)).toRingHom
  let Q := P.map i
  have hi : e.toRingHom.comp i = algebraMap R A := by
    apply RingHom.ext
    intro a
    simp [e,i,Algebra.smul_def]
  have hQ : Q.map e.toRingHom = P.map (algebraMap R A) := by
    rw [show Q = P.map i from rfl,Polynomial.map_map,hi]
  exact (AdjoinRoot.tensorAlgEquiv (R := R) (T := A) P Q rfl).trans
    (AdjoinRoot.mapAlgEquiv e Q (P.map (algebraMap R A)) (Associated.of_eq hQ))

lemma adjoinRoot_baseChangeEquiv_root (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (P : Polynomial R) :
    adjoinRoot_baseChangeEquiv R A P (1 ⊗ₜ[R] AdjoinRoot.root P) =
    AdjoinRoot.root (P.map (algebraMap R A)) := by
  unfold adjoinRoot_baseChangeEquiv
  simp only [AlgEquiv.trans_apply,AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_root]


lemma adjoinRoot_baseChangeEquiv_one_tmul
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (P : Polynomial R)
    (x : AdjoinRoot P) :
    adjoinRoot_baseChangeEquiv R A P (1 ⊗ₜ[R] x) =
    AdjoinRoot.map (algebraMap R A) P (P.map (algebraMap R A)) dvd_rfl x := by
  let e := adjoinRoot_baseChangeEquiv R A P
  let j : AdjoinRoot P →+* (A ⊗[R] AdjoinRoot P) :=
    (Algebra.TensorProduct.includeRight : AdjoinRoot P →ₐ[R] _).toRingHom
  have h : e.toRingHom.comp j =
      AdjoinRoot.map (algebraMap R A) P (P.map (algebraMap R A)) dvd_rfl := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      change e (1 ⊗ₜ[R] AdjoinRoot.of P r) =
        AdjoinRoot.map (algebraMap R A) P (P.map (algebraMap R A)) dvd_rfl (AdjoinRoot.of P r)
      rw [AdjoinRoot.map_of]
      unfold e adjoinRoot_baseChangeEquiv
      rw [AlgEquiv.trans_apply,AdjoinRoot.tensorAlgEquiv_of]
      rw [AdjoinRoot.coe_mapAlgEquiv,AdjoinRoot.map_of]
      simp [Algebra.smul_def]
    · rw [RingHom.comp_apply,AdjoinRoot.map_root]
      change e (1 ⊗ₜ[R] AdjoinRoot.root P) = AdjoinRoot.root (P.map (algebraMap R A))
      exact adjoinRoot_baseChangeEquiv_root R A P
  exact RingHom.congr_fun h x

lemma adjoinRoot_baseChange_isLocalization
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) [IsLocalization M A] (P : Polynomial R) :
    let : Algebra (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R A))) :=
      (AdjoinRoot.map (algebraMap R A) P (P.map (algebraMap R A)) dvd_rfl).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (AdjoinRoot P) M)
      (AdjoinRoot (P.map (algebraMap R A))) := by
  let B := AdjoinRoot (P.map (algebraMap R A))
  let : Algebra (AdjoinRoot P) B :=
    (AdjoinRoot.map (algebraMap R A) P (P.map (algebraMap R A)) dvd_rfl).toAlgebra
  let : IsScalarTower R A B := inferInstance
  let : IsScalarTower R (AdjoinRoot P) B :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := AdjoinRoot P) (A := B) (by
    apply RingHom.ext
    intro r
    change algebraMap A B (algebraMap R A r) =
      AdjoinRoot.map (algebraMap R A) P (P.map (algebraMap R A)) dvd_rfl (AdjoinRoot.of P r)
    rw [AdjoinRoot.map_of]
    rfl)
  have hp : Algebra.IsPushout R A (AdjoinRoot P) B := by
    constructor
    apply IsBaseChange.of_equiv (adjoinRoot_baseChangeEquiv R A P).toLinearEquiv
    intro x
    exact adjoinRoot_baseChangeEquiv_one_tmul R A P x
  apply (Algebra.isLocalization_iff_isPushout M A).mpr
  exact (Algebra.IsPushout.comm R A (AdjoinRoot P) B).mp hp

end
end QEC.Coding.AlgebraicGeometry

namespace QEC.Coding.TannerLiftedProduct
noncomputable section

def lpsOriginalGaussCoefficientReduction (p : ℕ) : Polynomial ℤ →+* Polynomial (ZMod p) :=
  Polynomial.mapRingHom (Int.castRingHom (ZMod p))

def lpsOriginalGaussPrime (p : ℕ) : Ideal (Polynomial ℤ) :=
  RingHom.ker (lpsOriginalGaussCoefficientReduction p)

local instance lpsOriginalGaussPrime_isPrime (p : ℕ) [Fact p.Prime] :
    (lpsOriginalGaussPrime p).IsPrime :=
  RingHom.ker_isPrime (lpsOriginalGaussCoefficientReduction p)

lemma lpsOriginalGaussPrime_eq_span (p : ℕ) [Fact p.Prime] :
    lpsOriginalGaussPrime p = Ideal.span {Polynomial.C (p : ℤ)} := by
  apply Ideal.ext
  intro f
  rw [Ideal.mem_span_singleton,Polynomial.C_dvd_iff_dvd_coeff]
  change f.map (Int.castRingHom (ZMod p)) = 0 ↔ ∀ i, (p : ℤ) ∣ f.coeff i
  constructor
  · intro h i
    have hi := congrArg (fun q : Polynomial (ZMod p) => q.coeff i) h
    have hc : (f.coeff i : ZMod p) = 0 := by simpa [Polynomial.coeff_map] using hi
    exact (CharP.intCast_eq_zero_iff (ZMod p) p (f.coeff i)).mp hc
  · intro h
    ext i
    simpa [Polynomial.coeff_map] using
      (CharP.intCast_eq_zero_iff (ZMod p) p (f.coeff i)).mpr (h i)

local instance lpsOriginalGaussPrime_principal (p : ℕ) [Fact p.Prime] :
    (lpsOriginalGaussPrime p).IsPrincipal :=
  ⟨⟨Polynomial.C (p : ℤ), lpsOriginalGaussPrime_eq_span p⟩⟩

lemma lpsOriginalGaussPrime_ne_bot (p : ℕ) [Fact p.Prime] :
    lpsOriginalGaussPrime p ≠ ⊥ := by
  intro h
  have hc : Polynomial.C (p : ℤ) ∈ lpsOriginalGaussPrime p := by
    rw [lpsOriginalGaussPrime_eq_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [h,Ideal.mem_bot] at hc
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact hp (Polynomial.C_eq_zero.mp hc)

abbrev LPSOriginalGaussBase (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime (lpsOriginalGaussPrime p)

lemma lpsOriginalGaussBase_dvr (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing (LPSOriginalGaussBase p) := by
  let R := LPSOriginalGaussBase p
  have hnf : ¬ IsField R := IsLocalization.AtPrime.not_isField
    (Polynomial ℤ) (lpsOriginalGaussPrime_ne_bot p) R
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (lpsOriginalGaussPrime p) R]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 4 0).mp hprincipal


lemma lpsOriginalGaussCoefficientReduction_surjective (p : ℕ) :
    Function.Surjective (lpsOriginalGaussCoefficientReduction p) :=
  Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective

def lpsOriginalGaussResidueEquiv (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField (LPSOriginalGaussBase p) ≃+*
      FractionRing (Polynomial (ZMod p)) := by
  let e : (Polynomial ℤ ⧸ lpsOriginalGaussPrime p) ≃+* Polynomial (ZMod p) :=
    (lpsOriginalGaussCoefficientReduction p).quotientKerEquivOfSurjective
      (lpsOriginalGaussCoefficientReduction_surjective p)
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := (lpsOriginalGaussPrime p).ResidueField)
    (L := FractionRing (Polynomial (ZMod p))) e

lemma lpsOriginalGaussResidueEquiv_base (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) :
    lpsOriginalGaussResidueEquiv p
      (algebraMap (Polynomial ℤ)
        (IsLocalRing.ResidueField (LPSOriginalGaussBase p)) f) =
    algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))
      (lpsOriginalGaussCoefficientReduction p f) := by
  let e : (Polynomial ℤ ⧸ lpsOriginalGaussPrime p) ≃+* Polynomial (ZMod p) :=
    (lpsOriginalGaussCoefficientReduction p).quotientKerEquivOfSurjective
      (lpsOriginalGaussCoefficientReduction_surjective p)
  change (IsFractionRing.ringEquivOfRingEquiv
    (K := (lpsOriginalGaussPrime p).ResidueField)
    (L := FractionRing (Polynomial (ZMod p))) e)
    (algebraMap (Polynomial ℤ ⧸ lpsOriginalGaussPrime p)
      (lpsOriginalGaussPrime p).ResidueField
      (Ideal.Quotient.mk (lpsOriginalGaussPrime p) f)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

def lpsOriginalGaussPolynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Polynomial (LPSOriginalGaussBase p) :=
  (lpsOriginalIntegerPolynomial N hN).map
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))

lemma lpsOriginalGaussPolynomial_residueDiagram
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (((lpsOriginalGaussPolynomial N hN p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p))).map
      (lpsOriginalGaussResidueEquiv p).toRingHom) =
    lpsOriginalModularPolynomialModFraction N hN p := by
  rw [lpsOriginalGaussPolynomial,Polynomial.map_map,Polynomial.map_map,
    lpsOriginalModularPolynomialModFraction]
  congr 1
  apply RingHom.ext
  intro f
  change lpsOriginalGaussResidueEquiv p
    (algebraMap (Polynomial ℤ) (lpsOriginalGaussPrime p).ResidueField f) = _
  exact lpsOriginalGaussResidueEquiv_base p f

lemma lpsOriginalGaussPolynomial_residueSeparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ((lpsOriginalGaussPolynomial N hN p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p))).Separable := by
  apply (Polynomial.separable_map (lpsOriginalGaussResidueEquiv p).toRingHom).mp
  rw [lpsOriginalGaussPolynomial_residueDiagram]
  exact lpsOriginalModularPolynomialModFraction_separable N hN p hpN

lemma lpsOriginalGaussAffineOrder_formallyUnramified
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    Algebra.FormallyUnramified (LPSOriginalGaussBase p)
      (AdjoinRoot (lpsOriginalGaussPolynomial N hN p)) :=
  QEC.Coding.AlgebraicGeometry.adjoinRoot_formallyUnramified_of_residueSeparable
    (LPSOriginalGaussBase p) (lpsOriginalGaussPolynomial N hN p)
    ((lpsOriginalIntegerPolynomial_monic N hN).map _)
    (lpsOriginalGaussPolynomial_residueSeparable N hN p hpN)


def lpsOriginalGaussBaseFractionMap (p : ℕ) [Fact p.Prime] :
    LPSOriginalGaussBase p →+* FractionRing (Polynomial ℚ) := by
  let g : Polynomial ℤ →+* FractionRing (Polynomial ℚ) :=
    (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
      (Polynomial.mapRingHom (Int.castRingHom ℚ))
  have hg : Function.Injective g :=
    (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
      lpsOriginalIntegerCoefficientMap_injective
  exact IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl)
    (S := LPSOriginalGaussBase p) (g := g) (fun s =>
      isUnit_iff_ne_zero.mpr (fun h => s.property (by
        have hs : (s : Polynomial ℤ) = 0 := hg (h.trans g.map_zero.symm)
        rw [hs]
        exact Ideal.zero_mem _)))

lemma lpsOriginalGaussBaseFractionMap_base (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) :
    lpsOriginalGaussBaseFractionMap p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
    algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))
      (f.map (Int.castRingHom ℚ)) := by
  simp [lpsOriginalGaussBaseFractionMap]

lemma lpsOriginalGaussBaseFractionMap_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalGaussBaseFractionMap p) := by
  rw [lpsOriginalGaussBaseFractionMap,IsLocalization.lift_injective_iff]
  intro x y
  rw [(FaithfulSMul.algebraMap_injective (Polynomial ℤ)
      (LPSOriginalGaussBase p)).eq_iff]
  have h : Function.Injective
      ((algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ))) :=
    (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
      lpsOriginalIntegerCoefficientMap_injective
  exact h.eq_iff.symm

lemma lpsOriginalGaussPolynomial_fractionDiagram
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (lpsOriginalGaussPolynomial N hN p).map
      (lpsOriginalGaussBaseFractionMap p) =
    (lpsOriginalIntegerPolynomialRational N hN).map
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) := by
  rw [lpsOriginalGaussPolynomial,lpsOriginalIntegerPolynomialRational,
    Polynomial.map_map,Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact lpsOriginalGaussBaseFractionMap_base p f

lemma lpsOriginalGaussPolynomial_irreducible
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Irreducible (lpsOriginalGaussPolynomial N hN p) := by
  have hm : (lpsOriginalGaussPolynomial N hN p).Monic :=
    (lpsOriginalIntegerPolynomial_monic N hN).map _
  apply hm.isPrimitive.irreducible_of_irreducible_map_of_injective
    (lpsOriginalGaussBaseFractionMap_injective p)
  rw [lpsOriginalGaussPolynomial_fractionDiagram,
    lpsOriginalIntegerPolynomial_minpoly N hN]
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact minpoly.irreducible (lpsOriginalJNInFractionField_integralQ N hN)

abbrev LPSOriginalGaussAffineOrder
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :=
  AdjoinRoot (lpsOriginalGaussPolynomial N hN p)

lemma lpsOriginalGaussAffineOrder_domain
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    IsDomain (LPSOriginalGaussAffineOrder N hN p) := by
  let := lpsOriginalGaussBase_dvr p
  exact AdjoinRoot.isDomain_of_prime
    (lpsOriginalGaussPolynomial_irreducible N hN p).prime

lemma lpsOriginalGaussAffineOrder_dedekind
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    IsDedekindDomain (LPSOriginalGaussAffineOrder N hN p) := by
  let := lpsOriginalGaussBase_dvr p
  let := lpsOriginalGaussAffineOrder_domain N hN p
  let : Module.Finite (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let := lpsOriginalGaussAffineOrder_formallyUnramified N hN p hpN
  exact isDedekindDomain.of_formallyUnramified (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder N hN p)

lemma lpsOriginalGaussAffineOrder_integrallyClosed
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    IsIntegrallyClosed (LPSOriginalGaussAffineOrder N hN p) := by
  let := lpsOriginalGaussAffineOrder_dedekind N hN p hpN
  infer_instance


def lpsOriginalGaussBaseOriginalEval (p : ℕ) [Fact p.Prime] :
    LPSOriginalGaussBase p →+* LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.comp (lpsOriginalGaussBaseFractionMap p)

lemma lpsOriginalGaussPolynomial_originalRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (lpsOriginalGaussPolynomial N hN p).eval₂
      (lpsOriginalGaussBaseOriginalEval p) (lpsOriginalJNInFractionField N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalGaussBaseOriginalEval,← Polynomial.eval₂_map,
    lpsOriginalGaussPolynomial_fractionDiagram,
    lpsOriginalIntegerPolynomial_minpoly N hN]
  change Polynomial.aeval (lpsOriginalJNInFractionField N hN)
    (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)) = 0
  exact minpoly.aeval _ _

def lpsOriginalGaussAffineOrder_originalEval
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    LPSOriginalGaussAffineOrder N hN p →+* LPSOriginalHolomorphicFractionField :=
  AdjoinRoot.lift (lpsOriginalGaussBaseOriginalEval p)
    (lpsOriginalJNInFractionField N hN)
    (lpsOriginalGaussPolynomial_originalRoot N hN p)

lemma lpsOriginalGaussAffineOrder_originalEval_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    lpsOriginalGaussAffineOrder_originalEval N hN p
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) =
    lpsOriginalJNInFractionField N hN := AdjoinRoot.lift_root _

lemma lpsOriginalGaussAffineOrder_originalEval_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalGaussAffineOrder_originalEval N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih q =>
    rw [lpsOriginalGaussAffineOrder_originalEval,AdjoinRoot.lift_mk] at hx
    apply AdjoinRoot.mk_eq_zero.mpr
    have hm : (lpsOriginalGaussPolynomial N hN p).Monic :=
      (lpsOriginalIntegerPolynomial_monic N hN).map _
    rw [← Polynomial.map_dvd_map (lpsOriginalGaussBaseFractionMap p)
      (lpsOriginalGaussBaseFractionMap_injective p)
      hm,
      lpsOriginalGaussPolynomial_fractionDiagram,
      lpsOriginalIntegerPolynomial_minpoly N hN,minpoly.dvd_iff]
    rw [Polynomial.aeval_def,Polynomial.eval₂_map]
    change q.eval₂ (lpsOriginalJFractionEmbeddingQ.comp
      (lpsOriginalGaussBaseFractionMap p)) (lpsOriginalJNInFractionField N hN) = 0
    exact hx

-- This map is induced by the same original polynomial and sends its root to the same root.
def lpsOriginalIntegerAffineToGauss
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    lpsOriginalIntegerAffineRing N hN →+* LPSOriginalGaussAffineOrder N hN p :=
  AdjoinRoot.map (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))
    (lpsOriginalIntegerPolynomial N hN) (lpsOriginalGaussPolynomial N hN p)
    dvd_rfl


open scoped TensorProduct

-- This is a proved comparison to base change of the SAME original integer affine order.
def lpsOriginalGaussAffineOrder_baseChangeEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (LPSOriginalGaussBase p ⊗[Polynomial ℤ] lpsOriginalIntegerAffineRing N hN) ≃ₐ[
      LPSOriginalGaussBase p] LPSOriginalGaussAffineOrder N hN p :=
  QEC.Coding.AlgebraicGeometry.adjoinRoot_baseChangeEquiv
    (Polynomial ℤ) (LPSOriginalGaussBase p) (lpsOriginalIntegerPolynomial N hN)

lemma lpsOriginalGaussAffineOrder_baseChangeEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    lpsOriginalGaussAffineOrder_baseChangeEquiv N hN p
      (1 ⊗ₜ[Polynomial ℤ] AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN)) =
    AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by
  exact QEC.Coding.AlgebraicGeometry.adjoinRoot_baseChangeEquiv_root
    (Polynomial ℤ) (LPSOriginalGaussBase p) (lpsOriginalIntegerPolynomial N hN)


lemma lpsOriginalGaussAffineOrder_isLocalization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let : Algebra (lpsOriginalIntegerAffineRing N hN)
        (LPSOriginalGaussAffineOrder N hN p) :=
      (lpsOriginalIntegerAffineToGauss N hN p).toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (lpsOriginalIntegerAffineRing N hN)
        (lpsOriginalGaussPrime p).primeCompl)
      (LPSOriginalGaussAffineOrder N hN p) :=
  QEC.Coding.AlgebraicGeometry.adjoinRoot_baseChange_isLocalization
    (Polynomial ℤ) (LPSOriginalGaussBase p)
    (lpsOriginalGaussPrime p).primeCompl (lpsOriginalIntegerPolynomial N hN)


def lpsOriginalGaussAffineToGenerated
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalGaussAffineOrder N hN p →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI : Algebra (lpsOriginalIntegerAffineRing N hN)
      (LPSOriginalGaussAffineOrder N hN p) :=
    (lpsOriginalIntegerAffineToGauss N hN p).toAlgebra
  letI := lpsOriginalGaussAffineOrder_domain N hN p
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (lpsOriginalIntegerAffineRing N hN)
        (lpsOriginalGaussPrime p).primeCompl)
      (LPSOriginalGaussAffineOrder N hN p) :=
    lpsOriginalGaussAffineOrder_isLocalization N hN p
  let M := Algebra.algebraMapSubmonoid (lpsOriginalIntegerAffineRing N hN)
    (lpsOriginalGaussPrime p).primeCompl
  apply IsLocalization.lift (M := M) (S := LPSOriginalGaussAffineOrder N hN p)
    (g := lpsOriginalIntegerAffineToGenerated N hN)
  intro t
  apply isUnit_iff_ne_zero.mpr
  intro ht
  have hz : (t : lpsOriginalIntegerAffineRing N hN) = 0 :=
    lpsOriginalIntegerAffineToGenerated_injective N hN
      (ht.trans (lpsOriginalIntegerAffineToGenerated N hN).map_zero.symm)
  have hu := IsLocalization.map_units (M := M) (LPSOriginalGaussAffineOrder N hN p) t
  rw [hz,map_zero] at hu
  exact not_isUnit_zero hu

lemma lpsOriginalGaussAffineToGenerated_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (x : lpsOriginalIntegerAffineRing N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGaussAffineToGenerated N hN p
      (lpsOriginalIntegerAffineToGauss N hN p x) =
    lpsOriginalIntegerAffineToGenerated N hN x := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : Algebra (lpsOriginalIntegerAffineRing N hN)
      (LPSOriginalGaussAffineOrder N hN p) :=
    (lpsOriginalIntegerAffineToGauss N hN p).toAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (lpsOriginalIntegerAffineRing N hN)
        (lpsOriginalGaussPrime p).primeCompl)
      (LPSOriginalGaussAffineOrder N hN p) :=
    lpsOriginalGaussAffineOrder_isLocalization N hN p
  unfold lpsOriginalGaussAffineToGenerated
  exact IsLocalization.lift_eq _ x

lemma lpsOriginalGaussAffineGenerated_isFractionRing
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    IsFractionRing (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (lpsOriginalIntegerAffineRing N hN)
      (LPSOriginalGaussAffineOrder N hN p) :=
    (lpsOriginalIntegerAffineToGauss N hN p).toAlgebra
  let := (lpsOriginalIntegerAffineToGenerated N hN).toAlgebra
  let := lpsOriginalIntegerAffineRing_domain N hN
  let := lpsOriginalGaussAffineOrder_isLocalization N hN p
  let := lpsOriginalIntegerAffineGenerated_isFractionRing N hN
  let : IsScalarTower (lpsOriginalIntegerAffineRing N hN)
      (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (lpsOriginalGaussAffineToGenerated_base N hN p x).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid (lpsOriginalIntegerAffineRing N hN)
      (lpsOriginalGaussPrime p).primeCompl)
    (LPSOriginalGaussAffineOrder N hN p) (lpsOriginalGeneratedFunctionFieldQ N hN)

lemma lpsOriginalGaussAffineOrder_isIntegralClosure
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    IsIntegralClosure (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let := lpsOriginalGaussAffineOrder_domain N hN p
  let := lpsOriginalGaussAffineGenerated_isFractionRing N hN p
  let := lpsOriginalGaussAffineOrder_integrallyClosed N hN p hpN
  let : Module.Finite (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p) :=
    ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  infer_instance


lemma lpsOriginalGaussAffineToGenerated_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGaussAffineToGenerated N hN p
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val) =
      lpsOriginalJNInFractionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [← AdjoinRoot.map_root (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))
    (lpsOriginalIntegerPolynomial N hN) (lpsOriginalGaussPolynomial N hN p) dvd_rfl]
  change (lpsOriginalGaussAffineToGenerated N hN p
    (lpsOriginalIntegerAffineToGauss N hN p
      (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN)))).val = _
  rw [lpsOriginalGaussAffineToGenerated_base]
  change lpsOriginalIntegerAffineLocalizedEval N hN
    (AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN)) = _
  simp [lpsOriginalIntegerAffineLocalizedEval,lpsOriginalIntegerAffineEval,
    lpsOriginalJNInFractionField]

def lpsOriginalGaussNormalizationEquiv
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    LPSOriginalGaussAffineOrder N hN p ≃ₐ[LPSOriginalGaussBase p]
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  letI : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  letI := lpsOriginalGaussAffineOrder_isIntegralClosure N hN p hpN
  exact IsIntegralClosure.equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder N hN p) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN))

lemma lpsOriginalGaussNormalizationEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    ((lpsOriginalGaussNormalizationEquiv N hN p hpN
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val) =
      lpsOriginalJNInFractionField N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ((lpsOriginalGaussAffineToGenerated N hN p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let := lpsOriginalGaussAffineOrder_isIntegralClosure N hN p hpN
  have he := IsIntegralClosure.algebraMap_equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder N hN p) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN))
    (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))
  change (lpsOriginalGaussNormalizationEquiv N hN p hpN
    (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val = _ at he
  exact (congrArg Subtype.val he).trans (lpsOriginalGaussAffineToGenerated_root N hN p)

end
end QEC.Coding.TannerLiftedProduct

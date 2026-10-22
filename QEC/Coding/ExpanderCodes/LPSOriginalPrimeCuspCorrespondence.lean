import QEC.Coding.ExpanderCodes.LPSOriginalPrimeModularBranches
import QEC.Coding.ExpanderCodes.LPSOriginalAnalyticCuspLocalization

/-!
# Original prime modular polynomial in cusp-series rings

The pointwise original prime branch product passes through actual localized
analytic functions and their Taylor images. Faithful cyclotomic coefficient
comparison identifies the original integer polynomial with its formal product,
which then reduces in characteristic p.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

def lpsOriginalAnalyticPrimeBranch (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    lpsOriginalAnalyticCuspLaurentRing :=
  match i with
  | none => lpsOriginalAnalyticCuspAffineBranch (p*p)
      (Nat.mul_pos (Fact.out : p.Prime).pos (Fact.out : p.Prime).pos) 0
  | some m => lpsOriginalAnalyticCuspAffineBranch 1 (by decide) ((m.val:ℚ)/p)

def lpsOriginalAnalyticPrimeJ (p : ℕ) [Fact p.Prime] :
    lpsOriginalAnalyticCuspLaurentRing :=
  lpsOriginalAnalyticCuspAffineBranch p (Fact.out : p.Prime).pos 0

lemma lpsOriginalAnalyticPrimeJ_nome (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticPrimeJ p)=
      lpsOriginalJInvariant (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ) := by
  change lpsOriginalAnalyticCuspLocalizedNomeEval τ
    (lpsOriginalAnalyticCuspAffineBranch p (Fact.out : p.Prime).pos 0)=_
  have h:=lpsOriginalAnalyticCuspAffineBranch_nome p (Fact.out : p.Prime).pos 0 τ
  simpa only [Rat.cast_zero] using h

lemma lpsOriginalAnalyticPrimeBranch_nome (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticPrimeBranch p i)=
      lpsOriginalPrimeBranch p i (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ) := by
  cases i with
  | none =>
    rw [lpsOriginalAnalyticPrimeBranch,lpsOriginalAnalyticCuspAffineBranch_nome,
      lpsOriginalPrimeBranch_infty]
    apply congrArg lpsOriginalJInvariant
    apply UpperHalfPlane.ext
    simp only [lpsE2AffineMatrix_action,Nat.cast_mul,Complex.ofReal_zero,add_zero]
    norm_num [mul_assoc]
  | some m =>
    rw [lpsOriginalAnalyticPrimeBranch,lpsOriginalAnalyticCuspAffineBranch_nome]
    apply congrArg lpsOriginalJInvariant
    apply UpperHalfPlane.ext
    rw [lpsE2AffineMatrix_action,lpsOriginalPrimeBranch_finite_point,lpsOriginalJDilated_coe]
    simp only [Nat.cast_one,one_mul]
    push_cast
    have hp : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp [hp]

def lpsOriginalAnalyticPrimeCoefficientEval (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* lpsOriginalAnalyticCuspLaurentRing :=
  Polynomial.eval₂RingHom (Int.castRingHom lpsOriginalAnalyticCuspLaurentRing)
    (lpsOriginalAnalyticPrimeJ p)

lemma lpsOriginalAnalyticPrimeCoefficientEval_nome (p : ℕ) [Fact p.Prime] (τ : ℍ) :
    (lpsOriginalAnalyticCuspLocalizedNomeEval τ).comp
      (lpsOriginalAnalyticPrimeCoefficientEval p)=
    (Polynomial.evalRingHom
      (lpsOriginalJInvariant (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ))).comp
      (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
  ext
  · simp [lpsOriginalAnalyticPrimeCoefficientEval]
  · simp [lpsOriginalAnalyticPrimeCoefficientEval,lpsOriginalAnalyticPrimeJ_nome]

lemma lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct (p : ℕ) [Fact p.Prime] :
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalAnalyticPrimeCoefficientEval p)).map lpsOriginalAnalyticCuspLocalizedTaylor=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticPrimeBranch p i))) := by
  classical
  let D := (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalAnalyticPrimeCoefficientEval p)-
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalAnalyticPrimeBranch p i))
  have hzero : D.map lpsOriginalAnalyticCuspLocalizedTaylor=0 := by
    ext k
    rw [Polynomial.coeff_map,Polynomial.coeff_zero]
    apply lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
    intro τ
    rw [←Polynomial.coeff_map]
    have hc : D.map (lpsOriginalAnalyticCuspLocalizedNomeEval τ)=0 := by
      dsimp only [D]
      rw [Polynomial.map_sub,Polynomial.map_map,
        lpsOriginalAnalyticPrimeCoefficientEval_nome,Polynomial.map_prod]
      have h:=lpsOriginalPrimeIntegerPolynomial_pointwiseProduct p
        (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ)
      rw [h]
      apply sub_eq_zero.mpr
      apply Finset.prod_congr rfl
      intro i _
      rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
        lpsOriginalAnalyticPrimeBranch_nome]
    rw [hc,Polynomial.coeff_zero]
  dsimp only [D] at hzero
  rw [Polynomial.map_sub,Polynomial.map_prod] at hzero
  simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    using sub_eq_zero.mp hzero

lemma lpsOriginalCyclotomicComplexRoot_phase (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (lpsOriginalCyclotomicComplexRoot p)^m=
      Function.Periodic.qParam 1 (((((m:ℚ)/(p:ℚ)):ℚ)):ℂ) := by
  rw [lpsOriginalCyclotomicComplexRoot,←Complex.exp_nat_mul]
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one,Rat.cast_div,Rat.cast_natCast]
  congr 1
  ring

lemma lpsOriginalCyclotomicFiniteCuspBranch_complex (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCyclotomicFiniteCuspBranch p m)=
      lpsOriginalAnalyticCuspLocalizedTaylor
        (lpsOriginalAnalyticCuspAffineBranch 1 (by decide) ((m:ℚ)/p)) := by
  rw [lpsOriginalCyclotomicFiniteCuspBranch,map_mul,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    map_mul,PowerSeries.map_C,pow_mul,map_pow,
    lpsOriginalCyclotomicComplexEmbedding_root_inverse]
  have he : lpsOriginalCyclotomicComplexEmbedding p
      ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)=
      (lpsOriginalCyclotomicComplexRoot p)^m := by
    rw [map_pow,lpsOriginalCyclotomicComplexEmbedding_root]
  rw [←PowerSeries.rescale_map,he,lpsOriginalCuspCoefficientMap_integerNumerator,
    lpsOriginalAnalyticCuspAffineBranch_taylor]
  have hK : lpsOriginalCuspJNumerator ℂ=lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by
    exact lpsOriginalJZSeries_mapC
  rw [hK,inv_pow]
  simp only [lpsOriginalCyclotomicComplexRoot_phase,PowerSeries.expand_one_apply,pow_one]

def lpsOriginalCyclotomicPrimeCoefficientEval (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p) :=
  Polynomial.eval₂RingHom
    (Int.castRingHom (lpsOriginalCuspSeriesRing (lpsOriginalCyclotomicCoefficientRing p)))
    (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) p (Fact.out : p.Prime).ne_zero)

lemma lpsOriginalCyclotomicPrimeCoefficientEval_complex (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)).comp
      (lpsOriginalCyclotomicPrimeCoefficientEval p)=
    lpsOriginalAnalyticCuspLocalizedTaylor.comp (lpsOriginalAnalyticPrimeCoefficientEval p) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalCyclotomicPrimeCoefficientEval,lpsOriginalAnalyticPrimeCoefficientEval]
  · simp only [RingHom.comp_apply,lpsOriginalCyclotomicPrimeCoefficientEval,
      lpsOriginalAnalyticPrimeCoefficientEval,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) p
        (Fact.out : p.Prime).ne_zero)=
      lpsOriginalAnalyticCuspLocalizedTaylor
        (lpsOriginalAnalyticCuspAffineBranch p (Fact.out : p.Prime).pos 0)
    rw [lpsOriginalCuspCoefficientMap_jWidth,lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase]

lemma lpsOriginalCyclotomicFormalPrimeProduct_complex (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicFormalPrimeProduct p).map
      (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p))=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticPrimeBranch p i))) := by
  classical
  rw [lpsOriginalCyclotomicFormalPrimeProduct,Polynomial.map_mul,Fintype.prod_option]
  congr 1
  · rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      lpsOriginalCuspCoefficientMap_jWidth,lpsOriginalAnalyticPrimeBranch,
      lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase]
  · rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro m _
    rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      lpsOriginalCyclotomicFiniteCuspBranch_complex,lpsOriginalAnalyticPrimeBranch]

lemma lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalCyclotomicPrimeCoefficientEval p)=
      lpsOriginalCyclotomicFormalPrimeProduct p := by
  apply Polynomial.map_injective
    (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p))
    (lpsOriginalCuspCoefficientMap_injective (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCyclotomicComplexEmbedding_injective p))
  rw [Polynomial.map_map,lpsOriginalCyclotomicPrimeCoefficientEval_complex,
    lpsOriginalCyclotomicFormalPrimeProduct_complex,←Polynomial.map_map]
  exact lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct p

def lpsOriginalModPrimeCoefficientEval (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (ZMod p) :=
  Polynomial.eval₂RingHom (Int.castRingHom (lpsOriginalCuspSeriesRing (ZMod p)))
    (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)

lemma lpsOriginalModPrimeCoefficientEval_reduction (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicCuspReduction p).comp (lpsOriginalCyclotomicPrimeCoefficientEval p)=
      lpsOriginalModPrimeCoefficientEval p := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalCyclotomicPrimeCoefficientEval,lpsOriginalModPrimeCoefficientEval]
  · simp only [RingHom.comp_apply,lpsOriginalCyclotomicPrimeCoefficientEval,
      lpsOriginalModPrimeCoefficientEval,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p)
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) p
        (Fact.out : p.Prime).ne_zero)=lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero
    exact lpsOriginalCuspCoefficientMap_jWidth _ p _

lemma lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalModPrimeCoefficientEval p)=
      (Polynomial.X-Polynomial.C
          ((lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p)) *
        (Polynomial.X^p-Polynomial.C
          (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)) := by
  have h:=congrArg (Polynomial.map (lpsOriginalCyclotomicCuspReduction p))
    (lpsOriginalPrimeIntegerPolynomial_cyclotomicFormalProduct p)
  rw [Polynomial.map_map,lpsOriginalModPrimeCoefficientEval_reduction,
    lpsOriginalCyclotomicFormalPrimeProduct_reduction] at h
  exact h

end
end QEC.Coding.TannerLiftedProduct

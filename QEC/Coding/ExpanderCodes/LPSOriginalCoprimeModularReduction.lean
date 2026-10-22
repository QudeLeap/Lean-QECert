import QEC.Coding.ExpanderCodes.LPSOriginalIntegerAffineModel
import QEC.Coding.ExpanderCodes.LPSOriginalCosetCuspSeries
import QEC.Coding.ExpanderCodes.LPSOriginalAnalyticCuspLocalization

/-!
# Coprime reduction of the original modular polynomial

The original monic integer polynomial is identified with the full actual
inverse Gamma0-coset branch product through localized analytic Taylor
comparison and the faithful integral phase algebra. Its coefficient
specialization factors into distinct entire residue Laurent series when
p does not divide the positive level N. Faithful pole evaluation then
proves the original reduced polynomial separable over F_p(X).

This internal proof supports the original-model arithmetic route behind
pinned PK22 ex:Xpq, main.tex:484-486, and th:qLDPC, main.tex:231-238.
It does not prove Gauss unramifiedness, uniform good reduction,
Hecke/Frobenius/Weil, spectra or the explicit quantum family.
-/

open Filter Topology
open scoped UpperHalfPlane MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

lemma lpsOriginalIntegerPolynomial_pointwiseProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) (τ : ℍ) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalJDilated N hN (x.out.val⁻¹ • τ))) := by
  have hc : (((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ))).comp
      (Polynomial.mapRingHom (algebraMap ℤ ℚ))) =
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change ((P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).eval
      (lpsOriginalJInvariant τ) = (P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.map_map]
    have he : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := by
      ext z
      simp
    rw [he]
  have h := lpsOriginalRationalRelation_pointwiseProduct N hN
    (lpsOriginalIntegerPolynomialRational N hN)
    (lpsOriginalIntegerPolynomialRational_monic N hN)
    (lpsOriginalIntegerPolynomialRational_degree N hN)
    (lpsOriginalIntegerPolynomialRational_root N hN) τ
  rw [lpsOriginalIntegerPolynomialRational,Polynomial.map_map,hc] at h
  exact h

def lpsOriginalAnalyticCosetBranch
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalAnalyticCuspLaurentRing :=
  lpsOriginalAnalyticCuspAffineBranch (lpsOriginalCosetCuspWitness N hN x).1.val
    (lpsOriginalCosetCuspWitness N hN x).1.property
    (lpsOriginalCosetCuspWitness N hN x).2.val

lemma lpsOriginalAnalyticCosetBranch_nome
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticCosetBranch N hN x) =
      lpsOriginalJDilated N hN (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • τ)) := by
  rw [lpsOriginalAnalyticCosetBranch,lpsOriginalAnalyticCuspAffineBranch_nome]
  exact ((lpsOriginalCosetCuspWitness N hN x).2.property.2.2 τ).symm

def lpsOriginalAnalyticLevelCoefficientEval (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalAnalyticCuspLaurentRing :=
  Polynomial.eval₂RingHom (Int.castRingHom lpsOriginalAnalyticCuspLaurentRing)
    (lpsOriginalAnalyticCuspAffineBranch N hN 0)

lemma lpsOriginalAnalyticLevelCoefficientEval_nome
    (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    (lpsOriginalAnalyticCuspLocalizedNomeEval τ).comp
      (lpsOriginalAnalyticLevelCoefficientEval N hN) =
      (Polynomial.evalRingHom (lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • τ))).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
  ext
  · simp [lpsOriginalAnalyticLevelCoefficientEval]
  · simp [lpsOriginalAnalyticLevelCoefficientEval,
      lpsOriginalAnalyticCuspAffineBranch_nome]

lemma lpsOriginalIntegerPolynomial_actualCosetTaylorProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    ((lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalAnalyticLevelCoefficientEval N hN)).map
        lpsOriginalAnalyticCuspLocalizedTaylor =
      ∏ x : LPSOriginalCuspIndex N, (Polynomial.X - Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCosetBranch N hN x))) := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  let D := (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalAnalyticLevelCoefficientEval N hN) -
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalAnalyticCosetBranch N hN x))
  have hzero : D.map lpsOriginalAnalyticCuspLocalizedTaylor = 0 := by
    ext k
    rw [Polynomial.coeff_map,Polynomial.coeff_zero]
    apply lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
    intro τ
    rw [← Polynomial.coeff_map]
    have hc : D.map (lpsOriginalAnalyticCuspLocalizedNomeEval τ) = 0 := by
      dsimp only [D]
      rw [Polynomial.map_sub,Polynomial.map_map,
        lpsOriginalAnalyticLevelCoefficientEval_nome,Polynomial.map_prod]
      rw [lpsOriginalIntegerPolynomial_pointwiseProduct N hN
        (lpsE2AffineMatrix N hN 0 • τ)]
      apply sub_eq_zero.mpr
      apply Finset.prod_congr rfl
      intro x _
      rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
        lpsOriginalAnalyticCosetBranch_nome]
    rw [hc,Polynomial.coeff_zero]
  dsimp only [D] at hzero
  rw [Polynomial.map_sub,Polynomial.map_prod] at hzero
  simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    using sub_eq_zero.mp hzero


lemma lpsOriginalCosetIntegralCuspSeries_complex
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom
      (lpsOriginalCosetIntegralCuspSeries N hN x) =
      lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCosetBranch N hN x) := by
  rw [lpsOriginalCosetIntegralCuspSeries,lpsOriginalPhaseCuspSeries_map]
  change lpsOriginalPhaseCuspSeries ℂ N
    (lpsOriginalCosetCuspWitness N hN x).1.val
    (lpsOriginalCosetCuspWitness N hN x).1.property.ne'
    (Function.Periodic.qParam 1 ((lpsOriginalCosetCuspWitness N hN x).2.val : ℂ)) = _
  rw [lpsOriginalPhaseCuspSeries,lpsOriginalPhaseCuspNumerator_taylor N hN]
  · rw [lpsOriginalAnalyticCosetBranch,lpsOriginalAnalyticCuspAffineBranch,
      map_mul,map_pow,lpsOriginalAnalyticCuspLocalizedTaylor_invParameter,
      lpsOriginalAnalyticCuspLocalizedTaylor_function]
    rfl
  · exact (lpsOriginalCosetCuspWitness N hN x).2.property.2.1

def lpsOriginalIntegralLevelCoefficientEval (N : ℕ) (hN : 0 < N) :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (lpsOriginalLevelPhaseRing N) :=
  Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalCuspJWidth (lpsOriginalLevelPhaseRing N) N hN.ne')

lemma lpsOriginalIntegralLevelCoefficientEval_complex
    (N : ℕ) (hN : 0 < N) :
    (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom).comp
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      lpsOriginalAnalyticCuspLocalizedTaylor.comp
        (lpsOriginalAnalyticLevelCoefficientEval N hN) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalIntegralLevelCoefficientEval,
      lpsOriginalAnalyticLevelCoefficientEval]
  · simp only [RingHom.comp_apply,lpsOriginalIntegralLevelCoefficientEval,
      lpsOriginalAnalyticLevelCoefficientEval,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rw [lpsOriginalCuspCoefficientMap_jWidth,
      lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase]


lemma lpsOriginalLevelPhaseRing_complexEmbedding_injective (N : ℕ) :
    Function.Injective (lpsOriginalLevelPhaseRing N).val.toRingHom := by
  intro x y hxy
  exact Subtype.ext hxy

lemma lpsOriginalIntegralCuspComplexMap_injective (N : ℕ) :
    Function.Injective (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom) :=
  lpsOriginalCuspCoefficientMap_injective
    (R := lpsOriginalLevelPhaseRing N) (S := ℂ) (lpsOriginalLevelPhaseRing N).val.toRingHom
    (lpsOriginalLevelPhaseRing_complexEmbedding_injective N)

lemma lpsOriginalIntegerPolynomial_integralCosetProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalCosetIntegralCuspSeries N hN x)) := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  apply Polynomial.map_injective
    (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom)
    (lpsOriginalIntegralCuspComplexMap_injective N)
  rw [Polynomial.map_map,lpsOriginalIntegralLevelCoefficientEval_complex,
    ← Polynomial.map_map,Polynomial.map_prod]
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    lpsOriginalCosetIntegralCuspSeries_complex]
  exact lpsOriginalIntegerPolynomial_actualCosetTaylorProduct N hN

def lpsOriginalResidueLevelCoefficientEval
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    Polynomial ℤ →+* lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp) :=
  Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalCuspJWidth (LPSOriginalLevelPhaseResidue N hN p hp) N hN.ne')

lemma lpsOriginalIntegralLevelCoefficientEval_reduction
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    (lpsOriginalCuspCoefficientMap (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp))).comp
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      lpsOriginalResidueLevelCoefficientEval N hN p hp := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalIntegralLevelCoefficientEval,
      lpsOriginalResidueLevelCoefficientEval]
  · simp only [RingHom.comp_apply,lpsOriginalIntegralLevelCoefficientEval,
      lpsOriginalResidueLevelCoefficientEval,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    exact lpsOriginalCuspCoefficientMap_jWidth _ N hN.ne'

lemma lpsOriginalIntegerPolynomial_residueCosetProduct
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalResidueLevelCoefficientEval N hN p hp) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalCosetResidueCuspSeries N hN p hp x)) := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  have h := congrArg (Polynomial.map
    (lpsOriginalCuspCoefficientMap (Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp))))
    (lpsOriginalIntegerPolynomial_integralCosetProduct N hN)
  rw [Polynomial.map_map,lpsOriginalIntegralLevelCoefficientEval_reduction,
    Polynomial.map_prod] at h
  simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    lpsOriginalCosetCuspSeries_reduction] using h


local instance lpsOriginalFieldCuspSeries_domain
    (K : Type*) [Field K] : IsDomain (lpsOriginalCuspSeriesRing K) :=
  Localization.Away.isDomain PowerSeries.X_ne_zero

def lpsOriginalFieldLevelJPolynomialEval
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    Polynomial K →+* lpsOriginalCuspSeriesRing K :=
  Polynomial.eval₂RingHom
    ((algebraMap (PowerSeries K) (lpsOriginalCuspSeriesRing K)).comp PowerSeries.C)
    (lpsOriginalCuspJWidth K N hN.ne')

lemma lpsOriginalFieldLevelJPolynomialEval_injective
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalFieldLevelJPolynomialEval K N hN) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hF : PowerSeries.constantCoeff
      (PowerSeries.expand N hN.ne' (lpsOriginalCuspJNumerator K)) = 1 := by
    rw [PowerSeries.constantCoeff_expand,lpsOriginalCuspJNumerator_constant]
  apply (lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
    (PowerSeries.expand N hN.ne' (lpsOriginalCuspJNumerator K)) hF N hN P).mp
  simpa only [lpsOriginalFieldLevelJPolynomialEval,Polynomial.coe_eval₂RingHom,
    lpsOriginalCuspJWidth] using hP

lemma lpsOriginalIntegerPolynomial_residueFractionSeparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ((lpsOriginalIntegerPolynomial N hN).map
      ((algebraMap (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp))
          (FractionRing (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp)))).comp
        (lpsOriginalResidueLevelCoefficientEval N hN p hp))).Separable := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  rw [← Polynomial.map_map,lpsOriginalIntegerPolynomial_residueCosetProduct,
    Polynomial.map_prod]
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
  apply Polynomial.separable_prod_X_sub_C_iff.mpr
  exact (IsFractionRing.injective
    (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp))
    (FractionRing (lpsOriginalCuspSeriesRing (LPSOriginalLevelPhaseResidue N hN p hp)))).comp
    (lpsOriginalCosetResidueCuspSeries_injective N hN p hp hpN)


def lpsOriginalModularPolynomialModFraction
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Polynomial (FractionRing (Polynomial (ZMod p))) :=
  (lpsOriginalIntegerPolynomial N hN).map
    ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p))))

lemma lpsOriginalModularPolynomialModFraction_separable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (lpsOriginalModularPolynomialModFraction N hN p).Separable := by
  let hp : p.Prime := Fact.out
  let K := LPSOriginalLevelPhaseResidue N hN p hp
  let : CharP K p := lpsOriginalLevelPhaseResidue_charP N hN p hp
  let L := FractionRing (lpsOriginalCuspSeriesRing K)
  let κ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  let e : Polynomial (ZMod p) →+* lpsOriginalCuspSeriesRing K :=
    (lpsOriginalFieldLevelJPolynomialEval K N hN).comp (Polynomial.mapRingHom κ)
  have he : Function.Injective e :=
    (lpsOriginalFieldLevelJPolynomialEval_injective K N hN).comp
      (Polynomial.map_injective κ (ZMod.castHom_injective K))
  let g : Polynomial (ZMod p) →+* L :=
    (algebraMap (lpsOriginalCuspSeriesRing K) L).comp e
  have hg : Function.Injective g :=
    (IsFractionRing.injective (lpsOriginalCuspSeriesRing K) L).comp he
  let f : FractionRing (Polynomial (ZMod p)) →+* L := IsFractionRing.lift hg
  have hc : f.comp
      ((algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      (algebraMap (lpsOriginalCuspSeriesRing K) L).comp
        (lpsOriginalResidueLevelCoefficientEval N hN p hp) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [f,g,e,κ,lpsOriginalFieldLevelJPolynomialEval,
        lpsOriginalResidueLevelCoefficientEval]
    · simp [f,g,e,κ,lpsOriginalFieldLevelJPolynomialEval,
        lpsOriginalResidueLevelCoefficientEval]
      rfl
  apply (Polynomial.separable_map f).mp
  rw [lpsOriginalModularPolynomialModFraction,Polynomial.map_map,hc]
  exact lpsOriginalIntegerPolynomial_residueFractionSeparable N hN p hp hpN

end
end QEC.Coding.TannerLiftedProduct

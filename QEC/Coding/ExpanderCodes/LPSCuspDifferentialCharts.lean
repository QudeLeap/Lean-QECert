import QEC.Coding.ExpanderCodes.LPSCuspDifferential
import QEC.Coding.ExpanderCodes.LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope

/-!
# LPSCuspDifferentialCharts

The genuine exponential q-coordinate derivative identifies the same original differential with its regular coefficient. Actual cusp vanishing and a removable divided difference prove regularity at infinity and every original integral cusp translate, using the common positive width N.
No differential law, regularity or Hecke pullback conclusion is assumed.
The algebraic modular curve, arithmetic magnitude bound and public PK22 theorem remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section

/-- The actual q-chart coefficient with the removable singularity filled by its derivative. -/
def lpsCuspQDifferentialCoefficient (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (q : ℂ) : ℂ :=
  ((2:ℂ)*Real.pi*I)⁻¹*dslope (UpperHalfPlane.cuspFunction 1 f) 0 q

/-- Actual cusp vanishing removes the apparent differential pole at infinity. -/
lemma lpsCuspQDifferentialCoefficient_analyticAt_zero (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    AnalyticAt ℂ (lpsCuspQDifferentialCoefficient N f) 0 := by
  have hper : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  obtain ⟨P,hP⟩ := ModularFormClass.analyticAt_cuspFunction_zero f (by norm_num : (0:ℝ)<1) hper
  have ha : AnalyticAt ℂ (dslope (UpperHalfPlane.cuspFunction 1 f) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  exact analyticAt_const.mul ha

/-- The regular q coefficient represents the SAME actual differential on the upper half-plane. -/
lemma lpsCuspQDifferentialCoefficient_qParam (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (τ : ℍ) :
    lpsCuspQDifferentialCoefficient N f (Function.Periodic.qParam 1 τ) =
      f τ / (((2:ℂ)*Real.pi*I)*Function.Periodic.qParam 1 τ) := by
  have hper : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hf0 := CuspFormClass.cuspFunction_apply_zero f (by norm_num : (0:ℝ)<1) hper
  have hq : Function.Periodic.qParam 1 (τ:ℂ)≠0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  rw [lpsCuspQDifferentialCoefficient,dslope_of_ne _ hq]
  rw [slope,hf0]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [UpperHalfPlane.eq_cuspFunction τ (by norm_num : (1:ℝ)≠0)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hper)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual regular q-chart coefficient at every original integral cusp representative.
The common width is N; no unproved cusp regularity is stored. -/
def lpsCuspTranslateQDifferentialCoefficient (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) : ℂ :=
  (N:ℂ) / ((2:ℂ)*Real.pi*I) *
    dslope (UpperHalfPlane.cuspFunction (N:ℝ)
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0 q

/-- Genuine cusp vanishing makes the differential coefficient regular at every rational cusp. -/
lemma lpsCuspTranslateQDifferentialCoefficient_analyticAt_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) :
    AnalyticAt ℂ (lpsCuspTranslateQDifferentialCoefficient N f ρ) 0 := by
  have hm : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero
    (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)) hm
    (lpsGamma0Translate_integerPeriod N ρ)
  obtain ⟨P,hP⟩ := ha
  have hd : AnalyticAt ℂ
    (dslope (UpperHalfPlane.cuspFunction (N:ℝ)
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  exact analyticAt_const.mul hd

/-- Away from the cusp the regular coefficient is the same actual slash-translated differential. -/
lemma lpsCuspTranslateQDifferentialCoefficient_qParam (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspTranslateQDifferentialCoefficient N f ρ (Function.Periodic.qParam (N:ℝ) τ) =
      (N:ℂ) * (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ) /
        (((2:ℂ)*Real.pi*I)*Function.Periodic.qParam (N:ℝ) τ) := by
  have hm : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  let ft := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
  have hper := lpsGamma0Translate_integerPeriod N ρ
  have hf0 := CuspFormClass.cuspFunction_apply_zero ft hm hper
  have hq : Function.Periodic.qParam (N:ℝ) (τ:ℂ)≠0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  rw [lpsCuspTranslateQDifferentialCoefficient,dslope_of_ne _ hq]
  change (N:ℂ)/((2:ℂ)*Real.pi*I) *
    slope (UpperHalfPlane.cuspFunction (N:ℝ) ft) 0 (Function.Periodic.qParam (N:ℝ) τ) = _
  rw [slope,hf0]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [UpperHalfPlane.eq_cuspFunction τ hm.ne'
    (SlashInvariantFormClass.periodic_comp_ofComplex ft hper)]
  have he : ft τ = ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ := rfl
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The derivative of the genuine exponential cusp coordinate, with its exact width factor. -/
lemma lpsQParam_deriv (h : ℝ) (z : ℂ) :
    deriv (Function.Periodic.qParam h) z =
      (((2:ℂ)*Real.pi*I)/(h:ℂ))*Function.Periodic.qParam h z := by
  unfold Function.Periodic.qParam
  have hd := (((hasDerivAt_id z).const_mul ((2:ℂ)*Real.pi*I)).div_const (h:ℂ)).cexp
  simpa only [id_eq,one_mul,mul_comm] using hd.deriv

/-- The filled-in coefficient pulls back to the original differential, not just a formal ratio. -/
lemma lpsCuspQDifferentialCoefficient_pullback (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    lpsCuspQDifferentialCoefficient N f (Function.Periodic.qParam 1 τ) *
      (deriv (Function.Periodic.qParam 1) τ*v) = lpsCuspDifferential N f τ v := by
  rw [lpsCuspQDifferentialCoefficient_qParam,lpsQParam_deriv,lpsCuspDifferential_apply]
  have hq := Function.Periodic.qParam_ne_zero (h:=1) (τ:ℂ)
  norm_num only [Complex.ofReal_one,div_one]
  field_simp [Complex.two_pi_I_ne_zero,hq]

/-- At every rational cusp the same regular coefficient pulls back to the true slash differential. -/
lemma lpsCuspTranslateQDifferentialCoefficient_pullback (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) (v : ℂ) :
    lpsCuspTranslateQDifferentialCoefficient N f ρ (Function.Periodic.qParam (N:ℝ) τ) *
      (deriv (Function.Periodic.qParam (N:ℝ)) τ*v) =
      (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ)*v := by
  rw [lpsCuspTranslateQDifferentialCoefficient_qParam,lpsQParam_deriv]
  have hq := Function.Periodic.qParam_ne_zero (h:=(N:ℝ)) (τ:ℂ)
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp [Complex.two_pi_I_ne_zero,hq,hN]

end
end QEC.Coding.TannerLiftedProduct

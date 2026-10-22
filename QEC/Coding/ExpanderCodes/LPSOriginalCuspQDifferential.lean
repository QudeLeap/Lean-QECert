import QEC.Coding.ExpanderCodes.LPSOriginalCuspWidths
import QEC.Coding.ExpanderCodes.LPSCuspDifferentialCharts

/-!
# LPSOriginalCuspQDifferential

Actual minimal widths and original cusp-neighborhood geometry for the same Gamma0 group.
No width, stabilizer, descent, analytic coefficient or quotient topology law is assumed.
These are punctured neighborhoods; cusp filling, analytic gluing, compactness, algebraic
modular curves, arithmetic Hecke/Frobenius correspondence and the PK22 magnitude bound
remain unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

/-- The actual minimal-width removable differential coefficient of the original cusp form. -/
def lpsOriginalCuspQCoefficient (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) : ℂ :=
  ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ) / ((2:ℂ)*Real.pi*I) *
    dslope (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0 q

/-- Genuine cusp vanishing proves analyticity at zero in the actual minimal-width coordinate. -/
lemma lpsOriginalCuspQCoefficient_analyticAt_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : AnalyticAt ℂ (lpsOriginalCuspQCoefficient N f ρ) 0 := by
  have hm := lpsOriginalCuspGroup_width_positive N ρ
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero
    (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)) hm hp
  obtain ⟨P,hP⟩ := ha
  have hd : AnalyticAt ℂ
    (dslope (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0) 0 :=
    ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩
  exact analyticAt_const.mul hd

/-- The removable coefficient equals the same slash differential away from the cusp. -/
lemma lpsOriginalCuspQCoefficient_qParam (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsOriginalCuspQCoefficient N f ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) =
      ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ) *
        (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ) /
        (((2:ℂ)*Real.pi*I)*
          Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) := by
  have hm := lpsOriginalCuspGroup_width_positive N ρ
  let ft := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
  have hp := Subgroup.strictWidthInfty_mem_strictPeriods (lpsOriginalCuspGroup N ρ)
  have hf0 := CuspFormClass.cuspFunction_apply_zero ft hm hp
  have hq := Function.Periodic.qParam_ne_zero
    (h:=(lpsOriginalCuspGroup N ρ).strictWidthInfty) (τ:ℂ)
  rw [lpsOriginalCuspQCoefficient,dslope_of_ne _ hq]
  change ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ)/((2:ℂ)*Real.pi*I) *
    slope (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty ft)
      0 (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) = _
  rw [slope,hf0]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [UpperHalfPlane.eq_cuspFunction τ hm.ne'
    (SlashInvariantFormClass.periodic_comp_ofComplex ft hp)]
  have he : ft τ = ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ := rfl
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual minimal-width coefficient pulls back to the original slash differential. -/
lemma lpsOriginalCuspQCoefficient_pullback (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) (v : ℂ) :
    lpsOriginalCuspQCoefficient N f ρ
      (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty τ) *
      (deriv (Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty) τ*v) =
      (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ)*v := by
  rw [lpsOriginalCuspQCoefficient_qParam,lpsQParam_deriv]
  have hq := Function.Periodic.qParam_ne_zero
    (h:=(lpsOriginalCuspGroup N ρ).strictWidthInfty) (τ:ℂ)
  have hw : ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (lpsOriginalCuspGroup_width_positive N ρ).ne'
  field_simp [Complex.two_pi_I_ne_zero,hq,hw]

end
end QEC.Coding.TannerLiftedProduct

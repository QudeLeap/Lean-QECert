import QEC.Coding.ExpanderCodes.LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# LPSPeterssonMeasure

Finite hyperbolic area of the actual closed modular fundamental domain and
convergence of the actual Petersson integrand. The volume is dxdy/y^2; no
finite-measure hypothesis or exact area formula is assumed.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate

noncomputable section
/-- The inverse-square height density is integrable above every positive height. -/
lemma lpsPetersson_im_inverse_square_integrable (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun y : ℝ => (1/y)^2) (Ioi a) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) ha
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp

/-- The actual inverse-square height density is integrable on the containing vertical strip. -/
lemma lpsPetersson_complex_strip_inverse_square_integrable :
    IntegrableOn (fun z : ℂ => (1/z.im)^2)
      (Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ))) := by
  have hx : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc (-1/2:ℝ) (1/2)) :=
    integrableOn_const (C := (1:ℝ)) (by simp)
  have hy := lpsPetersson_im_inverse_square_integrable (1/2) (by norm_num)
  have hp := hx.mul_prod hy
  simp only [one_mul] at hp
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hp
  exact (Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (measurableSet_Icc.prod measurableSet_Ioi)).integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding |>.mpr hp

/-- The actual closed modular fundamental domain has finite hyperbolic volume. -/
lemma lpsPetersson_fundamentalDomain_volume_finite : (volume : Measure ℍ) ModularGroup.fd < ⊤ := by
  let S : Set ℂ := Complex.measurableEquivRealProd ⁻¹'
    (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ))
  have hsub : UpperHalfPlane.coe '' ModularGroup.fd ⊆ S := by
    rintro z ⟨τ,hτ,rfl⟩
    have hxy := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    have hr := abs_le.mp hτ.2
    change (τ.re,τ.im) ∈ Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ)
    exact ⟨⟨by linarith [hr.1],hr.2⟩,by change (1/2:ℝ)<τ.im; have hp := τ.im_pos; nlinarith⟩
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply lt_of_le_of_lt (lintegral_mono_set hsub)
  have hi := lpsPetersson_complex_strip_inverse_square_integrable
  have hfinite := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfinite
  convert hfinite using 1
  apply setLIntegral_congr_fun ((measurableSet_Icc.prod measurableSet_Ioi).preimage
    Complex.measurableEquivRealProd.measurable)
  intro z hz
  change (z.re,z.im) ∈ Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ) at hz
  have hzpos : 0<z.im := by have h : (1/2:ℝ)<z.im := hz.2;linarith
  simp only [enorm_eq_nnnorm,nnnorm_pow,nnnorm_div,nnnorm_one]

/-- The actual cusp/modular Petersson integrand is integrable on the fundamental domain. -/
lemma lpsWeightTwoCusp_petersson_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (petersson 2 f g) ModularGroup.fd := by
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left 2 _ f g
  have hi : IntegrableOn (fun _ : ℍ => C) ModularGroup.fd :=
    integrableOn_const (ne_of_lt lpsPetersson_fundamentalDomain_volume_finite)
  exact hi.mono' (petersson_continuous 2 (by fun_prop) (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

end
end QEC.Coding.TannerLiftedProduct

import QEC.Coding.ExpanderCodes.LPSOriginalIntegerModularEquation
import QEC.Coding.ExpanderCodes.LPSOriginalCuspSeriesReduction

/-!
# Localized analytic cusp functions and Taylor comparison

Nome evaluation and Taylor expansion extend to the actual analytic cusp ring
with its parameter inverted. Vanishing at all upper-half-plane nomes implies
a zero Taylor image, and genuine affine j branches have their expected images.
-/

namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

abbrev lpsOriginalAnalyticCuspLaurentParameter : lpsOriginalCuspAnalyticSubring :=
  ⟨fun q : ℂ=>q,analyticAt_id⟩

abbrev lpsOriginalAnalyticCuspLaurentRing : Type :=
  Localization.Away lpsOriginalAnalyticCuspLaurentParameter

abbrev lpsOriginalComplexCuspLaurentRing : Type :=
  Localization.Away (PowerSeries.X : PowerSeries ℂ)

lemma lpsOriginalAnalyticCuspLaurentParameter_taylor :
    lpsOriginalCuspTaylorRingHom lpsOriginalAnalyticCuspLaurentParameter=
      PowerSeries.X := by
  change lpsOriginalTaylorSeries (fun q : ℂ=>q)=PowerSeries.X
  simpa only [pow_one] using lpsOriginalTaylorSeries_qpow 1

def lpsOriginalAnalyticCuspLocalizedTaylor :
    lpsOriginalAnalyticCuspLaurentRing →+* lpsOriginalComplexCuspLaurentRing :=
  IsLocalization.Away.lift lpsOriginalAnalyticCuspLaurentParameter
    (g:=(algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing).comp
      lpsOriginalCuspTaylorRingHom)
    (by
      change IsUnit (algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
        (lpsOriginalCuspTaylorRingHom lpsOriginalAnalyticCuspLaurentParameter))
      rw [lpsOriginalAnalyticCuspLaurentParameter_taylor]
      exact IsLocalization.Away.algebraMap_isUnit PowerSeries.X)

def lpsOriginalAnalyticCuspLocalizedNomeEval (τ : ℍ) :
    lpsOriginalAnalyticCuspLaurentRing →+* ℂ :=
  IsLocalization.Away.lift lpsOriginalAnalyticCuspLaurentParameter
    (g:=lpsOriginalCuspEvaluateRingHom (Function.Periodic.qParam 1 (τ:ℂ)))
    (by
      change IsUnit (Function.Periodic.qParam 1 (τ:ℂ))
      exact isUnit_iff_ne_zero.mpr (Function.Periodic.qParam_ne_zero _))

lemma lpsOriginalAnalyticCuspLocalizedTaylor_function
    (F : lpsOriginalCuspAnalyticSubring) :
    lpsOriginalAnalyticCuspLocalizedTaylor
      (algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing F)=
      algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
        (lpsOriginalCuspTaylorRingHom F) :=
  IsLocalization.Away.lift_eq _ _ _

lemma lpsOriginalAnalyticCuspLocalizedNomeEval_function
    (τ : ℍ) (F : lpsOriginalCuspAnalyticSubring) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing F)=
      F.val (Function.Periodic.qParam 1 (τ:ℂ)) :=
  IsLocalization.Away.lift_eq _ _ _

lemma lpsOriginalAnalyticCuspNome_zero_germ (F : lpsOriginalCuspAnalyticSubring)
    (hF : ∀ τ : ℍ,F.val (Function.Periodic.qParam 1 (τ:ℂ))=0) :
    F.val=ᶠ[𝓝 (0:ℂ)]0 := by
  have hDisk : ∀ q : ℂ, ‖q‖<1 → q≠0 → F.val q=0 := by
    intro q hq hq0
    let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqτ : Function.Periodic.qParam 1 (τ:ℂ)=q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    simpa only [hqτ] using hF τ
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖<1 :=
    (isOpen_lt (continuous_norm : Continuous (fun q : ℂ=>‖q‖)) continuous_const).mem_nhds
      (by norm_num : ‖(0:ℂ)‖<1)
  have hp : F.val=ᶠ[𝓝[≠] (0:ℂ)]0 := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
    exact hDisk q hq hq0
  have h0 : F.val 0=0 := tendsto_nhds_unique_of_eventuallyEq
    (F.property.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hp
  filter_upwards [hsmall] with q hq
  by_cases hq0 : q=0
  · subst q;exact h0
  · exact hDisk q hq hq0

lemma lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
    (A : lpsOriginalAnalyticCuspLaurentRing)
    (hA : ∀ τ : ℍ,lpsOriginalAnalyticCuspLocalizedNomeEval τ A=0) :
    lpsOriginalAnalyticCuspLocalizedTaylor A=0 := by
  obtain ⟨n,F,hF⟩:=IsLocalization.Away.surj lpsOriginalAnalyticCuspLaurentParameter A
  have hNome (τ : ℍ) : F.val (Function.Periodic.qParam 1 (τ:ℂ))=0 := by
    have h:=congrArg (lpsOriginalAnalyticCuspLocalizedNomeEval τ) hF
    rw [map_mul,map_pow,hA τ,zero_mul,
      lpsOriginalAnalyticCuspLocalizedNomeEval_function] at h
    exact h.symm
  have hTaylor : lpsOriginalCuspTaylorRingHom F=0 :=
    (lpsOriginalTaylorSeries_zero_iff_germ F.property).mpr
      (lpsOriginalAnalyticCuspNome_zero_germ F hNome)
  have h:=congrArg lpsOriginalAnalyticCuspLocalizedTaylor hF
  rw [map_mul,map_pow,lpsOriginalAnalyticCuspLocalizedTaylor_function,
    lpsOriginalAnalyticCuspLaurentParameter_taylor,
    lpsOriginalAnalyticCuspLocalizedTaylor_function,hTaylor,map_zero] at h
  exact (IsLocalization.Away.algebraMap_isUnit
    (S:=lpsOriginalComplexCuspLaurentRing) (PowerSeries.X : PowerSeries ℂ)).pow n
      |>.mul_right_cancel (h.trans (zero_mul _).symm)

lemma lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=
      (Function.Periodic.qParam 1 (τ:ℂ))⁻¹ := by
  have h:=congrArg (lpsOriginalAnalyticCuspLocalizedNomeEval τ)
    (IsLocalization.Away.mul_invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
      lpsOriginalAnalyticCuspLaurentParameter)
  rw [map_mul,map_one,lpsOriginalAnalyticCuspLocalizedNomeEval_function] at h
  change Function.Periodic.qParam 1 (τ:ℂ)*
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=1 at h
  apply (mul_left_cancel₀ (Function.Periodic.qParam_ne_zero (τ:ℂ)))
  rw [h,mul_inv_cancel₀ (Function.Periodic.qParam_ne_zero (τ:ℂ))]

lemma lpsOriginalAnalyticCuspLocalizedTaylor_invParameter :
    lpsOriginalAnalyticCuspLocalizedTaylor
      (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
        lpsOriginalAnalyticCuspLaurentParameter)=
      IsLocalization.Away.invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ) := by
  have h:=congrArg lpsOriginalAnalyticCuspLocalizedTaylor
    (IsLocalization.Away.mul_invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
      lpsOriginalAnalyticCuspLaurentParameter)
  rw [map_mul,map_one,lpsOriginalAnalyticCuspLocalizedTaylor_function,
    lpsOriginalAnalyticCuspLaurentParameter_taylor] at h
  exact (IsLocalization.Away.algebraMap_isUnit (S:=lpsOriginalComplexCuspLaurentRing)
    (PowerSeries.X : PowerSeries ℂ)).mul_left_cancel
      (h.trans (IsLocalization.Away.mul_invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ)).symm)

def lpsOriginalAnalyticClearedAffineBranch (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalCuspAnalyticSubring :=
  ⟨lpsOriginalClearedAffineCusp m m r,
    lpsOriginalClearedAffineCusp_analytic m m hm.ne' r⟩

def lpsOriginalAnalyticCuspAffineBranch (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalAnalyticCuspLaurentRing :=
  (IsLocalization.Away.invSelf (S:=lpsOriginalAnalyticCuspLaurentRing)
      lpsOriginalAnalyticCuspLaurentParameter)^m *
    algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing
      (lpsOriginalAnalyticClearedAffineBranch m hm r)

lemma lpsOriginalAnalyticCuspAffineBranch_nome (m : ℕ) (hm : 0<m) (r : ℚ) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticCuspAffineBranch m hm r)=
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • τ) := by
  rw [lpsOriginalAnalyticCuspAffineBranch,map_mul,map_pow,
    lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter,
    lpsOriginalAnalyticCuspLocalizedNomeEval_function]
  change (Function.Periodic.qParam 1 (τ:ℂ))⁻¹^m *
    lpsOriginalClearedAffineCusp m m r (Function.Periodic.qParam 1 (τ:ℂ))=_
  rw [lpsOriginalClearedAffineCusp_pullback m m hm le_rfl r τ,
    ←mul_assoc,←mul_pow,inv_mul_cancel₀ (Function.Periodic.qParam_ne_zero (τ:ℂ)),
    one_pow,one_mul]

lemma lpsOriginalAnalyticCuspAffineBranch_taylor (m : ℕ) (hm : 0<m) (r : ℚ) :
    lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCuspAffineBranch m hm r)=
      (IsLocalization.Away.invSelf (S:=lpsOriginalComplexCuspLaurentRing)
        (PowerSeries.X : PowerSeries ℂ))^m *
        algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
          (PowerSeries.C ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) *
            PowerSeries.expand m hm.ne' (PowerSeries.rescale (Function.Periodic.qParam 1 (r:ℂ))
              (lpsOriginalTaylorSeries lpsOriginalJQCoefficient))) := by
  rw [lpsOriginalAnalyticCuspAffineBranch,map_mul,map_pow,
    lpsOriginalAnalyticCuspLocalizedTaylor_invParameter,
    lpsOriginalAnalyticCuspLocalizedTaylor_function]
  change _ * algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
    (lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp m m r))=_
  have hf : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient
      (Function.Periodic.qParam 1 (r:ℂ)*q)) 0 :=
    lpsOriginalJQCoefficient_analytic_zero.fun_comp_of_eq
      (analyticAt_const.mul analyticAt_id) (mul_zero _)
  rw [lpsOriginalClearedAffineCusp_taylor m m hm.ne',Nat.sub_self,pow_zero,one_mul,
    lpsOriginalTaylorSeries_comp_pow hf m hm.ne',
    lpsOriginalTaylorSeries_comp_const_mul lpsOriginalJQCoefficient_analytic_zero]

lemma lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase (m : ℕ) (hm : 0<m) :
    lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCuspAffineBranch m hm 0)=
      lpsOriginalCuspJWidth ℂ m hm.ne' := by
  rw [lpsOriginalAnalyticCuspAffineBranch_taylor]
  have hz : Function.Periodic.qParam 1 ((0:ℚ):ℂ)=1 := by
    simp [Function.Periodic.qParam]
  rw [hz,inv_one,map_one,one_mul,PowerSeries.rescale_one]
  change _ * algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
    (PowerSeries.expand m hm.ne' (lpsOriginalTaylorSeries lpsOriginalJQCoefficient))=_
  have hK : lpsOriginalCuspJNumerator ℂ=lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by
    exact lpsOriginalJZSeries_mapC
  rw [←hK]
  rfl

end
end QEC.Coding.TannerLiftedProduct

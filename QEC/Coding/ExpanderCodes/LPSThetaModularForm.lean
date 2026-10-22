import QEC.Coding.ExpanderCodes.LPSGaussEvaluation
import QEC.Coding.ExpanderCodes.LPSThetaGaussFourthReduction
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# The actual LPS theta product as a weight-two modular form

The matrix determinant gives a genuine unit modulo its lower-left entry. The
proved finite Gauss fourth power normalizes the exact theta scalar to one for
every matrix in Gamma0(16*q^2), including negative and zero entries. Combining
this genuine slash invariance with actual holomorphicity and boundedness at
every rational cusp constructs Mathlib's ModularForm with the existing function.
Its q-expansion retains exactly the four-variable trace coefficients.

This does not assert cuspidality, an all-cusp Eisenstein correction, strong
arithmetic coefficient growth or the PK22 main theorem. No transformation,
Gauss value, cusp condition or target coefficient is supplied as an assumption.
The registered arbitrary-finite-field main theorem remains unproved.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

/-- The determinant unit and proved Gauss fourth power normalize the positive-entry scalar. -/
lemma lpsThetaPositiveGaussScalar_eq_one (q : ℕ) (hq : 0 < q)
    (γ : SL(2,ℤ)) (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) :
    lpsThetaPositiveGaussScalar q γ = 1 := by
  let c := (γ 1 0).toNat
  have hcp : 0 < c := by omega
  let : NeZero c := ⟨ne_of_gt hcp⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hdet : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hunit : IsUnit (γ 0 0:ZMod c) := by
    apply IsUnit.of_mul_eq_one (γ 1 1:ZMod c)
    have h := congrArg (fun x : ℤ => (x:ZMod c)) hdet
    simpa using h
  have h4 : 4 ∣ c := dvd_trans (show 4 ∣ 16*q^2 from ⟨4*q^2,by ring⟩) hlevel
  rw [lpsThetaPositiveGaussScalar_eq_fourth q hq γ hc hlevel,
    lpsUnaryQuadraticGauss_fourth c h4 (γ 0 0) hunit]
  have hcC : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hcp
  change -(4*(c:ℂ)^2)⁻¹ * (-4*(c:ℂ)^2) = 1
  field_simp [hcC]

/-- Every actual level matrix has scalar one, including zero and negative lower-left entries. -/
lemma lpsThetaGammaGaussScalar_eq_one (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) :
    lpsThetaGammaGaussScalar q γ = 1 := by
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hpos : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hn
    have hγn : (-γ) ∈ CongruenceSubgroup.Gamma0 (16*q^2) := by
      rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
      simpa using congrArg Neg.neg hγ
    simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_lt hn),
      if_neg (not_lt_of_ge hn.le)] using lpsThetaPositiveGaussScalar_eq_one q hq (-γ) hpos
        (lpsGamma0_pos_lower_dvd _ _ hγn hpos)
  · simp [lpsThetaGammaGaussScalar,hz]
  · simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_gt hp),if_pos hp] using
      lpsThetaPositiveGaussScalar_eq_one q hq γ hp (lpsGamma0_pos_lower_dvd _ _ hγ hp)

/-- The actual LPS theta function is invariant under the weight-two level subgroup action. -/
lemma lpsStandardTheta_slash_gamma0 (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) :
    (fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ =
      (fun w : UpperHalfPlane => lpsStandardTheta q w) := by
  funext z
  rw [lpsStandardTheta_slash_gamma0_scalar q hq γ hγ z,
    lpsThetaGammaGaussScalar_eq_one q hq γ hγ,one_mul]

/-- Differentiability of the actual complex theta product gives manifold holomorphicity. -/
lemma lpsStandardTheta_mdifferentiable (q : ℕ) (hq : 0<q) :
    MDiff (fun z : ℍ => lpsStandardTheta q z) := by
  intro z
  exact (differentiableAt_lpsStandardTheta q hq z.2).mdifferentiableAt.comp
    z z.mdifferentiable_coe

/-- Every actual cusp has a rational matrix representative and genuine slash boundedness. -/
lemma lpsStandardTheta_bounded_at_cusps (q : ℕ) (hq : 0<q)
    {c : OnePoint ℝ} (hc : IsCusp c
      (CongruenceSubgroup.Gamma0 (16*q^2) : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt (fun z : ℍ => lpsStandardTheta q z) (2:ℤ) := by
  have hcSL : IsCusp c 𝒮ℒ := hc.mono
    (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _)
  obtain ⟨γ,rfl⟩ := isCusp_SL2Z_iff'.mp hcSL
  rw [OnePoint.IsBoundedAt.smul_iff,OnePoint.isBoundedAt_infty_iff]
  simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using
    lpsStandardTheta_isBoundedAtImInfty_slash q hq γ

/-- The actual theta product is a weight-two modular form, with proved transformation and cusp conditions. -/
noncomputable def lpsStandardThetaModularForm (q : ℕ) (hq : 0<q) :
    ModularForm (CongruenceSubgroup.Gamma0 (16*q^2) : Subgroup (GL (Fin 2) ℝ)) (2:ℤ) where
  toFun := fun z => lpsStandardTheta q z
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using
      lpsStandardTheta_slash_gamma0 q hq γ hγ
  holo' := lpsStandardTheta_mdifferentiable q hq
  bdd_at_cusps' := lpsStandardTheta_bounded_at_cusps q hq

/-- The constructed modular form retains exactly the existing theta function. -/
@[simp] lemma lpsStandardThetaModularForm_apply (q : ℕ) (hq : 0<q) (z : ℍ) :
    lpsStandardThetaModularForm q hq z = lpsStandardTheta q z := rfl

/-- The genuine modular form has exactly the already-proved trace theta coefficients. -/
lemma coeff_qExpansion_lpsStandardThetaModularForm (q : ℕ) (hq : 0<q) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsStandardThetaModularForm q hq)) =
      ((PowerSeries.coeff n (lpsTraceThetaSeries q) : ℕ) : ℂ) :=
  coeff_qExpansion_lpsStandardTheta q hq n

end QEC.Coding.TannerLiftedProduct

import QEC.Coding.ExpanderCodes.LPSGaussSquare
import QEC.Coding.ExpanderCodes.LPSThetaGaussScalar

/-!
# Actual LPS theta scalar reduced to one Gauss fourth power

The matrix determinant gives an actual inverse modulo its positive lower-left
entry. Level divisibility permits the proved square scaling at factor `2*q`,
so the existing four-factor Gauss scalar becomes `-G(a,c)^4/(4*c^2)`.
The actual weight-two slash inherits this exact reduction.

The general fourth-power value and scalar normalization to one are not assumed
or proved here. Full Gamma0 invariance, ModularForm packaging, the correct
all-cusp Eisenstein correction, strong growth and the PK22 main theorem remain
unproved. The scope of the registered arbitrary finite-field theorem is unchanged.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Real

open scoped UpperHalfPlane ModularForm MatrixGroups

/-- Square scaling reduces the actual four-factor scalar to a single fourth power. -/
lemma lpsThetaPositiveGaussScalar_eq_fourth (q : ℕ) (hq : 0 < q)
    (γ : SL(2,ℤ)) (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) :
    lpsThetaPositiveGaussScalar q γ =
      -(4*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat^4 := by
  let c := (γ 1 0).toNat
  have hcp : 0 < c := by omega
  let : NeZero c := ⟨ne_of_gt hcp⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hdet : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  obtain ⟨k,hk⟩ := hlevel
  have hkp : 0 < k := by
    by_contra h
    have hkz : k=0 := by omega
    simp [hkz] at hk
    omega
  have hs := lpsUnaryQuadraticGauss_square_scale c (2*q) k
    (by dsimp [c];rw [hk];ring) (by positivity) hkp (γ 0 0) (γ 0 1) (γ 1 1) hdet
  have ha : γ 0 0*((2*q:ℕ):ℤ)^2=4*(q:ℤ)^2*γ 0 0 := by push_cast;ring
  rw [ha] at hs
  unfold lpsThetaPositiveGaussScalar
  change -(32*(q:ℂ)^3*(c:ℂ)^2)⁻¹ *
    lpsUnaryQuadraticGauss (γ 0 0) c * lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) c^3 =
      -(4*(c:ℂ)^2)⁻¹ * lpsUnaryQuadraticGauss (γ 0 0) c^4
  rw [hs]
  push_cast
  have hqC : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have hcC : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hcp
  field_simp [hqC,hcC]
  ring

/-- The actual weight-two slash has the proved fourth-power scalar. -/
lemma lpsStandardTheta_slash_level_fourth (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      (-(4*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat^4) * lpsStandardTheta q z := by
  have h := lpsStandardTheta_slash_level_scalar q hq γ hc hlevel z
  change _ = lpsThetaPositiveGaussScalar q γ*lpsStandardTheta q z at h
  rw [lpsThetaPositiveGaussScalar_eq_fourth q hq γ hc hlevel] at h
  exact h

end QEC.Coding.TannerLiftedProduct

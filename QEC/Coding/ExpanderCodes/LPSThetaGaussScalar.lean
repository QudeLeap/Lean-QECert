import QEC.Coding.ExpanderCodes.LPSThetaCusps
import QEC.Coding.ExpanderCodes.LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Exact Gauss scalar law on the LPS congruence subgroup

The supported Fourier-series identity reduces each of the four genuine theta
characteristic factors to its Gauss sum times the original Jacobi theta. Actual
Mathlib Gamma0 membership gives the necessary modulus divisibility. Combining
these identities with the existing rational-cusp slash formula proves the
scalar law for every actual matrix in `Gamma0 (16*q^2)`: positive entries use
both scaling identities, negative entries use even-weight negation, and zero
entries use the proved translation identity.

The scalar is an explicit finite Gauss expression. This module does not prove
that it equals one, assert scalar invariance or construct a ModularForm/CuspForm.
Gauss normalization, a genuine Eisenstein correction, strong arithmetic Fourier
growth and the PK22 main theorem remain separate proof obligations. No target
transformation or coefficient is supplied as an assumption.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups

/-- The two actual scale reductions yield the original LPS product times its Gauss scalar. -/
lemma lpsStandardTheta_slash_level_scalar (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      (-(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
        lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
        lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat^3) *
      lpsStandardTheta q z := by
  let c := (γ 1 0).toNat
  have hcp : 0 < c := by omega
  let : NeZero c := ⟨ne_of_gt hcp⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hcc : (c:ℂ)=(γ 1 0:ℂ) := by exact_mod_cast hci
  have hdet : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h4 : 4 ∣ c := Nat.dvd_trans (show 4 ∣ 16*q^2 from ⟨4*q^2,by ring_nf⟩) hlevel
  obtain ⟨k1,hk1⟩ := h4
  obtain ⟨k8,hk8⟩ := hlevel
  have hk1p : 0 < k1 := by
    by_contra he
    have hz : k1=0 := by omega
    simp [hz] at hk1
    omega
  have hk8p : 0 < k8 := by
    by_contra he
    have hz : k8=0 := by omega
    simp [hz] at hk8
    omega
  have h1 := lpsThetaGaussSum_scalar c 1 k1 (by decide) hk1p
    (by simpa using hk1) (γ 0 0) (γ 0 1) (γ 1 1) hdet z z.im_pos
  have h8 := lpsThetaGaussSum_scalar c (4*q^2) k8 (by positivity) hk8p
    (by dsimp [c];rw [hk8];ring_nf) (γ 0 0) (γ 0 1) (γ 1 1) hdet z z.im_pos
  norm_num only [Nat.cast_one,Int.cast_one,mul_one,one_mul] at h1
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] at h8
  rw [show (2:ℂ)*(4*(q:ℂ)^2)=8*(q:ℂ)^2 by ring_nf] at h8
  have ht : lpsStandardTheta q z = jacobiTheta (2*(z:ℂ))*jacobiTheta (8*(q:ℂ)^2*(z:ℂ))^3 := by
    unfold lpsStandardTheta lpsAnalyticThetaProduct
    congr 2
    push_cast
    ring_nf
  rw [lpsStandardTheta_slash_pos_c q hq γ hc z,← hcc]
  change -(32*(q:ℂ)^3*(c:ℂ)^2)⁻¹ *
      lpsThetaGaussSum (γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/2) *
      lpsThetaGaussSum (4*(q:ℤ)^2*γ 0 0) c (((z:ℂ)+(γ 1 1:ℂ)/(c:ℂ))/(8*(q:ℂ)^2))^3 = _
  rw [h1,h8,ht]
  dsimp only [c]
  ring

/-- Genuine finite Gauss expression for a positive lower-left entry. -/
noncomputable def lpsThetaPositiveGaussScalar (q : ℕ) (γ : SL(2,ℤ)) : ℂ :=
  -(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
    lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
    lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat^3

/-- Orient the matrix to positive lower-left entry; the translation scalar is one. -/
noncomputable def lpsThetaGammaGaussScalar (q : ℕ) (γ : SL(2,ℤ)) : ℂ :=
  if γ 1 0=0 then 1 else
    if 0 < γ 1 0 then lpsThetaPositiveGaussScalar q γ else lpsThetaPositiveGaussScalar q (-γ)

/-- Actual Mathlib congruence membership implies natural lower-left divisibility. -/
lemma lpsGamma0_pos_lower_dvd (N : ℕ) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hc : 0 < γ 1 0) : N ∣ (γ 1 0).toNat := by
  apply Int.natCast_dvd_natCast.mp
  rw [Int.toNat_of_nonneg hc.le]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)

/-- Exact scalar law for every actual Gamma0 matrix; scalar normalization is not assumed. -/
lemma lpsStandardTheta_slash_gamma0_scalar (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) (z : UpperHalfPlane) :
    ((fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ) z =
      lpsThetaGammaGaussScalar q γ * lpsStandardTheta q z := by
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hpos : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hn
    have hγn : (-γ) ∈ CongruenceSubgroup.Gamma0 (16*q^2) := by
      rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
      simpa using congrArg Neg.neg hγ
    have h := lpsStandardTheta_slash_level_scalar q hq (-γ) hpos
      (lpsGamma0_pos_lower_dvd _ _ hγn hpos) z
    rw [lpsStandardTheta_slash_neg_matrix] at h
    simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_lt hn),if_neg (not_lt_of_ge hn.le),
      lpsThetaPositiveGaussScalar] using h
  · have h := congrArg (fun f : UpperHalfPlane → ℂ => f z) (lpsStandardTheta_slash_zero_c q γ hz)
    simpa only [lpsThetaGammaGaussScalar,if_pos hz,one_mul] using h
  · have h := lpsStandardTheta_slash_level_scalar q hq γ hp
      (lpsGamma0_pos_lower_dvd _ _ hγ hp) z
    simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_gt hp),if_pos hp,
      lpsThetaPositiveGaussScalar] using h

end QEC.Coding.TannerLiftedProduct

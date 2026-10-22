import QEC.Coding.ExpanderCodes.LPSGamma0PeterssonDomain
import QEC.Coding.ExpanderCodes.LPSHeckeCoefficients
import QEC.Coding.ExpanderCodes.LPSPeterssonDomainTransfer

/-!
# Actual Hecke Petersson integrals and inverse-domain transfer

True cusp self-bounds prove convergence of every mixed positive-determinant slash term. Integrate the original Hecke operator term by term and transfer to genuine inverse-matrix image domains. Matching the two finite covers, self-adjointness and the arithmetic near-root estimate remain separate proofs.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- Every actual Gamma0 domain computes the original genuine Hecke pairing. -/
lemma lpsCuspHeckePairing_gamma0Domain (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∫τ in s,petersson 2 (lpsHeckeSlashSum p f) g τ :=
  lpsCuspPeterssonPairing_gamma0Domain N (lpsCuspHeckeLinearMap N p hNp f) g hs

/-- Actual cusp self-bounds and weight-two covariance bound every mixed positive-determinant slash term. -/
lemma lpsWeightTwoSlashPetersson_bounded (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    ∃C:ℝ,∀τ, ‖petersson 2 (f ∣[(2:ℤ)] A) g τ‖ ≤ C := by
  obtain ⟨Cf,hf⟩ := CuspFormClass.petersson_bounded_left 2 _ f f
  obtain ⟨Cg,hg⟩ := CuspFormClass.petersson_bounded_left 2 _ g g
  refine ⟨(Cf+Cg)/2,fun τ => ?_⟩
  have he : petersson 2 (f ∣[(2:ℤ)] A) (f ∣[(2:ℤ)] A) τ = petersson 2 f f (A • τ) := by
    have hA' : 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det := hA
    simpa [UpperHalfPlane.σ,hA'] using petersson_slash 2 f f A τ
  have hf' : ‖petersson 2 (f ∣[(2:ℤ)] A) (f ∣[(2:ℤ)] A) τ‖ ≤ Cf := by
    rw [he]
    exact hf _
  have hg' := hg τ
  have hnon := mul_nonneg (sq_nonneg (‖((f:ℍ→ℂ) ∣[(2:ℤ)] A) τ‖-‖g τ‖)) (sq_nonneg τ.im)
  simp only [petersson,norm_mul,Complex.norm_conj,norm_zpow,Complex.norm_real,
    Real.norm_of_nonneg τ.im_pos.le] at hf' hg' ⊢
  norm_num only [Int.reduceNeg,Int.ofNat_eq_natCast, zpow_ofNat] at hf' hg' ⊢
  nlinarith

/-- Every actual mixed slash term is absolutely integrable on the proved finite Gamma0 domain. -/
lemma lpsWeightTwoSlashPetersson_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    IntegrableOn (petersson 2 (f ∣[(2:ℤ)] A) g) (lpsGamma0PeterssonDomain N) volume := by
  obtain ⟨C,hC⟩ := lpsWeightTwoSlashPetersson_bounded N f g A hA
  have hi : IntegrableOn (fun _ : ℍ => C) (lpsGamma0PeterssonDomain N) :=
    integrableOn_const (ne_of_lt (lpsGamma0PeterssonDomain_volume_finite N))
  have hc : Continuous (f ∣[(2:ℤ)] A) := (f.holo'.slash 2 A).continuous
  exact hi.mono' (petersson_continuous 2 hc (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall hC)

/-- The actual weight-two integrand preserves finite sums in its conjugate-linear first factor. -/
lemma lpsWeightTwoPetersson_sum_left {ι : Type*} [Fintype ι] (F : ι → ℍ → ℂ)
    (g : ℍ → ℂ) (τ : ℍ) :
    petersson 2 (∑i,F i) g τ = ∑i,petersson 2 (F i) g τ := by
  classical
  simp [petersson,Finset.sum_apply,map_sum,Finset.sum_mul]

/-- The actual weight-two integrand preserves finite sums in its second factor. -/
lemma lpsWeightTwoPetersson_sum_right {ι : Type*} [Fintype ι] (f : ℍ → ℂ)
    (G : ι → ℍ → ℂ) (τ : ℍ) :
    petersson 2 f (∑i,G i) τ = ∑i,petersson 2 f (G i) τ := by
  classical
  simp [petersson,Finset.sum_apply,Finset.sum_mul,Finset.mul_sum]

/-- The positive-determinant inverse-matrix image integral is separately absolutely convergent. -/
lemma lpsWeightTwoInversePetersson_image_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] A⁻¹)) (A • lpsGamma0PeterssonDomain N) volume := by
  apply ((measurePreserving_smul A volume).integrableOn_image
    (measurableEmbedding_const_smul A)).mpr
  simpa only [Function.comp_def,←lpsWeightTwoPetersson_transfer _ _ A hA] using
    lpsWeightTwoSlashPetersson_integrable N f g A hA

/-- The original Hecke pairing is the true finite sum of absolutely convergent slash integrals. -/
lemma lpsCuspHeckePairing_sum_left (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        petersson 2 (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) g τ := by
  rw [lpsCuspHeckePairing_gamma0Domain N p hNp f g (lpsGamma0PeterssonDomain_fundamental N)]
  simp_rw [lpsHeckeSlashSum,lpsWeightTwoPetersson_sum_left]
  apply integral_finsetSum
  intro i _
  apply lpsWeightTwoSlashPetersson_integrable N f g
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos

/-- Change of variables transfers the original Hecke pairing to actual inverse-matrix image integrals. -/
lemma lpsCuspHeckePairing_inverseIntegrals (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∑i:Option (Fin p), ∫τ in (lpsHeckeUpperGL ℝ p i) • lpsGamma0PeterssonDomain N,
        petersson 2 f (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p i)⁻¹) τ := by
  rw [lpsCuspHeckePairing_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  apply lpsWeightTwoPetersson_integral_transfer
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos

/-- Every transferred genuine determinant-p Hecke integral is absolutely convergent. -/
lemma lpsCuspHeckePairing_inverseIntegrals_integrable (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p i)⁻¹))
      ((lpsHeckeUpperGL ℝ p i) • lpsGamma0PeterssonDomain N) volume := by
  apply lpsWeightTwoInversePetersson_image_integrable N f g
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos

/-- Every actual right-factor slash integrand is absolutely integrable on the proved Gamma0 domain. -/
lemma lpsWeightTwoSlashPetersson_right_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] A)) (lpsGamma0PeterssonDomain N) volume := by
  obtain ⟨C,hC⟩ := lpsWeightTwoSlashPetersson_bounded N g f A hA
  have hi : IntegrableOn (fun _ : ℍ => C) (lpsGamma0PeterssonDomain N) :=
    integrableOn_const (ne_of_lt (lpsGamma0PeterssonDomain_volume_finite N))
  have hc : Continuous (g ∣[(2:ℤ)] A) := (g.holo'.slash 2 A).continuous
  apply hi.mono' (petersson_continuous 2 (by fun_prop) hc).aestronglyMeasurable
  exact Eventually.of_forall fun τ => by rw [petersson_norm_symm];exact hC τ

/-- The original right Hecke pairing is the true finite sum of convergent right-factor slash integrals. -/
lemma lpsCuspHeckePairing_sum_right (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) =
      ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        petersson 2 f (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ := by
  rw [lpsCuspPeterssonPairing_gamma0Domain N f (lpsCuspHeckeLinearMap N p hNp g)
    (lpsGamma0PeterssonDomain_fundamental N)]
  change (∫τ in lpsGamma0PeterssonDomain N,petersson 2 f (∑i,g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ) = _
  simp_rw [lpsWeightTwoPetersson_sum_right]
  apply integral_finsetSum
  intro i _
  apply lpsWeightTwoSlashPetersson_right_integrable N f g
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos

end
end QEC.Coding.TannerLiftedProduct

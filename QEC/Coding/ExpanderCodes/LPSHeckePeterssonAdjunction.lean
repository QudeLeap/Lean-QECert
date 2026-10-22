import QEC.Coding.ExpanderCodes.LPSHeckeCommonDomain
import QEC.Coding.ExpanderCodes.LPSHeckeAdjointDensities

/-!
# Original cusp-Hecke Petersson adjunction

Component absolute convergence and genuine finite-cover integration prove adjunction for the original unnormalized cusp Hecke operator. This supplies symmetry, not a Ramanujan bound or the PK22 theorem.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- The original left Hecke pairing equals the convergent integral on the actual A-image cover. -/
lemma lpsHeckeLeft_cover_integral (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∫τ in lpsHeckeUpperGL ℝ p none •
        (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N),
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  let F : ℍ→ℂ := petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
  let FA : ℍ→ℂ := fun τ => F (lpsHeckeUpperGL ℝ p none • τ)
  have hi (i : Option (Fin p)) : IntegrableOn FA
      ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N) volume := by
    apply ((measurePreserving_smul (lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ volume).integrableOn_image
      (measurableEmbedding_const_smul (lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹)).mpr
    have h := lpsWeightTwoSlashPetersson_integrable N f g (lpsHeckeUpperGL ℝ p i)
      (by rw [lpsHeckeUpperGL_det];exact_mod_cast (Fact.out:p.Prime).pos)
    apply h.congr
    exact Eventually.of_forall (lpsHeckeLeft_density N p hNp f g i)
  rw [lpsCuspHeckePairing_sum_left]
  have he := lpsIndexedRelativeDomain_integral _ (lpsGamma0PeterssonDomain N)
    (lpsGamma0PeterssonDomain_fundamental N)
    (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm
    (lpsHeckeIntersectionEffectiveRepresentative N p hNp)
    (lpsHeckeIntersectionEffectiveRepresentative_mk N p hNp) FA hi
  calc
    _ = ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        FA ((lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • τ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Eventually.of_forall (lpsHeckeLeft_density N p hNp f g i)
    _ = ∫τ in ⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ •
        lpsGamma0PeterssonDomain N,FA τ := he.symm
    _ = _ := ((measurePreserving_smul (lpsHeckeUpperGL ℝ p none) volume).setIntegral_image_emb
      (measurableEmbedding_const_smul (lpsHeckeUpperGL ℝ p none)) F _).symm

/-- The original right Hecke pairing equals the convergent integral on the actual inverse cover. -/
lemma lpsHeckeRight_cover_integral (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) =
      ∫τ in ⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N,
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  let F : ℍ→ℂ := petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
  have hi (i : Option (Fin p)) : IntegrableOn F
      ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • lpsGamma0PeterssonDomain N) volume := by
    apply ((measurePreserving_smul (lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ volume).integrableOn_image
      (measurableEmbedding_const_smul (lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹)).mpr
    have h := lpsWeightTwoSlashPetersson_right_integrable N f g (lpsHeckeUpperGL ℝ p i)
      (by rw [lpsHeckeUpperGL_det];exact_mod_cast (Fact.out:p.Prime).pos)
    apply h.congr
    exact Eventually.of_forall (lpsHeckeRight_density N p hNp f g i)
  rw [lpsCuspHeckePairing_sum_right]
  have he := lpsIndexedRelativeDomain_integral _ (lpsGamma0PeterssonDomain N)
    (lpsGamma0PeterssonDomain_fundamental N)
    (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm
    (lpsHeckeConjugateEffectiveRepresentative N p hNp)
    (lpsHeckeConjugateEffectiveRepresentative_mk N p hNp) F hi
  calc
    _ = ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        F ((lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • τ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Eventually.of_forall (lpsHeckeRight_density N p hNp f g i)
    _ = _ := he.symm

/-- The original unnormalized prime-away-level cusp Hecke operator is Petersson self-adjoint. -/
lemma lpsCuspHecke_pairing_selfAdjoint (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) := by
  rw [lpsHeckeLeft_cover_integral,lpsHeckeRight_cover_integral]
  exact lpsHeckeTwoCover_integrals N p hNp f g (lpsGamma0PeterssonDomain_fundamental N)

end
end QEC.Coding.TannerLiftedProduct

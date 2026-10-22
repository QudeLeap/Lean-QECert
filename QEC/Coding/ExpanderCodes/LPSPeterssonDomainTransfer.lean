import QEC.Coding.ExpanderCodes.LPSModularFundamentalDomain
import QEC.Coding.ExpanderCodes.LPSCuspPeterssonTrace

/-!
# LPSPeterssonDomainTransfer

Domain independence and convergence of the original Petersson trace integral, and genuine positive-determinant weight-two slash change of variables. No self-adjointness or arithmetic coefficient estimate is assumed or asserted.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- The original actual finite-coset Petersson trace is invariant under the effective modular action. -/
lemma lpsPeterssonTrace_effectiveInvariant (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) (τ : ℍ) :
    lpsCuspPeterssonTrace N f g (h • τ) = lpsCuspPeterssonTrace N f g τ := by
  obtain ⟨h',hh'⟩ := lpsEffectiveRepresentative h
  change lpsCuspPeterssonTrace N f g ((h : Equiv.Perm ℍ) τ) = _
  rw [hh']
  exact lpsCuspPeterssonTrace_invariant N f g h' τ

/-- The original pairing equals its actual trace integral on every genuine effective modular domain. -/
lemma lpsPeterssonPairing_domain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain lpsEffectiveModularGroup s volume) :
    lpsCuspPeterssonPairing N f g = ∫τ in s,lpsCuspPeterssonTrace N f g τ :=
  lpsEffectiveFundamentalDomain.setIntegral_eq hs (lpsPeterssonTrace_effectiveInvariant N f g)

/-- The original trace remains absolutely integrable on every genuine effective modular domain. -/
lemma lpsPeterssonTrace_domain_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain lpsEffectiveModularGroup s volume) :
    IntegrableOn (lpsCuspPeterssonTrace N f g) s volume :=
  (lpsEffectiveFundamentalDomain.integrableOn_iff hs
    (lpsPeterssonTrace_effectiveInvariant N f g)).mp (lpsCuspPeterssonTrace_integrable N f g)

/-- Positive-determinant weight-two slash covariance transfers one factor to the inverse matrix. -/
lemma lpsWeightTwoPetersson_transfer (f g : ℍ → ℂ) (A : GL (Fin 2) ℝ)
    (hA : 0 < A.det.val) (τ : ℍ) :
    petersson 2 (f ∣[(2 : ℤ)] A) g τ = petersson 2 f (g ∣[(2 : ℤ)] A⁻¹) (A • τ) := by
  have he := UpperHalfPlane.petersson_slash 2 f (g ∣[(2 : ℤ)] A⁻¹) A τ
  have hA' : 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det := hA
  simpa [←SlashAction.slash_mul, UpperHalfPlane.σ,hA'] using he

/-- The actual hyperbolic change of variables integrates the one-factor slash transfer. -/
lemma lpsWeightTwoPetersson_integral_transfer (f g : ℍ → ℂ) (A : GL (Fin 2) ℝ)
    (hA : 0 < A.det.val) (s : Set ℍ) :
    (∫τ in s,petersson 2 (f ∣[(2 : ℤ)] A) g τ) =
      ∫τ in A • s,petersson 2 f (g ∣[(2 : ℤ)] A⁻¹) τ := by
  simp_rw [lpsWeightTwoPetersson_transfer f g A hA]
  exact ((measurePreserving_smul A volume).setIntegral_image_emb
    (measurableEmbedding_const_smul A) (petersson 2 f (g ∣[(2 : ℤ)] A⁻¹)) s).symm

/-- Every actual translate of the proved modular domain computes the original pairing. -/
lemma lpsPeterssonPairing_translatedDomain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) :
    lpsCuspPeterssonPairing N f g = ∫τ in h • ModularGroup.fd,lpsCuspPeterssonTrace N f g τ :=
  lpsPeterssonPairing_domain N f g (lpsEffectiveFundamentalDomain.smul h)

end
end QEC.Coding.TannerLiftedProduct

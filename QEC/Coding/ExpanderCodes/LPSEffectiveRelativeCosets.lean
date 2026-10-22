import QEC.Coding.ExpanderCodes.LPSHeckeCosetCover
import QEC.Coding.ExpanderCodes.LPSGamma0PeterssonDomain

/-!
# Actual effective relative cosets

The contained ineffective kernel preserves nonnormal relative coset spaces. This is genuine quotient transport, not an assumed cover.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- Removing the contained ineffective kernel preserves genuine nonnormal relative cosets. -/
noncomputable def lpsEffectiveRelativeCosetEquiv (N : ℕ) (H : Subgroup SL(2,ℤ))
    (hker : (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ H) :
    CongruenceSubgroup.Gamma0 N ⧸ H.subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
      lpsEffectiveGamma0 N ⧸
        (H.map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict).subgroupOf
          (lpsEffectiveGamma0 N) := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  let ψ : CongruenceSubgroup.Gamma0 N →* lpsEffectiveGamma0 N :=
    φ.subgroupMap (CongruenceSubgroup.Gamma0 N)
  let f : CongruenceSubgroup.Gamma0 N ⧸ H.subgroupOf (CongruenceSubgroup.Gamma0 N) →
      lpsEffectiveGamma0 N ⧸ (H.map φ).subgroupOf (lpsEffectiveGamma0 N) :=
    Quotient.map' ψ (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      have hm := Subgroup.mem_map_of_mem φ hxy
      change φ ((x:SL(2,ℤ))⁻¹*y) ∈ H.map φ at hm
      change (φ (x:SL(2,ℤ)))⁻¹*φ (y:SL(2,ℤ)) ∈ H.map φ
      simpa only [map_mul,map_inv] using hm)
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        have hxy' : (QuotientGroup.mk (ψ x) :
            lpsEffectiveGamma0 N ⧸ (H.map φ).subgroupOf (lpsEffectiveGamma0 N)) =
              QuotientGroup.mk (ψ y) := hxy
        have hm := QuotientGroup.eq.mp hxy'
        change (φ (x:SL(2,ℤ)))⁻¹*φ (y:SL(2,ℤ)) ∈ H.map φ at hm
        have hh : (x:SL(2,ℤ))⁻¹*y ∈ (H.map φ).comap φ := by
          simpa only [Subgroup.mem_comap,map_mul,map_inv] using hm
        have hc : (H.map φ).comap φ=H := Subgroup.comap_map_eq_self hker
        rw [hc] at hh
        exact hh
  · intro y
    induction y using QuotientGroup.induction_on with | H y =>
      obtain ⟨x,rfl⟩ := φ.subgroupMap_surjective (CongruenceSubgroup.Gamma0 N) y
      exact ⟨QuotientGroup.mk x,rfl⟩

/-- The genuine relative quotient transport evaluates by the original effective projection. -/
lemma lpsEffectiveRelativeCosetEquiv_mk (N : ℕ) (H : Subgroup SL(2,ℤ))
    (hker : (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ H)
    (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveRelativeCosetEquiv N H hker (QuotientGroup.mk γ) =
      QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ) := rfl

/-- The actual ineffective kernel lies in the original upper-right Hecke intersection. -/
lemma lpsEffectiveKernel_le_HeckeConjugate (N p : ℕ) :
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤
      lpsHeckeConjugateIntersection N p := by
  intro γ hγ
  have hh : (MulAction.toPermHom SL(2,ℤ) ℍ) γ=1 :=
    congrArg (fun e : lpsEffectiveModularGroup => (e:Equiv.Perm ℍ)) hγ
  rcases (lpsEffectiveKernel γ).mp hh with rfl | rfl
  · exact ⟨by simp,by simp [lpsUpperCongruence]⟩
  · exact ⟨by simp,by simp [lpsUpperCongruence]⟩

end
end QEC.Coding.TannerLiftedProduct

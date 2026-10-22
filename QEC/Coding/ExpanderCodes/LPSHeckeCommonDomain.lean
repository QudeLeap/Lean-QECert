import QEC.Coding.ExpanderCodes.LPSHeckeEffectiveCovers
import QEC.Coding.ExpanderCodes.LPSHeckePeterssonIntegrals

/-!
# Actual common Hecke integration domain

True matrix conjugacy transports the first cover to the same effective upper-right intersection as the second. Actual density invariance proves domain-integral equality.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- A true effective-subgroup domain transports to its injective permutation image. -/
lemma lpsEffectiveFundamental_perm (H : Subgroup lpsEffectiveModularGroup)
    {s : Set ℍ} (hs : IsFundamentalDomain H s volume) :
    IsFundamentalDomain (H.map lpsEffectiveModularGroup.subtype) s volume :=
  hs.preimage_of_equiv (Measure.QuasiMeasurePreserving.id volume)
    (H.equivMapOfInjective lpsEffectiveModularGroup.subtype
      lpsEffectiveModularGroup.subtype_injective).bijective (fun _ _ => rfl)

/-- A real GL matrix sends a true subgroup domain to its genuine permutation-conjugate domain. -/
lemma lpsPermConjugateFundamental (H : Subgroup (Equiv.Perm ℍ))
    (A : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsFundamentalDomain H s volume) :
    IsFundamentalDomain (H.map (MulAut.conj (MulAction.toPerm A)).toMonoidHom)
      (A • s) volume := by
  have heq : (MulAction.toPerm A : ℍ ≃ ℍ) '' s=A • s := rfl
  rw [←heq]
  refine hs.image_of_equiv (MulAction.toPerm A)
    ((measurePreserving_smul A⁻¹ volume).quasiMeasurePreserving)
    (((MulAut.conj (MulAction.toPerm A)).subgroupMap H).symm.toEquiv) ?_
  intro g τ
  change (MulAction.toPerm A) (((MulAut.conj (MulAction.toPerm A)).subgroupMap H).symm g • τ) =
    (g:Equiv.Perm ℍ) ((MulAction.toPerm A) τ)
  change (MulAction.toPerm A) (((MulAut.conj (MulAction.toPerm A)).symm (g:Equiv.Perm ℍ)) τ) = _
  simp

/-- The original integral modular action agrees with its true real GL realization. -/
lemma lpsGLPermSL (γ : SL(2,ℤ)) :
    (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ γ) : Equiv.Perm ℍ)=
      (MulAction.toPerm γ : Equiv.Perm ℍ) := by
  apply Equiv.ext
  intro τ
  change Matrix.SpecialLinearGroup.mapGL ℝ γ • τ = γ • τ
  exact (ModularGroup.sl_moeb γ τ).symm

/-- An actual real GL factor identity induces the genuine permutation conjugacy. -/
lemma lpsPerm_of_real_factor (A : GL (Fin 2) ℝ) (γ δ : SL(2,ℤ))
    (he : A*Matrix.SpecialLinearGroup.mapGL ℝ γ=
      Matrix.SpecialLinearGroup.mapGL ℝ δ*A) :
    (MulAut.conj (MulAction.toPerm A : Equiv.Perm ℍ))
      (MulAction.toPerm γ : Equiv.Perm ℍ)=(MulAction.toPerm δ : Equiv.Perm ℍ) := by
  have h' : A*Matrix.SpecialLinearGroup.mapGL ℝ γ*A⁻¹=Matrix.SpecialLinearGroup.mapGL ℝ δ := by
    rw [he,mul_assoc,mul_inv_cancel,mul_one]
  have hp := congrArg (MulAction.toPermHom (GL (Fin 2) ℝ) ℍ) h'
  simp only [map_mul,map_inv] at hp
  change (MulAction.toPerm A : Equiv.Perm ℍ) *
    (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ γ) : Equiv.Perm ℍ) *
      (MulAction.toPerm A : Equiv.Perm ℍ)⁻¹ =
        (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ δ) : Equiv.Perm ℍ) at hp
  simpa only [MulAut.conj_apply,lpsGLPermSL] using hp

/-- Effective projection followed by subtype gives the original permutation image. -/
lemma lpsEffectiveSubgroup_perm (H : Subgroup SL(2,ℤ)) :
    (H.map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict).map
      lpsEffectiveModularGroup.subtype=H.map (MulAction.toPermHom SL(2,ℤ) ℍ) := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  change (H.map φ).map lpsEffectiveModularGroup.subtype=_
  rw [Subgroup.map_map]
  rfl

/-- The true upper-right intersection is the actual dilation-conjugate Gamma0(Np) action. -/
lemma lpsHeckeConjugatePerm_eq (N p : ℕ) [Fact p.Prime] :
    (lpsEffectiveHeckeConjugateIntersection N p).map lpsEffectiveModularGroup.subtype =
      ((lpsEffectiveGamma0 (N*p)).map lpsEffectiveModularGroup.subtype).map
        (MulAut.conj (MulAction.toPerm (lpsHeckeUpperGL ℝ p none))).toMonoidHom := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  change ((lpsHeckeConjugateIntersection N p).map φ).map lpsEffectiveModularGroup.subtype =
    (((CongruenceSubgroup.Gamma0 (N*p)).map φ).map lpsEffectiveModularGroup.subtype).map _
  have hφ (H : Subgroup SL(2,ℤ)) : (H.map φ).map lpsEffectiveModularGroup.subtype =
      H.map (MulAction.toPermHom SL(2,ℤ) ℍ) := lpsEffectiveSubgroup_perm H
  rw [hφ,hφ,Subgroup.map_map]
  ext π
  constructor
  · intro hπ
    obtain ⟨δ,hδ,hδπ⟩ := Subgroup.mem_map.mp hπ
    obtain ⟨γ,hγ,he⟩ := lpsHeckeConjugateIntersection_conjugate N p δ hδ
    exact Subgroup.mem_map.mpr ⟨γ,hγ,(lpsPerm_of_real_factor _ γ δ he).trans hδπ⟩
  · intro hπ
    obtain ⟨γ,hγ,hγπ⟩ := Subgroup.mem_map.mp hπ
    obtain ⟨δ,hδ,he⟩ := lpsHeckeIntersection_conjugate_upper N p γ hγ
    exact Subgroup.mem_map.mpr ⟨δ,hδ,(lpsPerm_of_real_factor _ γ δ he).symm.trans hγπ⟩


/-- Pull a true permutation-image domain back along the injective effective action. -/
lemma lpsEffectiveFundamental_of_perm (H : Subgroup lpsEffectiveModularGroup)
    {s : Set ℍ} (hs : IsFundamentalDomain (H.map lpsEffectiveModularGroup.subtype) s volume) :
    IsFundamentalDomain H s volume := by
  let e := H.equivMapOfInjective lpsEffectiveModularGroup.subtype
    lpsEffectiveModularGroup.subtype_injective
  refine hs.preimage_of_equiv (Measure.QuasiMeasurePreserving.id volume) e.symm.bijective ?_
  intro g τ
  have he := congrArg (fun π : H.map lpsEffectiveModularGroup.subtype => (π:Equiv.Perm ℍ) τ)
    (e.apply_symm_apply g)
  exact he

/-- The A-image first cover is a genuine domain for the same effective upper-right intersection. -/
lemma lpsHeckeLeftImageCover_fundamental (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveHeckeConjugateIntersection N p)
      (lpsHeckeUpperGL ℝ p none •
        (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s)) volume := by
  have hA := lpsHeckeIntersectionCover_originalEffective N p hNp hs
  have hP := lpsEffectiveFundamental_perm _ hA
  have hC := lpsPermConjugateFundamental _ (lpsHeckeUpperGL ℝ p none) hP
  rw [←lpsHeckeConjugatePerm_eq N p] at hC
  exact lpsEffectiveFundamental_of_perm _ hC

/-- The second cover is a genuine domain for the same effective upper-right intersection. -/
lemma lpsHeckeRightCover_fundamental (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveHeckeConjugateIntersection N p)
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume :=
  lpsHeckeConjugateCover_originalEffective N p hNp hs

/-- Actual cusp slash invariance proves mixed inverse-Petersson invariance under the original intersection. -/
lemma lpsHeckeInversePetersson_gamma_invariant (N p : ℕ) [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (δ : SL(2,ℤ)) (hδ : δ ∈ lpsHeckeConjugateIntersection N p) (τ : ℍ) :
    petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) (δ • τ) =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  obtain ⟨γ,hγ,he⟩ := lpsHeckeConjugateIntersection_conjugate N p δ hδ
  have hδN := (lpsHeckeConjugateIntersection_mem N p δ).mp hδ |>.1
  have hγN := lpsGamma0_product_le N p hγ
  have hi : (lpsHeckeUpperGL ℝ p none)⁻¹*Matrix.SpecialLinearGroup.mapGL ℝ δ =
      Matrix.SpecialLinearGroup.mapGL ℝ γ*(lpsHeckeUpperGL ℝ p none)⁻¹ := by
    have hh := congrArg (fun A : GL (Fin 2) ℝ =>
      (lpsHeckeUpperGL ℝ p none)⁻¹*A*(lpsHeckeUpperGL ℝ p none)⁻¹) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one] using hh.symm
  have hg : (((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) ∣[(2:ℤ)] δ)=
      ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) := by
    change (((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) ∣[(2:ℤ)]
      Matrix.SpecialLinearGroup.mapGL ℝ δ)=_
    rw [←SlashAction.slash_mul,hi,SlashAction.slash_mul]
    change (((g:ℍ→ℂ) ∣[(2:ℤ)] γ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)=_
    rw [lpsWeightTwoCusp_slash_gamma0 N g γ hγN]
  have hp := UpperHalfPlane.petersson_slash_SL 2 (f:ℍ→ℂ)
    ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) δ τ
  simpa only [hg,lpsWeightTwoCusp_slash_gamma0 N f δ hδN] using hp.symm

/-- The genuine mixed inverse-Petersson density is invariant under the effective intersection. -/
lemma lpsHeckeInversePetersson_effective_invariant (N p : ℕ) [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveHeckeConjugateIntersection N p) (τ : ℍ) :
    petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) (h • τ) =
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ := by
  obtain ⟨δ,hδ,hδh⟩ := Subgroup.mem_map.mp h.property
  change petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹)
    (((h:lpsEffectiveModularGroup):Equiv.Perm ℍ) τ)=_
  rw [←hδh]
  exact lpsHeckeInversePetersson_gamma_invariant N p f g δ hδ τ

/-- The two actual covers give equal invariant mixed inverse-Petersson integrals. -/
lemma lpsHeckeTwoCover_integrals (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    (∫τ in lpsHeckeUpperGL ℝ p none •
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s),
      petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ) =
      ∫τ in (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s),
        petersson 2 f ((g:ℍ→ℂ) ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p none)⁻¹) τ :=
  (lpsHeckeLeftImageCover_fundamental N p hNp hs).setIntegral_eq
    (lpsHeckeRightCover_fundamental N p hNp hs)
    (lpsHeckeInversePetersson_effective_invariant N p f g)

end
end QEC.Coding.TannerLiftedProduct

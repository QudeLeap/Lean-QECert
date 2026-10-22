import QEC.Coding.ExpanderCodes.LPSRelativeCosetDomain
import QEC.Coding.ExpanderCodes.LPSEffectiveRelativeCosets

/-!
# Genuine effective Hecke covers

Canonical original representatives construct both genuine effective intersection domains with the proved inverse-index and section laws.
-/

namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

/-- Actual effective Gamma0(Np) relative cosets biject with the original Hecke indices. -/
noncomputable def lpsEffectiveHeckeIntersectionCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    lpsEffectiveGamma0 N ⧸ (lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N) ≃
      Option (Fin p) :=
  (lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p))
    (lpsEffectiveKernel_le_Gamma0 (N*p))).symm.trans (lpsHeckeIntersectionCosetEquiv N p hNp)

/-- The first effective coset equivalence agrees with original relative coset evaluation. -/
lemma lpsEffectiveHeckeIntersectionCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveHeckeIntersectionCosetEquiv N p hNp
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ)) =
      lpsHeckeIntersectionCosetEquiv N p hNp (QuotientGroup.mk γ) := by
  change lpsHeckeIntersectionCosetEquiv N p hNp
    ((lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p))
      (lpsEffectiveKernel_le_Gamma0 (N*p))).symm _) = _
  have hm := lpsEffectiveRelativeCosetEquiv_mk N (CongruenceSubgroup.Gamma0 (N*p)) (lpsEffectiveKernel_le_Gamma0 (N*p)) γ
  have hi := congrArg (lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p)) (lpsEffectiveKernel_le_Gamma0 (N*p))).symm hm
  have hi' : (lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p)) (lpsEffectiveKernel_le_Gamma0 (N*p))).symm
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ))=QuotientGroup.mk γ :=
    hi.symm.trans (Equiv.symm_apply_apply _ _)
  exact congrArg (lpsHeckeIntersectionCosetEquiv N p hNp) hi'


/-- Canonical actual original Gamma0 representative of each first-intersection left coset. -/
noncomputable def lpsHeckeIntersectionRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : CongruenceSubgroup.Gamma0 N :=
  Quotient.out ((lpsHeckeIntersectionCosetEquiv N p hNp).symm i)

/-- Project the actual first-intersection representatives to the effective Gamma0 group. -/
noncomputable def lpsHeckeIntersectionEffectiveRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : lpsEffectiveGamma0 N :=
  (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap (CongruenceSubgroup.Gamma0 N)
    (lpsHeckeIntersectionRepresentative N p hNp i)

/-- The inverse of each genuine original first representative has its exact Hecke index. -/
lemma lpsHeckeIntersectionRepresentative_index (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (lpsHeckeIntersectionRepresentative N p hNp i:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem
        (lpsHeckeIntersectionRepresentative N p hNp i).property) none=i := by
  rw [←lpsHeckeIntersectionCosetEquiv_mk]
  unfold lpsHeckeIntersectionRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeIntersectionCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeIntersectionCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeIntersectionCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)


/-- The projected first representatives satisfy the genuine effective section law. -/
lemma lpsHeckeIntersectionEffectiveRepresentative_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    (QuotientGroup.mk (lpsHeckeIntersectionEffectiveRepresentative N p hNp i) :
      lpsEffectiveGamma0 N ⧸ (lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N)) =
        (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm i := by
  apply (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).injective
  rw [Equiv.apply_symm_apply]
  unfold lpsHeckeIntersectionEffectiveRepresentative
  rw [lpsEffectiveHeckeIntersectionCosetEquiv_mk]
  unfold lpsHeckeIntersectionRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeIntersectionCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeIntersectionCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeIntersectionCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)


/-- The original first inverse-section cover is a true effective relative-intersection domain. -/
lemma lpsHeckeIntersectionCover_fundamental (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain ((lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N))
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s) volume :=
  lpsIndexedRelativeDomain_fundamental _ s hs
    (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm _
    (lpsHeckeIntersectionEffectiveRepresentative_mk N p hNp)

/-- The original upper-right intersection projected to the actual effective modular group. -/
def lpsEffectiveHeckeConjugateIntersection (N p : ℕ) : Subgroup lpsEffectiveModularGroup :=
  (lpsHeckeConjugateIntersection N p).map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict

/-- The true effective upper-right relative cosets biject with original Hecke indices. -/
noncomputable def lpsEffectiveHeckeConjugateCosetEquiv (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) :
    lpsEffectiveGamma0 N ⧸
      (lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N) ≃
      Option (Fin p) :=
  (lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p)
    (lpsEffectiveKernel_le_HeckeConjugate N p)).symm.trans (lpsHeckeConjugateCosetEquiv N p hNp)

/-- The second effective coset equivalence agrees with original relative coset evaluation. -/
lemma lpsEffectiveHeckeConjugateCosetEquiv_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveHeckeConjugateCosetEquiv N p hNp
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ)) =
      lpsHeckeConjugateCosetEquiv N p hNp (QuotientGroup.mk γ) := by
  change lpsHeckeConjugateCosetEquiv N p hNp
    ((lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p)
      (lpsEffectiveKernel_le_HeckeConjugate N p)).symm _) = _
  have hm := lpsEffectiveRelativeCosetEquiv_mk N (lpsHeckeConjugateIntersection N p) (lpsEffectiveKernel_le_HeckeConjugate N p) γ
  have hi := congrArg (lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p) (lpsEffectiveKernel_le_HeckeConjugate N p)).symm hm
  have hi' : (lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p) (lpsEffectiveKernel_le_HeckeConjugate N p)).symm
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ))=QuotientGroup.mk γ :=
    hi.symm.trans (Equiv.symm_apply_apply _ _)
  exact congrArg (lpsHeckeConjugateCosetEquiv N p hNp) hi'


/-- Canonical actual original representative of each upper-right intersection left coset. -/
noncomputable def lpsHeckeConjugateRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : CongruenceSubgroup.Gamma0 N :=
  Quotient.out ((lpsHeckeConjugateCosetEquiv N p hNp).symm i)

/-- Project the actual second-intersection representatives to the effective Gamma0 group. -/
noncomputable def lpsHeckeConjugateEffectiveRepresentative (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) : lpsEffectiveGamma0 N :=
  (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap (CongruenceSubgroup.Gamma0 N)
    (lpsHeckeConjugateRepresentative N p hNp i)

/-- The inverse of each true original second representative has its exact zero-based Hecke index. -/
lemma lpsHeckeConjugateRepresentative_index (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (lpsHeckeConjugateRepresentative N p hNp i:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem
        (lpsHeckeConjugateRepresentative N p hNp i).property)
        (some ⟨0,(Fact.out:p.Prime).pos⟩)=i := by
  rw [←lpsHeckeConjugateCosetEquiv_mk]
  unfold lpsHeckeConjugateRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeConjugateCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeConjugateCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeConjugateCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)


/-- The projected second representatives satisfy the actual effective section law. -/
lemma lpsHeckeConjugateEffectiveRepresentative_mk (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    (QuotientGroup.mk (lpsHeckeConjugateEffectiveRepresentative N p hNp i) :
      lpsEffectiveGamma0 N ⧸ (lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N)) =
        (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm i := by
  apply (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).injective
  rw [Equiv.apply_symm_apply]
  unfold lpsHeckeConjugateEffectiveRepresentative
  rw [lpsEffectiveHeckeConjugateCosetEquiv_mk]
  unfold lpsHeckeConjugateRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeConjugateCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeConjugateCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeConjugateCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)


/-- The actual second inverse-section cover is an effective relative-intersection domain. -/
lemma lpsHeckeConjugateCover_fundamental (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain ((lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N))
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume :=
  lpsIndexedRelativeDomain_fundamental _ s hs
    (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm _
    (lpsHeckeConjugateEffectiveRepresentative_mk N p hNp)

/-- The first genuine cover is a domain for the original effective Gamma0(Np). -/
lemma lpsHeckeIntersectionCover_originalEffective (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveGamma0 (N*p))
      (⋃i,(lpsHeckeIntersectionEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by
  have hle : lpsEffectiveGamma0 (N*p) ≤ lpsEffectiveGamma0 N :=
    Subgroup.map_mono (lpsGamma0_product_le N p)
  exact lpsRelativeFundamental_subgroupOf _ _ hle (lpsHeckeIntersectionCover_fundamental N p hNp hs)

/-- The second genuine cover is a domain for the actual effective upper-right intersection. -/
lemma lpsHeckeConjugateCover_originalEffective (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) {s : Set ℍ}
    (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    IsFundamentalDomain (lpsEffectiveHeckeConjugateIntersection N p)
      (⋃i,(lpsHeckeConjugateEffectiveRepresentative N p hNp i)⁻¹ • s) volume := by
  have hle : lpsEffectiveHeckeConjugateIntersection N p ≤ lpsEffectiveGamma0 N :=
    Subgroup.map_mono (show lpsHeckeConjugateIntersection N p ≤ CongruenceSubgroup.Gamma0 N from inf_le_left)
  exact lpsRelativeFundamental_subgroupOf _ _ hle (lpsHeckeConjugateCover_fundamental N p hNp hs)

end
end QEC.Coding.TannerLiftedProduct
